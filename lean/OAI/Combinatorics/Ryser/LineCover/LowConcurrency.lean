import OAI.Combinatorics.Ryser.LineCover.SurvivorSampling
import OAI.Combinatorics.Ryser.LineCover.LowDegeneracy
import OAI.Combinatorics.Ryser.LineCover.LowOccupancy
import OAI.Combinatorics.Ryser.LineCover.TupleGeometry

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F]

def lowFailureBound (X : Finset (Point F)) (L : Finset (AffineLine F))
    (shapes : Finset (Finset (Point F))) (D R h t : ℕ) (δ : ℝ) : ℝ :=
  2 * (orderedPairMass Incidence X L : ℝ) /
      (δ * (L.card.descFactorial 2 : ℝ)) +
    ((2 * t).descFactorial 2 : ℝ) * R / ((L.card - 1 : ℕ) : ℝ) +
    ((2 * t).descFactorial 3 : ℝ) * R / ((L.card - 2 : ℕ) : ℝ) +
    (shapes.card : ℝ) * (t : ℝ) ^ (2 * h) * ((L.card * D * R : ℕ) : ℝ) ^ h /
      (L.card.descFactorial (2 * h) : ℝ)

def LowBad (X : Finset (Point F)) (L : Finset (AffineLine F))
    (shapes : Finset (Finset (Point F))) (D h t : ℕ) (δ : ℝ)
    (u : CoverSample L t) : Prop :=
  δ * (t : ℝ) ^ 2 / 2 ≤ ((X ∩ crossPoints (liftSample L u)).card : ℝ) ∨
    LowDegeneracy.AnyParallel u ∨ LowDegeneracy.AnyConcurrent u ∨
    ∃ S ∈ shapes, S ∉ tupleShapes (liftSample L u) ∧
      2 * D * h < (S ∩ crossPoints (liftSample L u)).card

theorem direction_card_le_of_coverPencil
    (L : Finset (AffineLine F)) {R : ℕ}
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R)
    (d : Direction F) : (L.filter fun l => l.1 = d).card ≤ R := let _ := instFintypeF; by
  simpa only [coverPencil, ProjectiveIncidence, eq_comm] using hR (Sum.inr d)

private theorem prob_four_union_le {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (P Q R S : Ω → Prop) :
    μ.prob (fun u => P u ∨ Q u ∨ R u ∨ S u) ≤
      μ.prob P + μ.prob Q + μ.prob R + μ.prob S := by
  calc
    _ ≤ μ.prob P + μ.prob (fun u => Q u ∨ R u ∨ S u) :=
      μ.prob_union_le _ _
    _ ≤ μ.prob P + (μ.prob Q + μ.prob (fun u => R u ∨ S u)) :=
      add_le_add (le_refl (μ.prob P)) (μ.prob_union_le Q (fun u => R u ∨ S u))
    _ ≤ μ.prob P + (μ.prob Q + (μ.prob R + μ.prob S)) :=
      add_le_add (le_refl (μ.prob P))
        (add_le_add (le_refl (μ.prob Q)) (μ.prob_union_le R S))
    _ = _ := by simp only [add_assoc]

private theorem prob_uniform_parallel_le (L : Finset (AffineLine F)) (t R : ℕ)
    [Nonempty (CoverSample L t)] (hsize : 2 * t ≤ L.card) (hL : 3 ≤ L.card)
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R) :
    (FiniteLaw.uniform (CoverSample L t)).prob LowDegeneracy.AnyParallel ≤
      ((2 * t).descFactorial 2 : ℝ) * R / ((L.card - 1 : ℕ) : ℝ) := by
  have hbound := LowDegeneracy.prob_tuple_parallel_le L t R hsize
    ((by decide : 2 ≤ 3).trans hL) (direction_card_le_of_coverPencil L hR)
  rw [InjectionSampling.law_eq_uniform] at hbound
  exact hbound

private theorem prob_uniform_concurrent_le (L : Finset (AffineLine F)) (t R : ℕ)
    [Nonempty (CoverSample L t)] (hsize : 2 * t ≤ L.card) (hL : 3 ≤ L.card)
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R) :
    (FiniteLaw.uniform (CoverSample L t)).prob LowDegeneracy.AnyConcurrent ≤
      ((2 * t).descFactorial 3 : ℝ) * R / ((L.card - 2 : ℕ) : ℝ) := let _ := instFintypeF; by
  have hbound := LowDegeneracy.prob_tuple_concurrent_le L t R hsize hL hR
  rw [InjectionSampling.law_eq_uniform] at hbound
  exact hbound

theorem prob_lowBad_le
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    (shapes : Finset (Finset (Point F))) (D R h t : ℕ) (δ : ℝ)
    [Nonempty (CoverSample L t)]
    (hδ : 0 < δ) (ht : 0 < t) (hsize : 2 * t ≤ L.card) (hL : 3 ≤ L.card)
    (hSparse : SparseShapes shapes D)
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R) :
    (FiniteLaw.uniform (CoverSample L t)).prob (LowBad X L shapes D h t δ) ≤
      lowFailureBound X L shapes D R h t δ := by
  unfold LowBad lowFailureBound
  apply (prob_four_union_le (FiniteLaw.uniform (CoverSample L t)) _ _ _ _).trans
  exact add_le_add
    (add_le_add
      (add_le_add (prob_many_cross_survivors_le X L hδ ht)
        (prob_uniform_parallel_le L t R hsize hL hR))
      (prob_uniform_concurrent_le L t R hsize hL hR))
    (prob_bad_occupancy_le (h := h) (t := t) shapes L hSparse hR)

theorem admissible_of_not_lowBad
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    (shapes : Finset (Finset (Point F))) (D h t : ℕ) (δ : ℝ)
    (u : CoverSample L t) (hu : ¬ LowBad X L shapes D h t δ u) :
    AdmissibleTuple shapes D h (liftSample L u) ∧
      ((X ∩ crossPoints (liftSample L u)).card : ℝ) < δ * (t : ℝ) ^ 2 / 2 := by
  have hmany : ¬ δ * (t : ℝ) ^ 2 / 2 ≤
      ((X ∩ crossPoints (liftSample L u)).card : ℝ) :=
    fun he => hu (Or.inl he)
  have hparallel : ¬ LowDegeneracy.AnyParallel u :=
    fun he => hu (Or.inr (Or.inl he))
  have hconcurrent : ¬ LowDegeneracy.AnyConcurrent u :=
    fun he => hu (Or.inr (Or.inr (Or.inl he)))
  have hoccupied : ¬ ∃ S ∈ shapes, S ∉ tupleShapes (liftSample L u) ∧
      2 * D * h < (S ∩ crossPoints (liftSample L u)).card :=
    fun he => hu (Or.inr (Or.inr (Or.inr he)))
  have hp : NoParallel (liftSample L u) := by
    intro i j hij hdir
    exact hparallel ((LowDegeneracy.anyParallel_iff u).mpr ⟨i, j, hij, hdir⟩)
  have hc : NoConcurrentTriple (liftSample L u) := by
    intro p i j k hij hik hjk hi hj hk
    exact hconcurrent ((LowDegeneracy.anyConcurrent_iff u).mpr
      ⟨i, j, k, hij, hik, hjk, p, hi, hj, hk⟩)
  obtain ⟨hfinite, hcard⟩ :=
    finiteCrossings_card_of_no_parallel_no_concurrentTriple (liftSample L u) hp hc
  refine ⟨⟨hfinite, hcard, ?_⟩, lt_of_not_ge hmany⟩
  intro S hS hnot
  exact Nat.le_of_not_gt (fun hlarge => hoccupied ⟨S, hS, hnot, hlarge⟩)

theorem exists_low_sample_of_failureBound_lt_one
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    (shapes : Finset (Finset (Point F))) (D R h t : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (ht : 0 < t) (hsize : 2 * t ≤ L.card) (hL : 3 ≤ L.card)
    (hSparse : SparseShapes shapes D)
    (hR : ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R)
    (hbudget : lowFailureBound X L shapes D R h t δ < 1) :
    ∃ a : LineTuple F t, (∀ i, a i ∈ L) ∧ AdmissibleTuple shapes D h a ∧
      ((X ∩ crossPoints a).card : ℝ) < δ * (t : ℝ) ^ 2 / 2 := by
  classical
  let : Nonempty (CoverSample L t) := InjectionSampling.sample_nonempty
    (Fin t ⊕ Fin t) ↥L (by simpa [Nat.card_sum, two_mul] using hsize)
  let μ := FiniteLaw.uniform (CoverSample L t)
  have hprob := prob_lowBad_le X L shapes D R h t δ hδ ht hsize hL hSparse hR
  have hex : ∃ u : CoverSample L t, ¬ LowBad X L shapes D h t δ u := by
    by_contra hnone
    have hall (u : CoverSample L t) : LowBad X L shapes D h t δ u := by
      by_contra hu
      exact hnone ⟨u, hu⟩
    have hone : 1 ≤ μ.prob (LowBad X L shapes D h t δ) := by
      simpa only [FiniteLaw.prob_true] using
        (μ.prob_mono (P := fun _ => True) (Q := LowBad X L shapes D h t δ)
          (fun u _ => hall u))
    exact (not_le_of_gt (hprob.trans_lt hbudget)) hone
  obtain ⟨u, hu⟩ := hex
  exact ⟨liftSample L u, liftSample_mem L u,
    admissible_of_not_lowBad X L shapes D h t δ u hu⟩

end RyserCoveringCounterexample.LineCover

end

end OAI
