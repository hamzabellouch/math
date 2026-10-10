import OAI.Analysis.BoundedHochschild.OrthogonalProjectionTails

namespace OAI

/-!
# Absolute continuity of finite projection comparison

The projection argument behind Ringrose, *Lectures on the trace in a finite
von Neumann algebra*, Lemma 5.2. Projections separately subequivalent to an
orthogonal sequence admit decreasing dominating projections with zero
weak-star limit. No tracial functional is used.
-/

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- In a finite algebra, projections dominated in comparison by an orthogonal
sequence have weak-star-null decreasing projection envelopes. -/
theorem finite_subequivalent_orthogonal_tails (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (p q : ℕ → M)
    (hp : ∀ n, IsStarProjection (p n)) (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0)
    (hembed : ∀ n, ∃ v : PartialIso M, v.initial = p n ∧ v.final ≤ q n) :
    ∃ R : ℕ → M, (∀ n, IsStarProjection (R n)) ∧ Antitone R ∧
      (∀ n, p n ≤ R n) ∧ PredualTendsto e R atTop 0 := by
  classical
  obtain ⟨T, hT, hTm, hTq, hTlim⟩ := exists_orthogonal_projection_tails e q hq horth
  have hjoins (n : ℕ) : ∃ v : PartialIso M, v.final ≤ T n ∧
      (∀ i, p (n + i) ≤ v.initial) ∧
      ∀ r : M, IsStarProjection r → (∀ i, p (n + i) ≤ r) → v.initial ≤ r := by
    apply countable_join_subequivalence e (hT n)
      (finiteCorner_of_finiteAlgebra hfinite _ (hT n))
      (fun i => p (n + i)) (fun i => q (n + i))
      (fun i => hp (n + i)) (fun i => hq (n + i))
    · intro i j hij
      exact horth _ _ (fun h => hij (Nat.add_left_cancel h))
    · intro i
      exact hTq n (n + i) (Nat.le_add_right n i)
    · intro i
      exact hembed (n + i)
  choose v hvf hvu hvl using hjoins
  let R (n : ℕ) : M := (v n).initial
  have hR (n : ℕ) : IsStarProjection (R n) := (v n).initial_proj
  have hRm : Antitone R := antitone_nat_of_succ_le fun n => by
    apply hvl (n + 1) (R n) (hR n)
    intro i
    simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hvu n (i + 1)
  obtain ⟨s, hs, hglb, hRlim⟩ := exists_decreasing_projection_limit e R hR hRm
  have hsR (n : ℕ) : s ≤ (v n).initial := hglb.1 ⟨n, rfl⟩
  have hembedS (n : ℕ) : ∃ w : PartialIso M, w.initial = s ∧ w.final ≤ T n := by
    let w := (v n).restrict hs (hsR n)
    exact ⟨w, PartialIso.restrict_initial _ _ _,
      (PartialIso.final_mono (PartialIso.restrict_le _ _ _)).trans (hvf n)⟩
  have hcomp (n : ℕ) : ∃ w : PartialIso M, w.initial = 1 - T n ∧ w.final ≤ 1 - s := by
    obtain ⟨w, hwi, hwf⟩ := hembedS n
    exact finite_complement_subequivalence e hfinite hs (hT n) w hwi hwf
  have hcomplim : PredualTendsto e (fun n => 1 - T n) atTop 1 := by
    simpa only [sub_zero] using predual_tendsto_sub e
      (predual_tendsto_const e 1 atTop) hTlim
  have hcomleast (r : M) (_hr : IsStarProjection r)
      (hb : ∀ n, 1 - T n ≤ r) : (1 : M) ≤ r := by
    apply HochschildSakai.le_of_bounded_predual_limit e 1 zero_le_one
      (Eventually.of_forall fun n => (hT n).one_sub.norm_le _) ?_ hcomplim
    exact Eventually.of_forall hb
  obtain ⟨w, hwi, hwf⟩ := finite_subequivalence_at_supremum e hs.one_sub
    (finiteCorner_of_finiteAlgebra hfinite _ hs.one_sub) (IsStarProjection.one M)
    (fun n => 1 - T n) (fun i j hij => sub_le_sub_left (hTm hij) 1) hcomp
    (fun n => (hT n).one_sub.le_one) hcomleast
  have hwfull : w.final = 1 := hfinite (w : M) hwi
  have hs0 : s = 0 := by
    rw [hwfull] at hwf
    exact sub_eq_self.mp (le_antisymm hs.one_sub.le_one hwf)
  refine ⟨R, hR, hRm, ?_, ?_⟩
  · intro n
    simpa only [Nat.add_zero] using hvu n 0
  · simpa only [hs0] using hRlim

end KadisonRingrose
end BoundedHochschild

end

end OAI
