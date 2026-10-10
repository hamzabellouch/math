import Mathlib
import OAI.Probability.SphericalField.Positivity.Cliques

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
abbrev OverlapArray := ℕ → ℕ → ℝ
def relabelArray (π : Equiv.Perm ℕ) (Q : OverlapArray) : OverlapArray :=
  fun i j => Q (π i) (π j)

def OverlapSwapInvariant (μ : Measure OverlapArray) : Prop :=
  ∀ i j : ℕ, MeasurePreserving (relabelArray (Equiv.swap i j)) μ μ

def copyIndex (r j : ℕ) (i : Fin (r + 1)) : ℕ := if i.val = r then j else i.val

def copyBlock (r j : ℕ) (Q : OverlapArray) : OverlapBlock (r + 1) :=
  fun a b => Q (copyIndex r j a) (copyIndex r j b)

def copyEvent (r : ℕ) (s : Set (OverlapBlock (r + 1))) (j : ℕ) : Set OverlapArray :=
  copyBlock r j ⁻¹' s

@[simp] lemma copyIndex_self (r : ℕ) (i : Fin (r + 1)) : copyIndex r r i = i := by
  unfold copyIndex
  split_ifs with h
  · exact h.symm
  · rfl

lemma copyBlock_measurable (r j : ℕ) : Measurable (copyBlock r j) := by
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

lemma copyEvent_measurable (r : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (j : ℕ) : MeasurableSet (copyEvent r s j) :=
  hs.preimage (copyBlock_measurable r j)

lemma copyBlock_self (r : ℕ) (Q : OverlapArray) :
    copyBlock r r Q = overlapBlock id (r + 1) Q := by
  ext i j
  simp [copyBlock, overlapBlock]

lemma copyIndex_relabel (r j : ℕ) (π : Equiv.Perm ℕ)
    (hπ : ∀ a < r, π a = a) (i : Fin (r + 1)) :
    π (copyIndex r j i) = copyIndex r (π j) i := by
  by_cases hi : i.val = r
  · simp [copyIndex, hi]
  · simp only [copyIndex, ite_eq_right hi]
    exact hπ i (by omega)

lemma copyBlock_relabel (r j : ℕ) (π : Equiv.Perm ℕ)
    (hπ : ∀ a < r, π a = a) (Q : OverlapArray) :
    copyBlock r j (relabelArray π Q) = copyBlock r (π j) Q := by
  ext a b
  simp only [copyBlock, relabelArray, copyIndex_relabel r j π hπ]

lemma copyEvent_relabel (r j : ℕ) (π : Equiv.Perm ℕ)
    (hπ : ∀ a < r, π a = a) (s : Set (OverlapBlock (r + 1))) :
    relabelArray π ⁻¹' copyEvent r s j = copyEvent r s (π j) := by
  ext Q
  simp only [copyEvent, mem_preimage, copyBlock_relabel r j π hπ]

def uniqueEvent {Ω ι : Type*} (A : ι → Set Ω) (i : ι) : Set Ω :=
  {ω | ω ∈ A i ∧ ∀ j, j ≠ i → ω ∉ A j}

lemma uniqueEvent_measurable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (i : ι) :
    MeasurableSet (uniqueEvent A i) := by
  simp only [uniqueEvent, ofPred_and, ofPred_forall]
  exact (hA i).inter (MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => (hA j).compl)

lemma uniqueEvent_disjoint {Ω ι : Type*} (A : ι → Set Ω) :
    Pairwise (fun i j => Disjoint (uniqueEvent A i) (uniqueEvent A j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro ω hi hj
  exact hi.2 j hij.symm hj.1

lemma uniqueEvent_probability_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (i₀ : ι)
    (hsame : ∀ i, μ.real (uniqueEvent A i) = μ.real (uniqueEvent A i₀)) :
    Fintype.card ι * μ.real (uniqueEvent A i₀) ≤ 1 := by
  have h := sum_measureReal_le_measureReal_univ (μ := μ) (s := Finset.univ)
    (t := uniqueEvent A) (fun i _ => uniqueEvent_measurable A hA i)
    (fun i _ j _ hij => uniqueEvent_disjoint A hij)
  simp only [hsame, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  simpa [Measure.real] using h

lemma uniqueEvent_preimage {Ω ι : Type*} {f : Ω → Ω} (A : ι → Set Ω)
    (e : Equiv.Perm ι) (h : ∀ j, f ⁻¹' A j = A (e j)) (i : ι) :
    f ⁻¹' uniqueEvent A i = uniqueEvent A (e i) := by
  ext ω
  have hm (j : ι) : f ω ∈ A j ↔ ω ∈ A (e j) := by
    change ω ∈ f ⁻¹' A j ↔ ω ∈ A (e j)
    rw [h]
  constructor
  · intro hw
    refine ⟨(hm i).mp hw.1, ?_⟩
    intro j hji hj
    apply hw.2 (e.symm j) (fun heq => hji (by rw [← e.apply_symm_apply j, heq]))
    exact (hm _).mpr (by simpa using hj)
  · intro hw
    refine ⟨(hm i).mpr hw.1, ?_⟩
    intro j hji hj
    exact hw.2 (e j) (fun h' => hji (e.injective h')) ((hm j).mp hj)

lemma uniqueCopy_probability_bound (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (r k : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) :
    (k + 1 : ℝ) * μ.real (uniqueEvent
      (fun j : Fin (k + 1) => copyEvent r s (r + j)) 0) ≤ 1 := by
  let A : Fin (k + 1) → Set OverlapArray := fun j => copyEvent r s (r + j)
  have hA (j) : MeasurableSet (A j) := copyEvent_measurable r hs _
  have hsame (i : Fin (k + 1)) : μ.real (uniqueEvent A i) = μ.real (uniqueEvent A 0) := by
    let e : Equiv.Perm (Fin (k + 1)) := Equiv.swap i 0
    let π : Equiv.Perm ℕ := Equiv.swap (r + i) (r + (0 : Fin (k + 1)))
    have hfix : ∀ a < r, π a = a := by
      intro a ha
      exact Equiv.swap_apply_of_ne_of_ne (by omega) (by simp; omega)
    have hinj : Function.Injective (fun j : Fin (k + 1) => r + j.val) := by
      intro a b hab
      apply Fin.ext
      exact Nat.add_left_cancel hab
    have hmap (j : Fin (k + 1)) : relabelArray π ⁻¹' A j = A (e j) := by
      dsimp [A]
      rw [copyEvent_relabel r _ π hfix]
      congr 1
      exact (hinj.map_swap i 0 j).symm
    have he : e 0 = i := Equiv.swap_apply_right _ _
    rw [← he, ← uniqueEvent_preimage A e hmap]
    exact (hEx _ _).measureReal_preimage (uniqueEvent_measurable A hA 0).nullMeasurableSet
  have h := uniqueEvent_probability_bound μ A hA 0 hsame
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using h

def prefixBlock {n m : ℕ} (h : n ≤ m) (Q : OverlapBlock m) : OverlapBlock n :=
  fun a b => Q (Fin.castLE h a) (Fin.castLE h b)

lemma prefixBlock_measurable {n m : ℕ} (h : n ≤ m) : Measurable (prefixBlock h) := by
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

def starMatrices (r : ℕ) (s : Set (OverlapBlock (r + 1))) (t : ℝ) (k : ℕ) :
    Set (OverlapBlock (r + 1 + k)) :=
  {Q | prefixBlock (Nat.le_add_right (r + 1) k) Q ∈ s ∧
    ∀ j : Fin (r + 1 + k), j.val ≠ r → Q ⟨r, by omega⟩ j < t}

def starEvent (r : ℕ) (s : Set (OverlapBlock (r + 1))) (t : ℝ) (k : ℕ) :
    Set OverlapArray :=
  copyEvent r s r ∩ {Q | ∀ j < r + 1 + k, j ≠ r → Q r j < t}

lemma starMatrices_measurable (r : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ) (k : ℕ) : MeasurableSet (starMatrices r s t k) := by
  simp only [starMatrices, ofPred_and, ofPred_forall]
  apply MeasurableSet.inter (hs.preimage (prefixBlock_measurable _))
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_lt ((measurable_pi_apply j).comp (measurable_pi_apply _)) measurable_const

lemma starEvent_measurable (r : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ) (k : ℕ) : MeasurableSet (starEvent r s t k) := by
  apply (copyEvent_measurable r hs r).inter
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_lt ((measurable_pi_apply j).comp (measurable_pi_apply r)) measurable_const

lemma starEvent_preimage (r : ℕ) (s : Set (OverlapBlock (r + 1))) (t : ℝ) (k : ℕ) :
    overlapBlock id (r + 1 + k) ⁻¹' starMatrices r s t k = starEvent r s t k := by
  ext Q
  have hprefix : prefixBlock (Nat.le_add_right (r + 1) k)
      (overlapBlock id (r + 1 + k) Q) = copyBlock r r Q := by
    ext a b
    simp [prefixBlock, overlapBlock, copyBlock]
  simp only [mem_preimage, starMatrices, mem_ofPred_eq, hprefix, starEvent,
    copyEvent, mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, fun j hj hne => h' ⟨j, hj⟩ hne⟩
  · rintro ⟨h, h'⟩
    exact ⟨h, fun j hne => h' j j.isLt hne⟩

lemma starEvent_succ (r : ℕ) (s : Set (OverlapBlock (r + 1))) (t : ℝ) (k : ℕ) :
    starEvent r s t (k + 1) =
      starEvent r s t k ∩ {Q | Q r (r + 1 + k) < t} := by
  ext Q
  constructor
  · rintro ⟨hA, hQ⟩
    exact ⟨⟨hA, fun j hj hne => hQ j (by omega) hne⟩,
      hQ (r + 1 + k) (by omega) (by omega)⟩
  · rintro ⟨⟨hA, hQ⟩, hn⟩
    refine ⟨hA, ?_⟩
    intro j hj hne
    by_cases hlt : j < r + 1 + k
    · exact hQ j hlt hne
    · have heq : j = r + 1 + k := by omega
      simpa only [mem_ofPred_eq, heq] using hn

lemma starEvent_zero (r : ℕ) (s : Set (OverlapBlock (r + 1))) (t : ℝ)
    (hrow : ∀ Q ∈ copyEvent r s r, ∀ j < r, Q r j < t) :
    starEvent r s t 0 = copyEvent r s r := by
  ext Q
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, fun j hj hne => hrow Q h j (by omega)⟩

lemma gg_star_recurrence (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hGG : GhirlandaGuerra μ id) {r : ℕ} (hr : 1 ≤ r)
    {s : Set (OverlapBlock (r + 1))} (hs : MeasurableSet s) (t : ℝ) (k : ℕ) :
    ((r + 1 + k : ℕ) : ℝ) * μ.real (starEvent r s t (k + 1)) =
      (((r + 1 + k : ℕ) : ℝ) - 1 + μ.real {Q | Q 0 1 < t}) *
        μ.real (starEvent r s t k) := by
  classical
  let m := r + 1 + k
  let i : Fin m := ⟨r, by dsimp [m]; omega⟩
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h := hGG m hm i (starMatrices r s t k) (starMatrices_measurable r hs t k)
    (Iio t) measurableSet_Iio
  rw [starEvent_preimage] at h
  change μ.real (starEvent r s t k ∩ {Q | Q r m < t}) =
    μ.real (starEvent r s t k) * μ.real {Q | Q 0 1 < t} / m +
    (∑ j ∈ Finset.univ.erase i,
      μ.real (starEvent r s t k ∩ {Q | Q r j < t})) / m at h
  have hpair (j : Fin m) (hne : j ≠ i) :
      starEvent r s t k ∩ {Q | Q r j < t} = starEvent r s t k := by
    apply inter_eq_left.mpr
    intro Q hQ
    exact hQ.2 j j.isLt (fun heq => hne (Fin.ext heq))
  rw [Finset.sum_congr rfl (fun j hj => congrArg μ.real
    (hpair j (Finset.ne_of_mem_erase hj)))] at h
  have hcard : ((Finset.univ.erase i).card : ℝ) = (m : ℝ) - 1 := by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_sub (by omega)]
    norm_num
  simp only [Finset.sum_const, nsmul_eq_mul, hcard] at h
  rw [← starEvent_succ] at h
  have hmul := congrArg (fun x : ℝ => (m : ℝ) * x) h
  field_simp at hmul
  dsimp [m] at hmul
  nlinarith [hmul]

end SphericalPerceptron
end
end

end OAI
