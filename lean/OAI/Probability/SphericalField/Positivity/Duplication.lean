import Mathlib
import OAI.Probability.SphericalField.Positivity.Nonnegative
import OAI.Probability.SphericalField.Positivity.Arrays

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
def duplicateEvent (r : ℕ) (s : Set (OverlapBlock (r + 1))) (t : ℝ) (j : ℕ) :
    Set OverlapArray :=
  copyEvent r s r ∩ copyEvent r s j ∩ {Q | Q r j < t}

lemma duplicateEvent_measurable (r : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ) (j : ℕ) : MeasurableSet (duplicateEvent r s t j) :=
  ((copyEvent_measurable r hs r).inter (copyEvent_measurable r hs j)).inter
    (measurableSet_lt ((measurable_pi_apply j).comp (measurable_pi_apply r)) measurable_const)

lemma duplicateEvent_relabel (r j : ℕ) (π : Equiv.Perm ℕ)
    (hπ : ∀ a < r, π a = a) (hr : π r = r)
    (s : Set (OverlapBlock (r + 1))) (t : ℝ) :
    relabelArray π ⁻¹' duplicateEvent r s t j = duplicateEvent r s t (π j) := by
  ext Q
  simp only [duplicateEvent, copyEvent, mem_preimage, mem_inter_iff, mem_ofPred_eq,
    copyBlock_relabel r r π hπ, copyBlock_relabel r j π hπ, hr, relabelArray]

lemma duplicateEvent_null_future (μ : Measure OverlapArray)
    (hEx : OverlapSwapInvariant μ) (r : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ)
    (hzero : μ (duplicateEvent r s t (r + 1)) = 0) {j : ℕ} (hj : r + 1 ≤ j) :
    μ (duplicateEvent r s t j) = 0 := by
  let π : Equiv.Perm ℕ := Equiv.swap (r + 1) j
  have hfix : ∀ a ≤ r, π a = a := by
    intro a ha
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  calc
    μ (duplicateEvent r s t j) = μ (relabelArray π ⁻¹' duplicateEvent r s t (r + 1)) := by
      rw [duplicateEvent_relabel r (r + 1) π (fun a ha => hfix a ha.le) (hfix r le_rfl)]
      simp only [π, Equiv.swap_apply_left]
    _ = μ (duplicateEvent r s t (r + 1)) :=
      (hEx _ _).measure_preimage (duplicateEvent_measurable r hs t (r + 1)).nullMeasurableSet
    _ = 0 := hzero

lemma star_unique_bound_of_no_duplication (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (r : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ)
    (hzero : μ (duplicateEvent r s t (r + 1)) = 0) (k : ℕ) :
    (k + 1 : ℝ) * μ.real (starEvent r s t k) ≤ 1 := by
  have hnul (j : Fin (k + 1)) : ∀ᵐ Q ∂μ, j ≠ 0 → Q ∉ duplicateEvent r s t (r + j) := by
    by_cases hj : j = 0
    · exact Filter.Eventually.of_forall fun _ h => (h hj).elim
    · have hz : μ (duplicateEvent r s t (r + j)) = 0 :=
        duplicateEvent_null_future μ hEx r hs t hzero (by
          have : j.val ≠ 0 := fun h => hj (Fin.ext h)
          omega)
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with Q hQ
      exact fun _ => hQ
  have hae : starEvent r s t k ≤ᵐ[μ]
      uniqueEvent (fun j : Fin (k + 1) => copyEvent r s (r + j)) 0 := by
    filter_upwards [ae_all_iff.mpr hnul] with Q hQ
    intro hstar
    refine ⟨hstar.1, ?_⟩
    intro j hj hmem
    apply hQ j hj
    refine ⟨⟨hstar.1, hmem⟩, ?_⟩
    exact hstar.2 (r + j) (by have := j.isLt; omega) (by
      have : j.val ≠ 0 := fun h => hj (Fin.ext h)
      omega)
  have hle : μ.real (starEvent r s t k) ≤ μ.real
      (uniqueEvent (fun j : Fin (k + 1) => copyEvent r s (r + j)) 0) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hae)
  exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans
    (uniqueCopy_probability_bound μ hEx r k hs)

lemma edge_probability_swap (μ : Measure OverlapArray) (hEx : OverlapSwapInvariant μ)
    (a b i j : ℕ) (t : ℝ) :
    μ.real {Q | Q (Equiv.swap a b i) (Equiv.swap a b j) < t} =
      μ.real {Q | Q i j < t} := by
  exact (hEx a b).measureReal_preimage
    (measurableSet_lt ((measurable_pi_apply j).comp (measurable_pi_apply i))
      measurable_const).nullMeasurableSet

theorem gg_duplicate_last (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    {r : ℕ} (hr : 1 ≤ r) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ)
    (hA : 0 < μ.real (copyEvent r s r))
    (hrow : ∀ Q ∈ copyEvent r s r, ∀ j < r, Q r j < t) :
    0 < μ.real (duplicateEvent r s t (r + 1)) := by
  by_contra hbad
  have hz : μ (duplicateEvent r s t (r + 1)) = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top _ _)).mp (le_antisymm (not_lt.mp hbad) (measureReal_nonneg))
  have heq : μ.real {Q | Q r 0 < t} = μ.real {Q | Q 0 1 < t} := by
    have h₁ := edge_probability_swap μ hEx 1 r 1 0 t
    have h₂ := edge_probability_swap μ hEx 0 1 0 1 t
    have hr0 : (0 : ℕ) ≠ r := by omega
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne (by decide : (0 : ℕ) ≠ 1) hr0] at h₁ h₂
    exact h₁.trans h₂
  have hζ : 0 < μ.real {Q | Q 0 1 < t} := by
    rw [← heq]
    refine hA.trans_le (measureReal_mono ?_)
    exact fun Q hQ => hrow Q hQ 0 (by omega)
  apply gg_star_growth_impossible (a := fun k => μ.real (starEvent r s t k))
    (N := (r + 1 : ℕ)) (ζ := μ.real {Q | Q 0 1 < t})
    (by exact_mod_cast (by omega : 2 ≤ r + 1)) hζ (fun _ => measureReal_nonneg)
  · rwa [starEvent_zero r s t hrow]
  · intro k
    simpa only [Nat.cast_add] using gg_star_recurrence μ hGG hr hs t k
  · exact star_unique_bound_of_no_duplication μ hEx r hs t hz

def relabelBlock {n : ℕ} (e : Equiv.Perm (Fin n)) (B : OverlapBlock n) : OverlapBlock n :=
  fun i j => B (e i) (e j)

def replaceIndex {n : ℕ} (p : Fin n) (j : ℕ) (a : Fin n) : ℕ :=
  if a = p then j else a.val

def replaceBlock {n : ℕ} (p : Fin n) (j : ℕ) (Q : OverlapArray) : OverlapBlock n :=
  fun a b => Q (replaceIndex p j a) (replaceIndex p j b)

def replaceEvent {n : ℕ} (p : Fin n) (s : Set (OverlapBlock n)) (j : ℕ) : Set OverlapArray :=
  replaceBlock p j ⁻¹' s

lemma relabelBlock_measurable {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Measurable (relabelBlock e) :=
  Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

lemma replaceBlock_measurable {n : ℕ} (p : Fin n) (j : ℕ) :
    Measurable (replaceBlock p j) :=
  Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

lemma fin_swap_val {n : ℕ} (p q a : Fin n) :
    (Equiv.swap p q a).val = Equiv.swap p.val q.val a.val :=
  Fin.val_injective.map_swap p q a

lemma relabelBlock_swap {n : ℕ} (p q : Fin n) (Q : OverlapArray) :
    relabelBlock (Equiv.swap p q) (overlapBlock id n Q) =
      overlapBlock id n (relabelArray (Equiv.swap p.val q.val) Q) := by
  ext a b
  simp only [relabelBlock, overlapBlock, id_eq, relabelArray, fin_swap_val]

lemma relabelArray_swap_swap (p q : ℕ) (Q : OverlapArray) :
    relabelArray (Equiv.swap p q) (relabelArray (Equiv.swap p q) Q) = Q := by
  ext a b
  simp [relabelArray]

lemma relabelBlock_swap_swap {n : ℕ} (p q : Fin n) (B : OverlapBlock n) :
    relabelBlock (Equiv.swap p q) (relabelBlock (Equiv.swap p q) B) = B := by
  ext a b
  simp [relabelBlock]

lemma replaceBlock_last (r j : ℕ) (Q : OverlapArray) :
    replaceBlock (Fin.last r) j Q = copyBlock r j Q := by
  have h (a : Fin (r + 1)) : replaceIndex (Fin.last r) j a = copyIndex r j a := by
    simp [replaceIndex, copyIndex, Fin.ext_iff]
  ext a b
  simp only [replaceBlock, copyBlock, h]

lemma replaceBlock_swap {n : ℕ} (p q : Fin n) {j : ℕ} (hj : n ≤ j) (Q : OverlapArray) :
    relabelBlock (Equiv.swap p q)
      (replaceBlock q j (relabelArray (Equiv.swap p.val q.val) Q)) =
        replaceBlock p j Q := by
  have h (a : Fin n) : Equiv.swap p.val q.val (replaceIndex q j (Equiv.swap p q a)) =
      replaceIndex p j a := by
    by_cases ha : a = p
    · subst a
      simp only [Equiv.swap_apply_left, replaceIndex, ↓reduceIte]
      exact Equiv.swap_apply_of_ne_of_ne (by have := p.isLt; omega) (by have := q.isLt; omega)
    · have he : Equiv.swap p q a ≠ q := by
        intro h
        apply ha
        have := congrArg (Equiv.swap p q) h
        simpa using this
      simp only [replaceIndex, ite_eq_right he, ite_eq_right ha, fin_swap_val, Equiv.swap_apply_self]
  ext a b
  exact congrArg₂ Q (h a) (h b)

lemma block_event_swap (μ : Measure OverlapArray) (hEx : OverlapSwapInvariant μ)
    {n : ℕ} (p q : Fin n) {s : Set (OverlapBlock n)} (hs : MeasurableSet s) :
    μ.real (overlapBlock id n ⁻¹' (relabelBlock (Equiv.swap p q) ⁻¹' s)) =
      μ.real (overlapBlock id n ⁻¹' s) := by
  have heq : overlapBlock id n ⁻¹' (relabelBlock (Equiv.swap p q) ⁻¹' s) =
      relabelArray (Equiv.swap p.val q.val) ⁻¹' (overlapBlock id n ⁻¹' s) := by
    ext Q
    change relabelBlock (Equiv.swap p q) (overlapBlock id n Q) ∈ s ↔ _
    rw [relabelBlock_swap]
    rfl
  rw [heq]
  exact (hEx _ _).measureReal_preimage
    (hs.preimage (Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
      (measurable_pi_apply _).comp (measurable_pi_apply _))).nullMeasurableSet

theorem gg_duplicate_index (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    {r : ℕ} (hr : 1 ≤ r) (p : Fin (r + 1)) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ)
    (hA : 0 < μ.real (overlapBlock id (r + 1) ⁻¹' s))
    (hrow : ∀ Q ∈ overlapBlock id (r + 1) ⁻¹' s,
      ∀ j : Fin (r + 1), j ≠ p → Q p j < t) :
    0 < μ.real ((overlapBlock id (r + 1) ⁻¹' s) ∩ replaceEvent p s (r + 1) ∩
      {Q | Q p (r + 1) < t}) := by
  let q : Fin (r + 1) := Fin.last r
  let e := Equiv.swap p q
  let π := Equiv.swap p.val q.val
  let s' := relabelBlock e ⁻¹' s
  have hs' : MeasurableSet s' := hs.preimage (relabelBlock_measurable e)
  have hbase : copyEvent r s' r = overlapBlock id (r + 1) ⁻¹' s' := by
    ext Q
    change copyBlock r r Q ∈ s' ↔ overlapBlock id (r + 1) Q ∈ s'
    have hb : copyBlock r r Q = overlapBlock id (r + 1) Q := by
      ext a b
      simp [copyBlock, overlapBlock]
    rw [hb]
  have hA' : 0 < μ.real (copyEvent r s' r) := by
    rw [hbase]
    exact (block_event_swap μ hEx p q hs).symm ▸ hA
  have hrow' : ∀ Q ∈ copyEvent r s' r, ∀ j < r, Q r j < t := by
    intro Q hQ j hj
    have hmem : relabelArray π Q ∈ overlapBlock id (r + 1) ⁻¹' s := by
      rw [hbase] at hQ
      change relabelBlock e (overlapBlock id (r + 1) Q) ∈ s at hQ
      rwa [relabelBlock_swap] at hQ
    let a : Fin (r + 1) := ⟨j, by omega⟩
    have hne : e a ≠ p := by
      intro h
      have h' := congrArg e h
      have haq : a = q := by simpa [e] using h'
      have := congrArg Fin.val haq
      dsimp [a, q] at this
      omega
    have h := hrow (relabelArray π Q) hmem (e a) hne
    have hp : π p.val = r := by simp [π, q]
    have ha : π (e a).val = j := by simp [π, e, fin_swap_val, a]
    simpa only [relabelArray, hp, ha] using h
  have hD := gg_duplicate_last μ hEx hGG hr hs' t hA' hrow'
  have hset : relabelArray π ⁻¹' duplicateEvent r s' t (r + 1) =
      (overlapBlock id (r + 1) ⁻¹' s) ∩ replaceEvent p s (r + 1) ∩
        {Q | Q p (r + 1) < t} := by
    ext Q
    have hfirst : copyBlock r r (relabelArray π Q) ∈ s' ↔
        overlapBlock id (r + 1) Q ∈ s := by
      change relabelBlock e (copyBlock r r (relabelArray π Q)) ∈ s ↔ _
      have hb : copyBlock r r (relabelArray π Q) =
          overlapBlock id (r + 1) (relabelArray π Q) := by
        ext a b
        simp [copyBlock, overlapBlock]
      rw [hb, relabelBlock_swap, relabelArray_swap_swap]
    have hsecond : copyBlock r (r + 1) (relabelArray π Q) ∈ s' ↔
        replaceBlock p (r + 1) Q ∈ s := by
      change relabelBlock e (copyBlock r (r + 1) (relabelArray π Q)) ∈ s ↔ _
      rw [← replaceBlock_last]
      change relabelBlock (Equiv.swap p q)
        (replaceBlock q (r + 1) (relabelArray (Equiv.swap p.val q.val) Q)) ∈ s ↔ _
      rw [replaceBlock_swap p q (le_refl _)]
    have hp : π r = p.val := by exact Equiv.swap_apply_right _ _
    have hnew : π (r + 1) = r + 1 :=
      Equiv.swap_apply_of_ne_of_ne (by have := p.isLt; omega) (by dsimp [q]; omega)
    change ((copyBlock r r (relabelArray π Q) ∈ s' ∧
      copyBlock r (r + 1) (relabelArray π Q) ∈ s') ∧
      Q (π r) (π (r + 1)) < t) ↔ ((overlapBlock id (r + 1) Q ∈ s ∧
        replaceBlock p (r + 1) Q ∈ s) ∧ Q p (r + 1) < t)
    rw [hfirst, hsecond, hp, hnew]
  rw [← hset]
  rwa [(hEx _ _).measureReal_preimage
    (duplicateEvent_measurable r hs' t (r + 1)).nullMeasurableSet]

end SphericalPerceptron
end
end

end OAI
