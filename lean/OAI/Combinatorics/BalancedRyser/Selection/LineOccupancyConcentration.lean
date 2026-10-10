import OAI.Combinatorics.BalancedRyser.Probability.FiniteUniformConcentration
import OAI.Combinatorics.BalancedRyser.Probability.UniformRestriction
import OAI.Combinatorics.BalancedRyser.Selection.LineOccupancy
import OAI.Combinatorics.BalancedRyser.Selection.LineOccupancyAsymptotics

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Classical

namespace Balanced.LineOccupancy

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem offsetLaw_map_transverse (l : Line F) :
    (offsetLaw F).map (transverseOffsets l) =
      PMF.uniformOfFintype (TransverseDirections l → F) := by
  have ho : offsetLaw F = PMF.uniformOfFintype (MergedPairs F) := by
    unfold offsetLaw
    congr 1
    exact Subsingleton.elim _ _
  rw [ho]
  let e : TransverseDirections l ↪ Direction F × Bool :=
    ⟨fun d => (d.val, true), fun a b h => Subtype.ext (congrArg Prod.fst h)⟩
  let c : MergedPairs F ≃ (Direction F × Bool → F) := Equiv.curry _ _ _ |>.symm
  have hc := TupleAlignment.uniform_map_equiv c
  calc
    _ = ((PMF.uniformOfFintype (MergedPairs F)).map c).map
        (fun o i => o (e i)) := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by
      rw [hc]
      exact TupleAlignment.uniform_map_restrict e

theorem transverse_failure_le (l : Line F)
    (hgap : (Fintype.card F : ℝ) / 20 ≤
      (Fintype.card F : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) ^ Fintype.card F -
        (Fintype.card F : ℝ) / 5) :
    ((PMF.uniformOfFintype (TransverseDirections l → F)).toOuterMeasure
      {a | (unhitCount l a : ℝ) < (Fintype.card F : ℝ) / 5}).toReal ≤
      2 * Real.exp (-(Fintype.card F : ℝ) / 3200) := by
  let : MeasurableSpace F := ⊤
  let : MeasurableSingletonClass F := ⟨fun _ => trivial⟩
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hqR : (0 : ℝ) < Fintype.card F := Nat.cast_pos.mpr hq
  have ht := FiniteUniform.bounded_differences
    (fun a : TransverseDirections l → F => (unhitCount l a : ℝ)) (fun _ => 1)
    (fun _ => by norm_num)
    (fun i a b h => abs_unhitCount_sub_le_one l a b i h)
    (L := 1) (u := (Fintype.card F : ℝ) / 20)
    (by rw [card_transverseDirections]; exact Nat.succ_le_iff.mpr hq) (by norm_num) (fun _ => le_rfl) (by positivity)
  rw [integral_unhitCount (F := F) l, card_transverseDirections, occupancy_exponent _ hq] at ht
  have hsub : {a : TransverseDirections l → F |
        (unhitCount l a : ℝ) < (Fintype.card F : ℝ) / 5} ⊆
      {a | (Fintype.card F : ℝ) / 20 ≤
        |(unhitCount l a : ℝ) -
          (Fintype.card F : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) ^ Fintype.card F|} := by
    intro a ha
    change (unhitCount l a : ℝ) < (Fintype.card F : ℝ) / 5 at ha
    change (Fintype.card F : ℝ) / 20 ≤
      |(unhitCount l a : ℝ) -
        (Fintype.card F : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) ^ Fintype.card F|
    have habs := neg_le_abs ((unhitCount l a : ℝ) -
      (Fintype.card F : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) ^ Fintype.card F)
    linarith
  calc
    _ = (PMF.uniformOfFintype (TransverseDirections l → F)).toMeasure.real
        {a | (unhitCount l a : ℝ) < (Fintype.card F : ℝ) / 5} := by
      rw [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure_apply]
      exact (Set.toFinite _).measurableSet
    _ ≤ _ := measureReal_mono hsub
    _ ≤ _ := ht

theorem offset_failure_le (l : Line F)
    (hgap : (Fintype.card F : ℝ) / 20 ≤
      (Fintype.card F : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) ^ Fintype.card F -
        (Fintype.card F : ℝ) / 5) :
    offsetEventProbability (F := F)
      {M | (unhitCount l (transverseOffsets l M) : ℝ) < (Fintype.card F : ℝ) / 5} ≤
      2 * Real.exp (-(Fintype.card F : ℝ) / 3200) := by
  have h := transverse_failure_le l hgap
  rw [← offsetLaw_map_transverse l, PMF.toOuterMeasure_map_apply] at h
  exact h

omit [DecidableEq F] in

theorem offsetEventProbability_eq_real [MeasurableSpace (MergedPairs F)]
    [MeasurableSingletonClass (MergedPairs F)] (s : Set (MergedPairs F)) :
    offsetEventProbability s = (offsetLaw F).toMeasure.real s := by
  rw [offsetEventProbability, Measure.real,
    (offsetLaw F).toMeasure_apply_eq_toOuterMeasure_apply ((Set.toFinite s).measurableSet)]

theorem initial_failure_probability_le
    (hgap : (Fintype.card F : ℝ) / 20 ≤
      (Fintype.card F : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) ^ Fintype.card F -
        (Fintype.card F : ℝ) / 5) :
    offsetEventProbability (F := F)
      {M | ∃ l, l ∉ initialDeletedLines M ∧
        ((linePoints l ∩ initiallyRetained M).card : ℝ) < (Fintype.card F : ℝ) / 5} ≤
      (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1) *
        (2 * Real.exp (-(Fintype.card F : ℝ) / 3200)) := by
  let : MeasurableSpace (MergedPairs F) := ⊤
  let : MeasurableSingletonClass (MergedPairs F) := ⟨fun _ => trivial⟩
  let B (l : Line F) : Set (MergedPairs F) :=
    {M | (unhitCount l (transverseOffsets l M) : ℝ) < (Fintype.card F : ℝ) / 5}
  have hsub : {M : MergedPairs F | ∃ l, l ∉ initialDeletedLines M ∧
        ((linePoints l ∩ initiallyRetained M).card : ℝ) < (Fintype.card F : ℝ) / 5} ⊆
      ⋃ l, B l := by
    rintro M ⟨l, hl, hbad⟩
    apply Set.mem_iUnion.mpr
    refine ⟨l, ?_⟩
    change (unhitCount l (transverseOffsets l M) : ℝ) < _
    rw [unhitCount_eq_initiallyRetained l M hl]
    exact hbad
  rw [offsetEventProbability_eq_real]
  calc
    _ ≤ (offsetLaw F).toMeasure.real (⋃ l, B l) := measureReal_mono hsub
    _ ≤ ∑ l, (offsetLaw F).toMeasure.real (B l) := measureReal_iUnion_fintype_le B
    _ ≤ ∑ _l : Line F, (2 * Real.exp (-(Fintype.card F : ℝ) / 3200)) := by
      apply Finset.sum_le_sum
      intro l _
      rw [← offsetEventProbability_eq_real]
      exact offset_failure_le l hgap
    _ = _ := by simp [Line, Direction, mul_comm]

theorem tendsto_initial_failure (F : ℕ → Type*)
    [∀ n, Field (F n)] [∀ n, Fintype (F n)] [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | ∃ l, l ∉ initialDeletedLines M ∧
        ((linePoints l ∩ initiallyRetained M).card : ℝ) < (Fintype.card (F n) : ℝ) / 5})
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
  · filter_upwards [hq.eventually eventually_mean_gap] with n hn
    exact initial_failure_probability_le hn
  · exact tendsto_line_union_bound.comp hq

theorem initial_good_probability_eq_one_sub :
    offsetEventProbability (F := F)
      {M | ∀ l, l ∉ initialDeletedLines M →
        (Fintype.card F : ℝ) / 5 ≤ ((linePoints l ∩ initiallyRetained M).card : ℝ)} =
      1 - offsetEventProbability (F := F)
      {M | ∃ l, l ∉ initialDeletedLines M ∧
        ((linePoints l ∩ initiallyRetained M).card : ℝ) < (Fintype.card F : ℝ) / 5} := by
  let : MeasurableSpace (MergedPairs F) := ⊤
  let : MeasurableSingletonClass (MergedPairs F) := ⟨fun _ => trivial⟩
  have heq : {M : MergedPairs F | ∀ l, l ∉ initialDeletedLines M →
        (Fintype.card F : ℝ) / 5 ≤ ((linePoints l ∩ initiallyRetained M).card : ℝ)} =
      {M | ∃ l, l ∉ initialDeletedLines M ∧
        ((linePoints l ∩ initiallyRetained M).card : ℝ) < (Fintype.card F : ℝ) / 5}ᶜ := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_and, not_lt]
  rw [heq, offsetEventProbability_eq_real,
    probReal_compl_eq_one_sub ((Set.toFinite _).measurableSet),
    ← offsetEventProbability_eq_real]

theorem tendsto_initial_occupancy (F : ℕ → Type*)
    [∀ n, Field (F n)] [∀ n, Fintype (F n)] [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | ∀ l, l ∉ initialDeletedLines M →
        (1 / 5 : ℝ) * (Fintype.card (F n) : ℝ) ≤
          ((linePoints l ∩ initiallyRetained M).card : ℝ)}) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_initial_failure F hq)
  simpa only [one_div, mul_comm (5 : ℝ)⁻¹, ← div_eq_mul_inv,
    initial_good_probability_eq_one_sub, sub_zero] using h

end Balanced.LineOccupancy

end

end OAI
