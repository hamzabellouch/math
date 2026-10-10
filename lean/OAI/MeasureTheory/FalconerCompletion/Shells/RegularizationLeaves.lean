import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.WeightLeafLabel
import OAI.MeasureTheory.FalconerCompletion.Shells.LeafUnion

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def regularizationLeaves (μ : Measure (EuclideanSpace ℝ (Fin d))) (N : ℕ) : Finset (CellPath d) :=
  retainedLeaves μ N ((2:ℝ≥0∞)^((d+2)*N))⁻¹

noncomputable def regularizationLabel (μ : Measure (EuclideanSpace ℝ (Fin d))) (N B : ℕ) : CellPath d → List ℕ :=
  blockLabel (regularizationLeaves μ N) N B
    (weightLeafLabel ((d+2)*N) (fun p => (μ (treeCell p)).toReal)) (N/B+1)

noncomputable def sourceProfile (μ : Measure (EuclideanSpace ℝ (Fin d))) (N B : ℕ) (p : CellPath d) : ℝ → ℝ :=
  regularizedProfile (regularizationLeaves μ N) (regularizationLabel μ N B) N B (N/B+1) p

noncomputable def sourceClass (μ : Measure (EuclideanSpace ℝ (Fin d))) (N B : ℕ) (p : CellPath d) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  normalizedClass μ (regularizationLeaves μ N) (regularizationLabel μ N B) (regularizationLabel μ N B p)

lemma regularizationLeaves_subset (μ : Measure (EuclideanSpace ℝ (Fin d))) (N : ℕ) :
    regularizationLeaves μ N ⊆ dyadicPaths N := Finset.filter_subset _ _

lemma regularization_weight_bounds (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (N : ℕ) {p : CellPath d} (hp : p ∈ regularizationLeaves μ N) :
    1 ≤ (2:ℝ)^((d+2)*N)*(μ (treeCell p)).toReal ∧ (μ (treeCell p)).toReal ≤ 1 := by
  have hm := (Finset.mem_filter.mp hp).2
  have ht := ENNReal.toReal_mono (measure_ne_top μ _) hm
  simp only [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at ht
  constructor
  · simpa only [mul_comm] using (inv_le_iff_one_le_mul₀ (by positivity : 0 < (2:ℝ)^((d+2)*N))).mp ht
  · exact (ENNReal.toReal_le_toReal (measure_ne_top μ _) ENNReal.one_ne_top).mpr prob_le_one

lemma normalizedClass_real (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (L : Finset (CellPath d)) (F : CellPath d → List ℕ) (T : List ℕ) (S : Set (EuclideanSpace ℝ (Fin d))) :
    (normalizedClass μ L F T S).toReal =
      ((μ.restrict (leafUnion (classLeaves L F T))) S).toReal /
        (μ (leafUnion (classLeaves L F T))).toReal := by
  simp only [normalizedClass,classMeasure,Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply_univ,ENNReal.toReal_mul,ENNReal.toReal_inv,div_eq_mul_inv,mul_comm]

lemma sourceClass_probability (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (N B : ℕ) {p : CellPath d} (hp : p ∈ regularizationLeaves μ N) :
    IsProbabilityMeasure (sourceClass μ N B p) := by
  classical
  apply normalizedClass_probability
  have hw := (regularization_weight_bounds μ N hp).1
  have hp0 : 0 < (μ (treeCell p)).toReal := by
    have := pow_pos (by norm_num : (0:ℝ) < 2) ((d+2)*N)
    nlinarith
  have hsub : treeCell p ⊆ leafUnion
      (classLeaves (regularizationLeaves μ N) (regularizationLabel μ N B) (regularizationLabel μ N B p)) := by
    intro x hx
    exact mem_iUnion₂.mpr ⟨p, by simp [classLeaves,hp],hx⟩
  intro he
  have hh := measure_mono (μ := μ) hsub
  change μ (treeCell p) ≤ μ (leafUnion _) at hh
  have he' : μ (leafUnion (classLeaves (regularizationLeaves μ N)
      (regularizationLabel μ N B) (regularizationLabel μ N B p))) = 0 := by
    simpa only [classMeasure, Measure.restrict_apply_univ] using he
  rw [he'] at hh
  have : μ (treeCell p) = 0 := le_antisymm hh bot_le
  simp [this] at hp0

lemma sourceClass_grid_comparison (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) {p : CellPath d} (hp : p ∈ regularizationLeaves μ N)
    {i : ℕ} (hi : i ≤ N/B+1) {P : CellPath d}
    (hP : P ∈ (classLeaves (regularizationLeaves μ N) (regularizationLabel μ N B)
      (regularizationLabel μ N B p)).image (List.take (blockDepth N B i))) :
    (((2:ℝ)^N)^(-sourceProfile μ N B p (blockDepth N B i)))/(2:ℝ)^(N/B+2) ≤
      (sourceClass μ N B p (treeCell P)).toReal ∧
    (sourceClass μ N B p (treeCell P)).toReal ≤
      (2:ℝ)^(N/B+2)*(((2:ℝ)^N)^(-sourceProfile μ N B p (blockDepth N B i))) := by
  classical
  let C := classLeaves (regularizationLeaves μ N) (regularizationLabel μ N B) (regularizationLabel μ N B p)
  have hC : C ⊆ dyadicPaths N := fun q hq => regularizationLeaves_subset μ N (Finset.mem_filter.mp hq).1
  have hlen : P.length = blockDepth N B i := by
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
    have hqN := (mem_dyadicPaths _ _).mp (hC hq)
    simp [List.length_take,hqN]
  have hh := weighted_class_profile_grid hN (regularizationLeaves_subset μ N)
    (fun q => (μ (treeCell q)).toReal) (fun q hq => regularization_weight_bounds μ N hq) hB hp hi hP
  change _ ≤ _ ∧ _ ≤ _ at hh
  rw [sourceClass,normalizedClass_real,
    restriction_prefix_mass_real μ (Nat.sub_le _ _) hC hlen,
    restriction_total_mass_real μ hC]
  simpa only [sourceProfile,C,regularizationLabel,blockDepth,Nat.add_assoc, Nat.reduceAdd] using hh

lemma normalizedClass_occupied_prefix (μ : Measure (EuclideanSpace ℝ (Fin d)))
    {N n : ℕ} (hn : n ≤ N) {L : Finset (CellPath d)}
    (hL : L ⊆ dyadicPaths N) (F : CellPath d → List ℕ) (T : List ℕ)
    {P : CellPath d} (hP : P.length = n)
    (hp : 0 < (normalizedClass μ L F T (treeCell P)).toReal) :
    P ∈ (classLeaves L F T).image (List.take n) := by
  classical
  have hC : classLeaves L F T ⊆ dyadicPaths N := fun q hq => hL (Finset.mem_filter.mp hq).1
  have hne : (prefixFiber (classLeaves L F T) n P).Nonempty := by
    by_contra he
    have hz : prefixFiber (classLeaves L F T) n P = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    rw [normalizedClass_real,restriction_prefix_mass μ hn hC hP,hz] at hp
    simp at hp
  obtain ⟨q,hq⟩ := hne
  obtain ⟨hq,he⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_image.mpr ⟨q,hq,he⟩

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
