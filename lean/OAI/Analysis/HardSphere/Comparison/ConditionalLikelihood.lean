import Mathlib
import OAI.Analysis.HardSphere.Geometry.AuxiliaryChecks

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory Function Set Filter
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
open ProbabilityTheory
section NormalizerFacts
variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)] {C : Type*} [Fintype C]
  (checks : C → LocalCheck X)
omit [Fintype C] in
lemma partialNormalizer_le_one {μ : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]
    (s o : Finset ι) (x : ∀ i, X i) : partialNormalizer checks μ s o x ≤ 1 := by
  calc
    _ ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂Measure.pi (fun i : s ↦ μ i) :=
      lintegral_mono fun _ ↦ checkWeight_le_one checks _ _
    _ = 1 := by simp

lemma measurable_partialNormalizer {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    (s o : Finset ι) : Measurable (partialNormalizer checks μ s o) :=
  (measurable_checkWeight checks (s ∪ o)).lmarginal μ

omit [Fintype C] in
lemma UniformInsertionOn.mono {μ : ∀ i, Measure (X i)} {a : ℝ≥0∞}
    {s t : Finset ι} (h : UniformInsertionOn checks μ a t) (hst : s ⊆ t) :
    UniformInsertionOn checks μ a s := fun i hi ↦ h i (hst hi)

lemma checkNormalizer_pos_on {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {a : ℝ≥0∞} (ha : 0 < a) (s : Finset ι)
    (hcompat : UniformInsertionOn checks μ a s) (x : ∀ i, X i) :
    0 < checkNormalizer checks μ s x := by
  have hp := partialNormalizer_pos checks ha hcompat (Finset.disjoint_empty_right s) x
    (show x ∈ retainedEvent checks ∅ from fun c hc ↦
      False.elim ((checks c).nonempty.ne_empty (Finset.subset_empty.mp hc)))
  simpa only [partialNormalizer, checkNormalizer, Finset.union_empty] using hp

lemma checkNormalizer_union_lower_on {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {a : ℝ≥0∞} {t : Finset ι} (hcompat : UniformInsertionOn checks μ a t)
    (s : Finset ι) (hst : Disjoint s t) (x : ∀ i, X i) :
    a ^ t.card * checkNormalizer checks μ s x ≤ checkNormalizer checks μ (s ∪ t) x := by
  have h := partialNormalizer_union_lower checks hcompat s t ∅ (Finset.Subset.refl t)
    (by simpa using hst) x
  simpa only [partialNormalizer, checkNormalizer, Finset.union_empty] using h

end NormalizerFacts

lemma isProbabilityMeasure_compProd_of_mass {X Z : Type*} [MeasurableSpace X]
    [MeasurableSpace Z] (μ : Measure X) [IsFiniteMeasure μ]
    (κ : Kernel X Z) [IsFiniteKernel κ] (hm : ∫⁻ x, κ x Set.univ ∂μ = 1) :
    IsProbabilityMeasure (μ.compProd κ) where
  measure_univ := by simpa only [Measure.compProd_apply MeasurableSet.univ,
    Set.preimage_univ] using hm

section ConditionalOverlap
variable {ι : Type*} [DecidableEq ι] {X Z W : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Z i)]
  [∀ i, MeasurableSpace (W i)]
  {C D : Type*} [Fintype C] [Fintype D]
  (checks : C → LocalCheck (fun i ↦ X i × Z i))
  (other : D → LocalCheck (fun i ↦ X i × W i))
  (κ : ∀ i, Kernel (X i) (Z i)) [∀ i, IsFiniteKernel (κ i)]
  (η : ∀ i, Kernel (X i) (W i)) [∀ i, IsFiniteKernel (η i)]

lemma conditionalDensity_overlap_bound
    {μ : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]
    (fs ft cs ct os ot : Finset ι)
    (hff : Disjoint fs ft) (hfn : Disjoint (fs ∪ ft) (cs ∪ ct))
    {G : ℝ≥0∞}
    (hκb : ∀ i x, κ i x Set.univ ≤ G)
    (hκm : ∀ i, ∫⁻ x, κ i x Set.univ ∂μ i = 1)
    (hηm : ∀ i, ∫⁻ x, η i x Set.univ ∂μ i = 1)
    (x : ∀ i, X i) (z : ∀ i, Z i) (w : ∀ i, W i) :
    lmarginal μ ((fs ∪ ft) ∪ (cs ∪ ct))
      (fun y ↦ conditionalDensity checks κ (fs ∪ cs) os y z *
        conditionalDensity other η (ft ∪ ct) ot y w) x ≤
      (checkNormalizer checks (fun i ↦ (μ i).compProd (κ i)) fs (fun i ↦ (x i,z i)) *
       checkNormalizer other (fun i ↦ (μ i).compProd (η i)) ft (fun i ↦ (x i,w i))) *
       G ^ (cs ∩ ct).card := by
  apply le_trans (lmarginal_mono (fun y ↦
    mul_le_mul' (conditionalDensity_le_auxiliaryDensity checks κ _ _ y z)
      (conditionalDensity_le_auxiliaryDensity other η _ _ y w)) x)
  exact auxiliaryDensity_overlap_bound checks other κ η fs ft cs ct hff hfn hκb hκm hηm x z w

end ConditionalOverlap

lemma finite_normalizer_cancellation {p q zs zt ys yt : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpT : p ≠ ⊤) (hq0 : q ≠ 0) (hqT : q ≠ ⊤)
    (hzs0 : zs ≠ 0) (hzsT : zs ≠ ⊤) (hzt0 : zt ≠ 0) (hztT : zt ≠ ⊤)
    (hys0 : ys ≠ 0) (hysT : ys ≠ ⊤) (hyt0 : yt ≠ 0) (hytT : yt ≠ ⊤)
    (b : ℝ≥0∞) :
    ((zs / (p * ys)) * (zt / (q * yt)) * ((ys * yt) * b)) /
        ((p * q) * (zs * zt)) = b / ((p * q) ^ 2) := by
  have hpq0 : p * q ≠ 0 := mul_ne_zero hp0 hq0
  have hpqT : p * q ≠ ⊤ := ENNReal.mul_ne_top hpT hqT
  simp only [div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl hp0) (Or.inl hpT),
    ENNReal.mul_inv (Or.inl hq0) (Or.inl hqT),
    ENNReal.mul_inv (Or.inl hpq0) (Or.inl hpqT),
    ENNReal.mul_inv (Or.inl hzs0) (Or.inl hzsT), ENNReal.inv_pow]
  calc
    _ = (zs * zs⁻¹) * (zt * zt⁻¹) * (ys * ys⁻¹) * (yt * yt⁻¹) *
      (b * (p⁻¹ * q⁻¹) ^ 2) := by simp only [pow_two]; ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel hzs0 hzsT,
      ENNReal.mul_inv_cancel hzt0 hztT, ENNReal.mul_inv_cancel hys0 hysT,
      ENNReal.mul_inv_cancel hyt0 hytT]; simp

section ConditionalLower
variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)] {C : Type*} [Fintype C]
  (checks : C → LocalCheck X)

lemma partialNormalizer_ge_far {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {a : ℝ≥0∞} {s t o : Finset ι}
    (hcompat : UniformInsertionOn checks μ a (s ∪ t))
    (hto : Disjoint (s ∪ o) t) (hso : Disjoint s o)
    (hsep : SeparatedChecks checks s o) (x : ∀ i, X i)
    (hx : x ∈ retainedEvent checks o) :
    a ^ t.card * checkNormalizer checks μ s x ≤
      partialNormalizer checks μ (s ∪ t) o x := by
  have h := partialNormalizer_union_lower checks hcompat s t o Finset.subset_union_right hto x
  rwa [partialNormalizer_far_eq checks hso hsep x, checkWeight,
    Set.indicator_of_mem hx, mul_one] at h

end ConditionalLower

section CancellationEstimate
variable {ι : Type*} [DecidableEq ι] {X Z W : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Z i)]
  [∀ i, MeasurableSpace (W i)]
  {R C D : Type*} [Fintype R] [Fintype C] [Fintype D]
  (reference : R → LocalCheck X)
  (checks : C → LocalCheck (fun i ↦ X i × Z i))
  (other : D → LocalCheck (fun i ↦ X i × W i))
  (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
  (κ : ∀ i, Kernel (X i) (Z i)) [∀ i, IsFiniteKernel (κ i)]
  (η : ∀ i, Kernel (X i) (W i)) [∀ i, IsFiniteKernel (η i)]

def conditionalLikelihood (s o : Finset ι) (x : ∀ i, X i) (z : ∀ i, Z i) : ℝ≥0∞ :=
  (partialNormalizer reference μ s o x /
    partialNormalizer checks (fun i ↦ (μ i).compProd (κ i)) s o (fun i ↦ (x i,z i))) *
      conditionalDensity checks κ s o x z

lemma measurable_conditionalLikelihood (s o : Finset ι) (z : ∀ i, Z i) :
    Measurable (fun x ↦ conditionalLikelihood reference checks μ κ s o x z) := by
  apply Measurable.mul
  · apply Measurable.div (measurable_partialNormalizer reference s o)
    exact (measurable_partialNormalizer checks s o).comp
      (Measurable.of_eval fun i ↦ (measurable_pi_apply i).prodMk measurable_const)
  · exact measurable_conditionalDensity checks κ s o z

theorem conditional_cancellation
    (fs ft cs ct os ot : Finset ι)
    (hff : Disjoint fs ft) (hfn : Disjoint (fs ∪ ft) (cs ∪ ct))
    (hos : Disjoint (fs ∪ cs) os) (hot : Disjoint (ft ∪ ct) ot)
    (hosU : (fs ∪ cs) ∪ os = (fs ∪ ft) ∪ (cs ∪ ct))
    (hotU : (ft ∪ ct) ∪ ot = (fs ∪ ft) ∪ (cs ∪ ct))
    {a G : ℝ≥0∞} (ha : 0 < a) (ha1 : a ≤ 1)
    (hκb : ∀ i x, κ i x Set.univ ≤ G)
    (hκm : ∀ i, ∫⁻ x, κ i x Set.univ ∂μ i = 1)
    (hηm : ∀ i, ∫⁻ x, η i x Set.univ ∂μ i = 1)
    (hRef : UniformInsertionOn reference μ a ((fs ∪ ft) ∪ (cs ∪ ct)))
    (hS : UniformInsertionOn checks (fun i ↦ (μ i).compProd (κ i)) a (fs ∪ cs))
    (hT : UniformInsertionOn other (fun i ↦ (μ i).compProd (η i)) a (ft ∪ ct))
    (hsepRef : SeparatedChecks reference fs ft)
    (hsepS : SeparatedChecks checks fs os) (hsepT : SeparatedChecks other ft ot)
    (hOutsideS : ∀ (x : ∀ i, X i) (z : ∀ i, Z i), x ∈ retainedEvent reference os →
      (fun i ↦ (x i,z i)) ∈ retainedEvent checks os)
    (hOutsideT : ∀ (x : ∀ i, X i) (w : ∀ i, W i), x ∈ retainedEvent reference ot →
      (fun i ↦ (x i,w i)) ∈ retainedEvent other ot)
    (x : ∀ i, X i) (z : ∀ i, Z i) (w : ∀ i, W i) :
    lmarginal μ ((fs ∪ ft) ∪ (cs ∪ ct))
      (fun y ↦ checkWeight reference ((fs ∪ ft) ∪ (cs ∪ ct)) y *
        conditionalLikelihood reference checks μ κ (fs ∪ cs) os y z *
        conditionalLikelihood reference other μ η (ft ∪ ct) ot y w) x /
      checkNormalizer reference μ ((fs ∪ ft) ∪ (cs ∪ ct)) x ≤
      G ^ (cs ∩ ct).card / a ^ (2 * (cs.card + ct.card)) := by
  let U := (fs ∪ ft) ∪ (cs ∪ ct)
  let ν i := (μ i).compProd (κ i)
  let ξ i := (μ i).compProd (η i)
  have : ∀ i, IsProbabilityMeasure (ν i) :=
    fun i ↦ isProbabilityMeasure_compProd_of_mass (μ i) (κ i) (hκm i)
  have : ∀ i, IsProbabilityMeasure (ξ i) :=
    fun i ↦ isProbabilityMeasure_compProd_of_mass (μ i) (η i) (hηm i)
  let zs := checkNormalizer reference μ fs x
  let zt := checkNormalizer reference μ ft x
  let ys := checkNormalizer checks ν fs (fun i ↦ (x i,z i))
  let yt := checkNormalizer other ξ ft (fun i ↦ (x i,w i))
  have hfsU : fs ⊆ U := Finset.subset_union_left.trans Finset.subset_union_left
  have hftU : ft ⊆ U := Finset.subset_union_right.trans Finset.subset_union_left
  have hNearU : cs ∪ ct ⊆ U := Finset.subset_union_right
  have hzs : 0 < zs := checkNormalizer_pos_on reference ha fs
    (UniformInsertionOn.mono reference hRef hfsU) x
  have hzt : 0 < zt := checkNormalizer_pos_on reference ha ft
    (UniformInsertionOn.mono reference hRef hftU) x
  have hys : 0 < ys := checkNormalizer_pos_on checks ha fs
    (UniformInsertionOn.mono checks hS Finset.subset_union_left) _
  have hyt : 0 < yt := checkNormalizer_pos_on other ha ft
    (UniformInsertionOn.mono other hT Finset.subset_union_left) _
  have hzsT : zs ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (checkNormalizer_le_one reference fs x)
  have hztT : zt ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (checkNormalizer_le_one reference ft x)
  have hysT : ys ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (checkNormalizer_le_one checks fs _)
  have hytT : yt ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (checkNormalizer_le_one other ft _)
  have haT : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha1
  have hZU : a ^ (cs.card + ct.card) * (zs * zt) ≤ checkNormalizer reference μ U x := by
    calc
      _ ≤ a ^ (cs ∪ ct).card * (zs * zt) :=
        mul_le_mul_left (pow_le_pow_right_of_le_one' ha1 (Finset.card_union_le cs ct)) _
      _ = a ^ (cs ∪ ct).card * checkNormalizer reference μ (fs ∪ ft) x := by
        rw [checkNormalizer_union_eq_mul reference hff hsepRef]
      _ ≤ _ := checkNormalizer_union_lower_on reference
        (UniformInsertionOn.mono reference hRef hNearU) (fs ∪ ft) hfn x
  have hfs : Disjoint fs cs := hfn.mono Finset.subset_union_left Finset.subset_union_left
  have hft : Disjoint ft ct := hfn.mono Finset.subset_union_right Finset.subset_union_right
  have hfsos : Disjoint fs os := hos.mono_left Finset.subset_union_left
  have hftot : Disjoint ft ot := hot.mono_left Finset.subset_union_left
  have hfcso : Disjoint (fs ∪ os) cs := Finset.disjoint_union_left.mpr
    ⟨hfs, (hos.mono_left Finset.subset_union_right).symm⟩
  have hftcto : Disjoint (ft ∪ ot) ct := Finset.disjoint_union_left.mpr
    ⟨hft, (hot.mono_left Finset.subset_union_right).symm⟩
  let rs := zs / (a ^ cs.card * ys)
  let rt := zt / (a ^ ct.card * yt)
  have hratioS (y : ∀ i, X i) (hy : y ∈ retainedEvent reference U) :
      partialNormalizer reference μ (fs ∪ cs) os y /
        partialNormalizer checks ν (fs ∪ cs) os (fun i ↦ (y i,z i)) ≤ rs := by
    have hyo : y ∈ retainedEvent reference os := fun c hc ↦ hy c
      (hc.trans (by change os ⊆ (fs ∪ ft) ∪ (cs ∪ ct); rw [← hosU]; exact Finset.subset_union_right))
    have hl := partialNormalizer_ge_far checks hS hfcso hfsos hsepS
      (fun i ↦ (y i,z i)) (hOutsideS y z hyo)
    rw [checkNormalizer_const checks fs _ (fun i ↦ (x i,z i))] at hl
    have hu := partialNormalizer_le_far reference (μ := μ) (o := os) hfs y
    rw [checkNormalizer_const reference fs y x] at hu
    exact ENNReal.div_le_div hu hl
  have hratioT (y : ∀ i, X i) (hy : y ∈ retainedEvent reference U) :
      partialNormalizer reference μ (ft ∪ ct) ot y /
        partialNormalizer other ξ (ft ∪ ct) ot (fun i ↦ (y i,w i)) ≤ rt := by
    have hyo : y ∈ retainedEvent reference ot := fun c hc ↦ hy c
      (hc.trans (by change ot ⊆ (fs ∪ ft) ∪ (cs ∪ ct); rw [← hotU]; exact Finset.subset_union_right))
    have hl := partialNormalizer_ge_far other hT hftcto hftot hsepT
      (fun i ↦ (y i,w i)) (hOutsideT y w hyo)
    rw [checkNormalizer_const other ft _ (fun i ↦ (x i,w i))] at hl
    have hu := partialNormalizer_le_far reference (μ := μ) (o := ot) hft y
    rw [checkNormalizer_const reference ft y x] at hu
    exact ENNReal.div_le_div hu hl
  let H (y : ∀ i, X i) := conditionalDensity checks κ (fs ∪ cs) os y z *
    conditionalDensity other η (ft ∪ ct) ot y w
  have hH : Measurable H := (measurable_conditionalDensity checks κ _ _ z).mul
    (measurable_conditionalDensity other η _ _ w)
  have hpoint (y : ∀ i, X i) :
      checkWeight reference U y * conditionalLikelihood reference checks μ κ (fs ∪ cs) os y z *
        conditionalLikelihood reference other μ η (ft ∪ ct) ot y w ≤ (rs * rt) * H y := by
    classical
    by_cases hy : y ∈ retainedEvent reference U
    · simp only [checkWeight, Set.indicator_of_mem hy, one_mul, conditionalLikelihood]
      calc
        _ ≤ (rs * conditionalDensity checks κ (fs ∪ cs) os y z) *
            (rt * conditionalDensity other η (ft ∪ ct) ot y w) :=
          mul_le_mul' (mul_le_mul_left (hratioS y hy) _) (mul_le_mul_left (hratioT y hy) _)
        _ = _ := by dsimp [H]; ac_rfl
    · simp [checkWeight, hy]
  have hIntegral : lmarginal μ U
      (fun y ↦ checkWeight reference U y *
        conditionalLikelihood reference checks μ κ (fs ∪ cs) os y z *
        conditionalLikelihood reference other μ η (ft ∪ ct) ot y w) x ≤
      (rs * rt) * ((ys * yt) * G ^ (cs ∩ ct).card) := by
    calc
      _ ≤ lmarginal μ U (fun y ↦ (rs * rt) * H y) x := lmarginal_mono hpoint x
      _ = (rs * rt) * lmarginal μ U H x :=
        lintegral_const_mul _ (hH.comp (measurable_updateFinset (x := x) (s := U)))
      _ ≤ _ := mul_le_mul_right
        (conditionalDensity_overlap_bound checks other κ η fs ft cs ct os ot hff hfn
          hκb hκm hηm x z w) _
  calc
    _ ≤ ((rs * rt) * ((ys * yt) * G ^ (cs ∩ ct).card)) /
        (a ^ (cs.card + ct.card) * (zs * zt)) := ENNReal.div_le_div hIntegral hZU
    _ = G ^ (cs ∩ ct).card / ((a ^ cs.card * a ^ ct.card) ^ 2) := by
      rw [pow_add]
      exact finite_normalizer_cancellation (ne_of_gt (ENNReal.pow_pos ha _))
        (ENNReal.pow_ne_top haT) (ne_of_gt (ENNReal.pow_pos ha _)) (ENNReal.pow_ne_top haT)
        (ne_of_gt hzs) hzsT (ne_of_gt hzt) hztT (ne_of_gt hys) hysT (ne_of_gt hyt) hytT _
    _ = _ := by rw [← pow_add, ← pow_mul, Nat.mul_comm 2]

end CancellationEstimate

section LikelihoodIdentity
variable {ι : Type*} [DecidableEq ι] {X Z : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Z i)]
  {R C : Type*} [Fintype R] [Fintype C]
  (reference : R → LocalCheck X) (checks : C → LocalCheck (fun i ↦ X i × Z i))
  (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
  (κ : ∀ i, Kernel (X i) (Z i)) [∀ i, IsFiniteKernel (κ i)]

omit [Fintype R] [∀ i, IsProbabilityMeasure (μ i)] in
lemma partialNormalizer_updateFinset (s o : Finset ι) (x : ∀ i, X i) (u : ∀ i : s, X i) :
    partialNormalizer reference μ s o (Function.updateFinset x s u) =
      partialNormalizer reference μ s o x := by
  apply lmarginal_congr
  intro i hi
  simp [Function.updateFinset, hi]

omit [Fintype R] in
lemma partialNormalizer_le_outside {s o : Finset ι} (hso : Disjoint s o) (x : ∀ i, X i) :
    partialNormalizer reference μ s o x ≤ checkWeight reference o x := by
  calc
    _ ≤ lmarginal μ s (checkWeight reference o) x :=
      lmarginal_mono (checkWeight_antitone reference Finset.subset_union_right) x
    _ = _ := lmarginal_of_disjoint_depends
      (fun _ _ h ↦ checkWeight_depends reference o h) hso.symm x

omit [Fintype R] [Fintype C] [∀ i, IsFiniteKernel (κ i)] in

lemma conditionalDensity_reference_support (s o : Finset ι)
    (hincl : ∀ (x : ∀ i, X i) (z : ∀ i, Z i),
      checkWeight checks (s ∪ o) (fun i ↦ (x i,z i)) ≤ checkWeight reference (s ∪ o) x)
    (x : ∀ i, X i) (z : ∀ i, Z i) :
    checkWeight reference (s ∪ o) x * conditionalDensity checks κ s o x z =
      conditionalDensity checks κ s o x z := by
  classical
  by_cases hx : x ∈ retainedEvent reference (s ∪ o)
  · simp [checkWeight, hx]
  · have hz : conditionalDensity checks κ s o x z = 0 := by
      apply le_antisymm _ zero_le
      calc
        _ ≤ lmarginal (fun i ↦ κ i (x i)) s (fun _ ↦ checkWeight reference (s ∪ o) x) z :=
          lmarginal_mono (hincl x) z
        _ = 0 := by simp [lmarginal, checkWeight, hx]
    simp [hz]

omit [Fintype R] in

theorem conditionalLikelihood_marginal (s o : Finset ι) (hso : Disjoint s o)
    {a : ℝ≥0∞} (ha : 0 < a)
    (hκm : ∀ i, ∫⁻ x, κ i x Set.univ ∂μ i = 1)
    (hcompat : UniformInsertionOn checks (fun i ↦ (μ i).compProd (κ i)) a s)
    (hOutside : ∀ (x : ∀ i, X i) (z : ∀ i, Z i), x ∈ retainedEvent reference o →
      (fun i ↦ (x i,z i)) ∈ retainedEvent checks o)
    (hincl : ∀ (x : ∀ i, X i) (z : ∀ i, Z i),
      checkWeight checks (s ∪ o) (fun i ↦ (x i,z i)) ≤ checkWeight reference (s ∪ o) x)
    (x : ∀ i, X i) (z : ∀ i, Z i) :
    lmarginal μ s (fun y ↦ checkWeight reference (s ∪ o) y *
      conditionalLikelihood reference checks μ κ s o y z) x =
      partialNormalizer reference μ s o x := by
  let ν i := (μ i).compProd (κ i)
  have : ∀ i, IsProbabilityMeasure (ν i) :=
    fun i ↦ isProbabilityMeasure_compProd_of_mass (μ i) (κ i) (hκm i)
  let Z₀ := partialNormalizer reference μ s o x
  let Y₀ := partialNormalizer checks ν s o (fun i ↦ (x i,z i))
  have hYu (u : ∀ i : s, X i) :
      partialNormalizer checks ν s o (fun i ↦ (Function.updateFinset x s u i,z i)) = Y₀ := by
    apply lmarginal_congr
    intro i hi
    simp [Function.updateFinset, hi]
  have hRatio : ∀ (u : ∀ i : s, X i),
      partialNormalizer reference μ s o (Function.updateFinset x s u) /
        partialNormalizer checks ν s o (fun i ↦ (Function.updateFinset x s u i,z i)) = Z₀ / Y₀ := by
    intro u
    rw [partialNormalizer_updateFinset, hYu]
  have hm := measurable_conditionalDensity checks κ s o z
  calc
    _ = lmarginal μ s
        (fun y ↦ (partialNormalizer reference μ s o y /
          partialNormalizer checks ν s o (fun i ↦ (y i,z i))) *
          conditionalDensity checks κ s o y z) x := by
      apply lintegral_congr
      intro u
      change checkWeight reference (s ∪ o) (Function.updateFinset x s u) *
        conditionalLikelihood reference checks μ κ s o (Function.updateFinset x s u) z = _
      dsimp only [conditionalLikelihood]
      rw [mul_left_comm, conditionalDensity_reference_support reference checks κ s o hincl]
    _ = (Z₀ / Y₀) * lmarginal μ s (fun y ↦ conditionalDensity checks κ s o y z) x := by
      change (∫⁻ u, (partialNormalizer reference μ s o (Function.updateFinset x s u) /
          partialNormalizer checks ν s o (fun i ↦ (Function.updateFinset x s u i,z i))) *
          conditionalDensity checks κ s o (Function.updateFinset x s u) z
        ∂Measure.pi (fun i : s ↦ μ i)) = _
      simp_rw [hRatio]
      exact lintegral_const_mul _ (hm.comp (measurable_updateFinset (x := x) (s := s)))
    _ = (Z₀ / Y₀) * Y₀ := by rw [conditionalDensity_integral]
    _ = Z₀ := by
      classical
      by_cases hx : x ∈ retainedEvent reference o
      · have hypos : 0 < Y₀ := partialNormalizer_pos checks ha hcompat hso _ (hOutside x z hx)
        have hyT : Y₀ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
          (partialNormalizer_le_one checks s o _)
        exact ENNReal.div_mul_cancel (ne_of_gt hypos) hyT
      · have hz0 : Z₀ = 0 := le_antisymm (by
          simpa [checkWeight, hx] using partialNormalizer_le_outside reference μ hso x) zero_le
        simp [hz0]

end LikelihoodIdentity

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)] {R : Type*} [Fintype R]
  (reference : R → LocalCheck X)
  (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

def referenceMeasure (s : Finset ι) (x : ∀ i, X i) : Measure (∀ i : s, X i) :=
  (Measure.pi (fun i : s ↦ μ i)).withDensity
    (fun u ↦ checkWeight reference s (Function.updateFinset x s u) /
      checkNormalizer reference μ s x)

omit [∀ i, IsProbabilityMeasure (μ i)] in
lemma referenceMeasure_mass (s : Finset ι) (x : ∀ i, X i) :
    referenceMeasure reference μ s x Set.univ =
      checkNormalizer reference μ s x / checkNormalizer reference μ s x := by
  rw [referenceMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  simp only [div_eq_mul_inv]
  exact lintegral_mul_const _
    ((measurable_checkWeight reference s).comp measurable_updateFinset)

lemma referenceMeasure_probability {a : ℝ≥0∞} (ha : 0 < a) (s : Finset ι)
    (hcompat : UniformInsertionOn reference μ a s) (x : ∀ i, X i) :
    IsProbabilityMeasure (referenceMeasure reference μ s x) := by
  refine ⟨?_⟩
  rw [referenceMeasure_mass]
  exact ENNReal.div_self (ne_of_gt (checkNormalizer_pos_on reference ha s hcompat x))
    (ne_top_of_le_ne_top ENNReal.one_ne_top (checkNormalizer_le_one reference (μ := μ) s x))

end HardSphere.Comparison
end

end OAI
