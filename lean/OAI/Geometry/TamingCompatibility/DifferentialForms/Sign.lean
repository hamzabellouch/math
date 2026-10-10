import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.StarTwoComp
import OAI.Geometry.TamingCompatibility.Functional.GramOrthonormalBasis

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.OrientationSign
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sign (t : ℝ) : ℝ := if 0 < t then 1 else -1

lemma abs_mul_div (t a : ℝ) (ht : t ≠ 0) : |t| * (a / t) = sign t * a := by
  by_cases h : 0 < t
  · rw [abs_of_pos h,sign,ite_eq_left h]
    field_simp
  · have hn : t < 0 := lt_of_le_of_ne (le_of_not_gt h) ht
    rw [abs_of_neg hn,sign,ite_eq_right h]
    field_simp

omit [NormedSpace ℝ E] in
lemma locally_constant {U : Set E} (hU : IsOpen U) {f : E → ℝ}
    (hf : ContinuousOn f U) {x : E} (hx : x ∈ U) (hn : f x ≠ 0) :
    (fun y => sign (f y)) =ᶠ[𝓝 x] (fun _ => sign (f x)) := by
  have hc := (hf x hx).continuousAt (hU.mem_nhds hx)
  by_cases h : 0 < f x
  · filter_upwards [continuousAt_const.eventually_lt hc h] with y hy
    simp only [sign,ite_eq_left h,ite_eq_left hy]
  · have hp : f x < 0 := lt_of_le_of_ne (le_of_not_gt h) hn
    filter_upwards [hc.eventually_lt continuousAt_const hp] with y hy
    simp only [sign,ite_eq_right h,ite_eq_right (not_lt_of_ge hy.le)]

lemma contDiffOn {U : Set E} (hU : IsOpen U) {f : E → ℝ}
    (hf : ContinuousOn f U) (hn : ∀ x ∈ U, f x ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => sign (f x)) U := by
  intro x hx
  exact (contDiffAt_const.congr_of_eventuallyEq (locally_constant hU hf hx (hn x hx))).contDiffWithinAt

lemma extDeriv_smul {U : Set E} (hU : IsOpen U) {f : E → ℝ}
    (hf : ContinuousOn f U) {x : E} (hx : x ∈ U) (hn : f x ≠ 0)
    {k : ℕ} (α : E → E [⋀^Fin k]→L[ℝ] ℝ) :
    extDeriv (fun y => sign (f y) • α y) x = sign (f x) • extDeriv α x := by
  have he : (fun y => sign (f y) • α y) =ᶠ[𝓝 x] (fun y => sign (f x) • α y) :=
    (locally_constant hU hf hx hn).smul (Filter.EventuallyEq.refl _ _)
  rw [he.extDeriv_eq]
  exact _root_.extDeriv_fun_smul (sign (f x)) α

end TamingCompatibility.OrientationSign

namespace TamingCompatibility.ExteriorForms
open ContinuousAlternatingMap
variable {E D P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma volumeSquare_contDiffOn {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {U : Set P} {n : WithTop ℕ∞} {F : P → Form (E := E) 2}
    (hF : ContDiffOn ℝ n F U) : ContDiffOn ℝ n (fun x => volumeSquare (F x)) U := by
  apply FormSmooth.contDiffOn_of_basis b
  intro a
  simp_rw [volumeSquare_apply_vec]
  have hf (v : Fin 2 → E) : ContDiffOn ℝ n (fun x => F x v) U :=
    (ContinuousAlternatingMap.apply ℝ E ℝ v).contDiff.comp_contDiffOn hF
  exact ((hf _).mul (hf _)).sub ((hf _).mul (hf _)) |>.add ((hf _).mul (hf _))

end TamingCompatibility.ExteriorForms

namespace TamingCompatibility.ManifoldTop
open Bundle ContinuousAlternatingMap ManifoldHodge ExteriorForms
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

def basisIndex : Fin (Module.finrank ℝ Space) ≃ Fin 4 := finCongr (by simp [Space])
def basis : Module.Basis (Fin 4) ℝ Space := (stdOrthonormalBasis ℝ Space).toBasis.reindex basisIndex

lemma density_basis (B : Space →L[ℝ] Space →L[ℝ] ℝ) :
    MetricDensity.density (MetricDensity.gram basis B) =
      MetricDensity.density (MetricDensity.gram (stdOrthonormalBasis ℝ Space).toBasis B) := by
  unfold MetricDensity.density
  congr 1
  have he : MetricDensity.gram basis B =
      (MetricDensity.gram (stdOrthonormalBasis ℝ Space).toBasis B).submatrix basisIndex.symm basisIndex.symm := by
    ext i j
    simp [MetricDensity.gram,basis,Module.Basis.reindex_apply]
  rw [he,Matrix.det_submatrix_equiv_self]

def volumeForm (J : AlmostComplexStructure X) (α : TwoForm X) : ManifoldForms.Form X 4 :=
  fun x => volumeSquare (E := Space) (invariantPart J α x)

lemma pullback_volumeForm (J : AlmostComplexStructure X) (α : TwoForm X) (f : Space → X) (z : Space) :
    ManifoldForms.pullback (volumeForm J α) f z =
      volumeSquare (ManifoldForms.pullback (invariantPart J α) f z) :=
  volumeSquare_comp (E := Space) (D := Space) _ _

lemma volumeForm_smooth (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) :
    ManifoldForms.Smooth (volumeForm J α) := by
  intro f U hU hf
  change ContDiffOn ℝ ∞ (ManifoldForms.pullback (volumeForm J α) f) U
  have he : ManifoldForms.pullback (volumeForm J α) f =
      fun z => volumeSquare (ManifoldForms.pullback (invariantPart J α) f z) :=
    funext (pullback_volumeForm J α f)
  rw [he]
  exact volumeSquare_contDiffOn basis ((hs.invariantPart J) f U hU hf)

lemma volumeForm_ne_zero (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (x : X) :
    volumeForm J α x ≠ 0 := by
  let g : MetricModel.Metric Space :=
    ⟨associatedBilinear J (invariantPart J α) x,
      (invariantPart_isInvariant J α).associatedBilinear_symm x,
      (tames_invariantPart ht).associatedBilinear_pos x⟩
  exact VolumeNormalization.volume_ne_zero g (J.endomorphism x) (J.square x)
    ((invariantPart_isInvariant J α).associatedBilinear_hermitian x)
    (by simp [Space]) (invariantPart J α x)
    (fun u v => (associatedBilinear_invariantPart_fundamental J α x u v).symm)

def coefficient (J : AlmostComplexStructure X) (α : TwoForm X) (β : ManifoldForms.Form X 4) : X → ℝ :=
  fun x => TopForms.coefficient basis (volumeForm J α x) (β x)

lemma coefficient_chart (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (β : ManifoldForms.Form X 4) (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    coefficient J α β ((extChartAt Model p).symm z) =
      (ManifoldForms.pullback β (extChartAt Model p).symm z basis) /
      (ManifoldForms.pullback (volumeForm J α) (extChartAt Model p).symm z basis) := by
  have h := TopForms.coefficient_comp basis basis (inverseChartEquiv p z hz)
    (volumeForm J α ((extChartAt Model p).symm z)) (β ((extChartAt Model p).symm z))
    (volumeForm_ne_zero J α ht _)
  erw [inverseChartEquiv_coe] at h
  exact h.symm

lemma coordinateVolume_ne_zero (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    (ManifoldForms.pullback (volumeForm J α) (extChartAt Model p).symm z basis) ≠ 0 := by
  apply TopForms.eval_ne_zero basis
  have h := TopForms.comp_ne_zero (E := Space) (D := Space) (inverseChartEquiv p z hz)
    (volumeForm J α ((extChartAt Model p).symm z)) (volumeForm_ne_zero J α ht _)
  erw [inverseChartEquiv_coe] at h
  exact h

omit [IsManifold Model ∞ X] in
lemma scalar_smooth_of_charts {f : X → ℝ}
    (hf : ∀ p : X, ContDiffOn ℝ ∞ (f ∘ (extChartAt Model p).symm) (extChartAt Model p).target) :
    ContMDiff Model 𝓘(ℝ,ℝ) ∞ f := by
  intro x
  have h := ((hf x) ((extChartAt Model x) x)
    ((extChartAt Model x).map_source (mem_extChartAt_source x))).contDiffAt (extChartAt_target_mem_nhds x)
  have hc : ContMDiffAt Model 𝓘(ℝ,ℝ) ∞ (f ∘ (extChartAt Model x).symm) ((extChartAt Model x) x) :=
    contMDiffAt_iff_contDiffAt.mpr h
  apply (hc.comp x (contMDiffAt_extChartAt (n := ∞) (I := Model) (x := x))).congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source (I := Model) x).mem_nhds (mem_extChartAt_source x)] with y hy
  simp only [Function.comp_apply,(extChartAt Model x).left_inv hy]

lemma coefficient_smooth (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
    (ht : Tames α J) {β : ManifoldForms.Form X 4} (hβ : ManifoldForms.Smooth β) :
    ContMDiff Model 𝓘(ℝ,ℝ) ∞ (coefficient J α β) := by
  apply scalar_smooth_of_charts
  intro p
  have hn := (ContinuousAlternatingMap.apply ℝ Space ℝ basis).contDiff.comp_contDiffOn
    (ManifoldForms.smooth_chart β hβ p)
  have hd := (ContinuousAlternatingMap.apply ℝ Space ℝ basis).contDiff.comp_contDiffOn
    (ManifoldForms.smooth_chart _ (volumeForm_smooth J α hs) p)
  apply (hn.div hd (fun z hz => coordinateVolume_ne_zero J α ht p hz)).congr
  intro z hz
  exact coefficient_chart J α ht β p hz

lemma coordinateFundamental (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) (u v : Space) :
    ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm z ![u,v] =
      (coordinateMetric J α ht p z).bilinear (coordinateJ J p z u) v := by
  rw [← coordinateMetric_pullback J α ht p hz,coordinateJ_intertwine J p hz]
  change _ = associatedBilinear J (invariantPart J α) _ _ _
  rw [associatedBilinear_invariantPart_fundamental]
  change _ = invariantPart J α _ ![(inverseChartEquiv p z hz).toContinuousLinearMap u,
    (inverseChartEquiv p z hz).toContinuousLinearMap v]
  rw [inverseChartEquiv_coe]
  change (invariantPart J α _) ((mfderiv Model Model (extChartAt Model p).symm z) ∘ ![u,v]) = _
  congr 1
  ext i
  fin_cases i <;> rfl

lemma abs_coordinateVolume (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    |ManifoldForms.pullback (volumeForm J α) (extChartAt Model p).symm z basis| =
      ManifoldVolume.chartDensity J α p z := by
  rw [pullback_volumeForm]
  have he := VolumeNormalization.abs_volume_eq_density (coordinateMetric J α ht p z)
    (coordinateJ J p z) (coordinateJ_square J p hz) (coordinateMetric_hermitian J α ht p hz)
    (by simp [Space]) (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm z)
    (coordinateFundamental J α ht p hz) basis
  rw [coordinateMetric_bilinear J α ht p hz,density_basis] at he
  exact he

lemma density_coefficient (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (β : ManifoldForms.Form X 4) (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    ManifoldVolume.chartDensity J α p z * coefficient J α β ((extChartAt Model p).symm z) =
      OrientationSign.sign (ManifoldForms.pullback (volumeForm J α) (extChartAt Model p).symm z basis) *
        ManifoldForms.pullback β (extChartAt Model p).symm z basis := by
  rw [coefficient_chart J α ht β p hz,← abs_coordinateVolume J α ht p hz]
  exact OrientationSign.abs_mul_div _ _ (coordinateVolume_ne_zero J α ht p hz)

end TamingCompatibility.ManifoldTop

end

end OAI
