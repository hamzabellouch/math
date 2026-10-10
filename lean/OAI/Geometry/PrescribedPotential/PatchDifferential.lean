import Mathlib
import OAI.Geometry.PrescribedPotential.ComplexOperator
import OAI.Geometry.PrescribedPotential.CoreBounds
import OAI.Geometry.PrescribedPotential.GlobalParametrix
import OAI.Geometry.PrescribedPotential.ParameterSchwartz
import OAI.Geometry.PrescribedPotential.ParametrixCommutator

namespace OAI

/-! Patch Differential. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap ContDiff Classical ComplexOrder MatrixOrder BoundedContinuousFunction

namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma schwartz_temperate_product_distribution {a : E → ℂ}
    (ha : a.HasTemperateGrowth) (f : 𝓢(E, ℂ)) :
    SchwartzMap.toTemperedDistributionCLM E ℂ volume (SchwartzMap.smulLeftCLM ℂ a f) =
      smulLeftCLM ℂ a (f : 𝓢'(E, ℂ)) := by
  ext φ
  simp only [SchwartzMap.toTemperedDistributionCLM_apply_apply,
    smulLeftCLM_apply_apply, SchwartzMap.smulLeftCLM_apply_apply ha, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma schwartz_second_deriv (f : 𝓢(E, ℂ)) (v w x : E) :
    (∂_{v} (∂_{w} f)) x = fderiv ℝ (fderiv ℝ f) x v w := by
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (fun y => fderiv ℝ f y w) x v = _
  exact PotentialKaehler.fderiv_eval_derivative
    f.smooth'.contDiffAt v w
end SobolevChart

namespace MetricLocalization
open EllipticKernel FrozenPoisson SobolevChart
variable {n : ℕ}

def schwartzDifferential (c : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ) :
    𝓢(EC n, ℂ) →L[ℂ] 𝓢(EC n, ℂ) :=
  ∑ k, ∑ l, SchwartzMap.smulLeftCLM ℂ (c k l) ∘L
    lineDerivOpCLM ℂ 𝓢(EC n, ℂ) (stdOrthonormalBasis ℝ (EC n) k) ∘L
    lineDerivOpCLM ℂ 𝓢(EC n, ℂ) (stdOrthonormalBasis ℝ (EC n) l)

lemma schwartzDifferential_apply
    (c : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
    (hc : ∀ k l, (c k l : EC n → ℂ).HasTemperateGrowth)
    (f : 𝓢(EC n, ℂ)) (x : EC n) :
    schwartzDifferential c f x = ∑ k, ∑ l, c k l x *
      fderiv ℝ (fderiv ℝ f) x (stdOrthonormalBasis ℝ (EC n) k)
        (stdOrthonormalBasis ℝ (EC n) l) := by
  simp only [schwartzDifferential, _root_.sum_apply,
    ContinuousLinearMap.comp_apply, lineDerivOpCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply (hc _ _), smul_eq_mul, schwartz_second_deriv]

lemma schwartzDifferential_distribution
    (c : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
    (hc : ∀ k l, (c k l : EC n → ℂ).HasTemperateGrowth) (f : 𝓢(EC n, ℂ)) :
    SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume (schwartzDifferential c f) =
      chartDifferential c (SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume f) := by
  simp only [schwartzDifferential, chartDifferential, map_sum,
    _root_.sum_apply, ContinuousLinearMap.comp_apply, lineDerivOpCLM_apply]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [schwartz_temperate_product_distribution (hc k l),
    ← lineDerivOp_toTemperedDistributionCLM_eq, ← lineDerivOp_toTemperedDistributionCLM_eq]

lemma schwartzDifferential_tsupport
    (c : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ) (f : 𝓢(EC n, ℂ)) :
    tsupport (schwartzDifferential c f : EC n → ℂ) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  apply hx
  simp only [schwartzDifferential, _root_.sum_apply,
    ContinuousLinearMap.comp_apply, lineDerivOpCLM_apply]
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro l _
  apply image_eq_zero_of_notMem_tsupport
  intro hl
  exact hn (SchwartzMap.tsupport_lineDerivOp_subset _ _
    (SchwartzMap.tsupport_lineDerivOp_subset _ _
      (SchwartzMap.tsupport_smulLeftCLM_subset _ _ hl).1))

 
def schwartzCutoffError (c : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
    (κ : 𝓢(EC n, ℂ)) : 𝓢(EC n, ℂ) →L[ℂ] 𝓢(EC n, ℂ) :=
  (schwartzDifferential c).comp (SchwartzMap.smulLeftCLM ℂ κ) -
    (SchwartzMap.smulLeftCLM ℂ κ).comp (schwartzDifferential c)

lemma schwartzCutoffError_distribution
    (c : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
    (hc : ∀ k l, (c k l : EC n → ℂ).HasTemperateGrowth)
    (κ f : 𝓢(EC n, ℂ)) :
    SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume (schwartzCutoffError c κ f) =
      chartDifferential c (smulLeftCLM ℂ κ (SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume f)) -
        smulLeftCLM ℂ κ (chartDifferential c (SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume f)) := by
  simp only [schwartzCutoffError, _root_.sub_apply, ContinuousLinearMap.comp_apply,
    map_sub, schwartzDifferential_distribution c hc,
    schwartz_temperate_product_distribution κ.hasTemperateGrowth]

lemma schwartzCutoffError_tsupport
    (c : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ) (κ f : 𝓢(EC n, ℂ)) :
    tsupport (schwartzCutoffError c κ f : EC n → ℂ) ⊆ tsupport κ := by
  change tsupport (fun x => schwartzDifferential c (SchwartzMap.smulLeftCLM ℂ κ f) x -
    SchwartzMap.smulLeftCLM ℂ κ (schwartzDifferential c f) x) ⊆ _
  apply (tsupport_binop_subset (fun a b : ℂ => a - b) (sub_self 0) _ _).trans
  apply union_subset
  · exact (schwartzDifferential_tsupport c _).trans
      ((SchwartzMap.tsupport_smulLeftCLM_subset _ _).trans inter_subset_right)
  · exact (SchwartzMap.tsupport_smulLeftCLM_subset _ _).trans inter_subset_right

end MetricLocalization

namespace Anticanonical.SourceSmooth.ParametrixPatch
open EllipticKernel SobolevChart FrozenPoisson ParameterRegularity MetricLocalization
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
  {g : KaehlerMetric A}

abbrev coefficients (p : ParametrixPatch g) := extendedCoefficient p.matrix (coefficientBCF p.coefficient)

lemma coefficients_temperate (p : ParametrixPatch g) (k l : BasisIndex d) :
    (p.coefficients k l : EC d → ℂ).HasTemperateGrowth :=
  extendedCoefficient_temperate p.matrix _ (fun k l => (p.coefficient k l).hasTemperateGrowth) k l

def differential (p : ParametrixPatch g) := schwartzDifferential p.coefficients

def cutoffError (p : ParametrixPatch g) (κ : 𝓢(EC d, ℂ)) :=
  schwartzCutoffError p.coefficients κ

lemma differential_local (p : ParametrixPatch g) (f : 𝓢(EC d, ℂ))
    {y : EC d} (hy : y ∈ p.domain) :
    p.differential f y = GlobalElliptic.localL g p.index f y := by
  rw [differential, schwartzDifferential_apply _ p.coefficients_temperate]
  unfold GlobalElliptic.localL
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [p.equals y hy k l]

lemma localInverse_distribution (p : ParametrixPatch g) (m : ℝ) (hm : 1 ≤ m)
    (f : 𝓢(EC d, ℂ)) :
    SchwartzMap.toTemperedDistributionCLM (EC d) ℂ volume (p.localInverse m hm f) =
      realize 2 (parameterLocal p.matrix p.positive m hm (stdOrthonormalBasis ℝ (EC d))
        (coefficientBCF p.coefficient) p.small (schwartzCoord 0 f)) :=
  schwartzLocalValue_distribution p.matrix p.positive m hm (stdOrthonormalBasis ℝ (EC d))
    p.coefficient p.small f

lemma localInverse_equation (p : ParametrixPatch g) (m : ℝ) (hm : 1 ≤ m)
    (f : 𝓢(EC d, ℂ)) :
    (m^2 : ℂ) • p.localInverse m hm f - p.differential (p.localInverse m hm f) = f := by
  apply schwartz_distribution_injective
  simp only [map_sub, map_smul, differential, schwartzDifferential_distribution _ p.coefficients_temperate,
    localInverse_distribution]
  rw [chartDifferential_extension p.matrix _ (fun k l => (p.coefficient k l).hasTemperateGrowth)]
  rw [sub_add_eq_sub_sub, parameterLocal_equation]
  have h := realize_schwartzCoord (0 : ℝ) f
  simpa only [realize, neg_zero, besselPotential_zero, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, Lp.toTemperedDistributionCLM_apply] using h

lemma cutoffError_coord (p : ParametrixPatch g) (m : ℝ) (hm : 1 ≤ m)
    (κ f : 𝓢(EC d, ℂ)) :
    schwartzCoord 0 (p.cutoffError κ (p.localInverse m hm f)) =
      parameterCutoffError p.matrix p.positive m hm (coefficientBCF p.coefficient) p.small κ
        (schwartzCoord 0 f) := by
  apply l2_injective
  simp only [Lp.toTemperedDistributionCLM_apply]
  rw [schwartzCoord_distribution, besselPotential_zero, ContinuousLinearMap.id_apply]
  rw [cutoffError, schwartzCutoffError_distribution _ p.coefficients_temperate,
    localInverse_distribution, parameterCutoffError_distribution _ _ _ _ _
      (fun k l => (p.coefficient k l).hasTemperateGrowth)]

lemma cutoffError_bound (p : ParametrixPatch g) (m : ℝ) (hm : 1 ≤ m)
    (κ f : 𝓢(EC d, ℂ)) :
    ‖schwartzCoord 0 (p.cutoffError κ (p.localInverse m hm f))‖ ≤
      cutoffErrorConstant p.matrix p.positive (coefficientBCF p.coefficient) κ / m *
        ‖schwartzCoord 0 f‖ := by
  rw [cutoffError_coord]
  exact parameterCutoffError_bound p.matrix p.positive m hm _ p.small κ _

end Anticanonical.SourceSmooth.ParametrixPatch

end
end

end OAI
