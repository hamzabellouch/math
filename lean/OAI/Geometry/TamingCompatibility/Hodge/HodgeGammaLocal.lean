import Mathlib
import OAI.Geometry.TamingCompatibility.HeatFlow.ResolventGammaScalar
import OAI.Geometry.TamingCompatibility.Hodge.HodgeStarNormalGauge
import OAI.Geometry.TamingCompatibility.Hodge.HodgeParametrixPatch
import OAI.Geometry.TamingCompatibility.Hodge.HodgeKernelGammaBounds

namespace OAI

noncomputable section

section

namespace TamingCompatibility.GeometricHilbert.HodgeKernelBounds
open Set MeasureTheory

lemma flat_gamma_integrand {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z : FlatHeat.V) :
    hodgeGammaWeight s * FlatHeat.heat (r^2*s) z =
      (4*Real.pi)⁻¹^2 * (r⁻¹)^4 * profile 3 (1/4) (‖z‖/r) s := by
  have hexp : -‖z‖^2/(4*(r^2*s)) = -(1/4 : ℝ)*(‖z‖/r)^2/s := by ring
  unfold hodgeGammaWeight FlatHeat.heat profile
  rw [hexp]
  have hcoef : s^5*(4*Real.pi*(r^2*s))⁻¹^2 = (4*Real.pi)⁻¹^2*(r⁻¹)^4*s^3 := by
    field_simp [Real.pi_ne_zero,hr.ne',hs.ne']
  calc
    _ = (s^5*(4*Real.pi*(r^2*s))⁻¹^2)*Real.exp (-s)*Real.exp (-(1/4 : ℝ)*(‖z‖/r)^2/s) := by ring
    _ = _ := by rw [hcoef]; ring

lemma flat_gamma_integral {r : ℝ} (hr : 0 < r) (T : ℝ) (z : FlatHeat.V) :
    (1/120 : ℝ) * (∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s * FlatHeat.heat (r^2*s) z) =
      leading r T ‖z‖ := by
  have he : (∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s * FlatHeat.heat (r^2*s) z) =
      ((4*Real.pi)⁻¹^2*(r⁻¹)^4) * truncatedProfile 3 (1/4) (‖z‖/r) (T/r^2) := by
    unfold truncatedProfile
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact flat_gamma_integrand hr hs.1 z
  rw [he]
  unfold leading
  ring

end TamingCompatibility.GeometricHilbert.HodgeKernelBounds

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge HodgeNormalSymbol NormalJets NormalMetricCalculus Set MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

lemma leadingCoordinate_gamma {r : ℝ} (hr : 0 < r) (T : ℝ) (ψ χ : Space → ℝ) (q z : Space) :
    (1/120 : ℝ) • (∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s •
      leadingCoordinate J α ht p D g B ψ χ (r^2*s) (q,z)) =
      (ψ q*χ z*HodgeKernelBounds.leading r T ‖z‖) • normalGauge J α ht p D g B (q,z) := by
  have operatorComplete (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [CompleteSpace E] : CompleteSpace (E →L[ℝ] E) := inferInstance
  let : CompleteSpace (W →L[ℝ] W) := operatorComplete W
  simp only [leadingCoordinate,smul_smul]
  have he (s : ℝ) : hodgeGammaWeight s*(ψ q*χ z*FlatHeat.heat (r^2*s) z) =
      (ψ q*χ z)*(hodgeGammaWeight s*FlatHeat.heat (r^2*s) z) := by ring
  simp_rw [he]
  rw [integral_smul_const,integral_const_mul,smul_smul]
  rw [show (1/120 : ℝ)*((ψ q*χ z)*(∫ s : ℝ in Ioc 0 (T/r^2),
      hodgeGammaWeight s*FlatHeat.heat (r^2*s) z)) =
      (ψ q*χ z)*((1/120 : ℝ)*(∫ s : ℝ in Ioc 0 (T/r^2),
      hodgeGammaWeight s*FlatHeat.heat (r^2*s) z)) by ring]
  rw [HodgeKernelBounds.flat_gamma_integral hr]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end

namespace TamingCompatibility.GeometricHilbert.HodgeKernelBounds

lemma leading_quadratic_upper (N : ℕ) {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) (T : ℝ) :
    d^2 * leading r T d ≤ leadingConstant (N+2)*(r⁻¹)^2/(1+d/r)^N := by
  have hb : 0 < 1+d/r := by positivity
  have hsq : d^2*(r⁻¹)^4 ≤ (1+d/r)^2*(r⁻¹)^2 := by
    have h : (d/r)^2 ≤ (1+d/r)^2 := by nlinarith [div_nonneg hd hr.le]
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg r⁻¹)
    calc
      d^2*(r⁻¹)^4 = (d/r)^2*(r⁻¹)^2 := by ring
      _ ≤ _ := hm
  have hc := (leadingConstant_pos (N+2)).le
  calc
    _ ≤ d^2*(leadingConstant (N+2)*(r⁻¹)^4/(1+d/r)^(N+2)) :=
      mul_le_mul_of_nonneg_left (leading_upper (N+2) hr hd T) (sq_nonneg d)
    _ = leadingConstant (N+2)*(d^2*(r⁻¹)^4)/(1+d/r)^(N+2) := by ring
    _ ≤ leadingConstant (N+2)*((1+d/r)^2*(r⁻¹)^2)/(1+d/r)^(N+2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hc) (pow_nonneg hb.le _)
    _ = _ := by rw [pow_add]; field_simp [hb.ne']

end TamingCompatibility.GeometricHilbert.HodgeKernelBounds

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge HodgeNormalSymbol NormalJets NormalMetricCalculus Set MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

lemma leadingCoordinate_gamma_angular (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (K : Set Space) (hK : IsCompact K) (hactual : ∀ q ∈ K, ActualData J α ht p D q g B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ radius : ℝ, 0 < radius ∧
      ∀ N : ℕ, ∀ r : ℝ, 0 < r → ∀ T : ℝ, ∀ ψ χ : Space → ℝ,
      ∀ q ∈ K, ∀ z : Space, ‖z‖ ≤ radius →
      0 ≤ ψ q*χ z → ψ q*χ z ≤ 1 →
      ∀ v w : Space, ‖v‖ = 1 → ‖w‖ = 1 →
      (1/2 : ℝ)*(ψ q*χ z*HodgeKernelBounds.leading r T ‖z‖)*
        ‖UnitaryFrame.line v-normalGauge J α ht p D g B (q,z) (UnitaryFrame.line w)‖^2 -
          (C*HodgeKernelBounds.leadingConstant (N+2))*(r⁻¹)^2/(1+‖z‖/r)^N ≤
        ⟪UnitaryFrame.line v,UnitaryFrame.star
          (((1/120 : ℝ) • (∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s •
            leadingCoordinate J α ht p D g B ψ χ (r^2*s) (q,z))) (UnitaryFrame.line w))⟫ := by
  obtain ⟨C,hC,ρ,hρ,hangular⟩ := compact_normalGauge_angular J α ht p D g B hs hg hB K hK hactual
  refine ⟨C,hC,ρ,hρ,?_⟩
  intro N r hr T ψ χ q hq z hz hp hp1 v w hv hw
  rw [leadingCoordinate_gamma J α ht p D g B hr]
  simp only [smul_apply,UnitaryFrame.star_smul,inner_smul_right]
  have hl := HodgeKernelBounds.leading_nonneg r T ‖z‖
  have ha := mul_le_mul_of_nonneg_left (hangular q hq z hz v w hv hw) (mul_nonneg hp hl)
  have he : (ψ q*χ z*HodgeKernelBounds.leading r T ‖z‖)*(C*‖z‖^2) ≤
      (C*HodgeKernelBounds.leadingConstant (N+2))*(r⁻¹)^2/(1+‖z‖/r)^N := by
    calc
      _ = C*((ψ q*χ z)*(‖z‖^2*HodgeKernelBounds.leading r T ‖z‖)) := by ring
      _ ≤ C*(‖z‖^2*HodgeKernelBounds.leading r T ‖z‖) :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (mul_nonneg (sq_nonneg _) hl) hp1) hC
      _ ≤ C*(HodgeKernelBounds.leadingConstant (N+2)*(r⁻¹)^2/(1+‖z‖/r)^N) :=
        mul_le_mul_of_nonneg_left (HodgeKernelBounds.leading_quadratic_upper N hr (norm_nonneg z) T) hC
      _ = _ := by ring
  nlinarith

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end

end OAI
