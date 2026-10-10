import OAI.Geometry.Perimeter.Regularity.ActualFiberMoments
import OAI.Geometry.Perimeter.Regularity.FiberLocalization
import OAI.Geometry.Perimeter.Regularity.PlaneWindowLift

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace ContDiff
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n m : ℕ} {v : Euc n}

theorem planeHeight_tsupport_gradient_subset (ψ : Euc m → ℝ) : tsupport (gradient ψ) ⊆ tsupport ψ := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hh
  exact hx (by simp only [gradient,fderiv_of_notMem_tsupport ℝ hh,map_zero])

def chartLaplacianTest (e : Euc m ≃ₗᵢ[ℝ] normalPlane v) (ψ : Euc m → ℝ)
    (y : normalPlane v) : ℝ := divergence (gradient ψ) (e.symm y)

theorem chartLaplacianTest_continuous (e : Euc m ≃ₗᵢ[ℝ] normalPlane v)
    {ψ : Euc m → ℝ} (hψ : ContDiff ℝ ∞ ψ) : Continuous (chartLaplacianTest e ψ) :=
  (continuous_divergence (gradient_contDiff hψ)).comp e.symm.continuous

theorem chartLaplacianTest_hasCompactSupport (e : Euc m ≃ₗᵢ[ℝ] normalPlane v)
    {ψ : Euc m → ℝ} (hcψ : HasCompactSupport ψ) : HasCompactSupport (chartLaplacianTest e ψ) := by
  have h : HasCompactSupport (divergence (gradient ψ)) :=
    hcψ.of_isClosed_subset (isClosed_tsupport _)
      ((tsupport_divergence_subset _).trans (planeHeight_tsupport_gradient_subset ψ))
  exact h.comp_homeomorph e.symm.toHomeomorph

theorem minimizing_chart_height_residual (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (hv : ‖v‖=1) (e : Euc m ≃ₗᵢ[ℝ] normalPlane v)
    {η : Euc n → ℝ} {a b δ b₀ R : ℝ}
    (ha : 0<a) (hδ : 0<δ) (hab : a+δ<b) (hab₀ : a<b₀) (hR : 0<R)
    (hηs : Function.support η ⊆ Metric.ball 0 R)
    {ψ : Euc m → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχone : ∀ s : ℝ, |s|<b₀ → χ s=1)
    (hηone : ∀ y ∈ tsupport (chartLaplacianTest e ψ), ∀ s : ℝ, |s|≤b →
      η ((y:Euc n)+s•v)=1)
    (hKR : ∀ y ∈ tsupport (chartLaplacianTest e ψ), ‖y‖+b+δ≤R)
    (hs : tsupport (planeWindowLift e ψ χ) ⊆ Metric.ball 0 R)
    {M K : ℝ} (hM : ∀ y, ‖divergence (gradient ψ) y‖≤M) (hK : 0≤K)
    (hd : ∀ x ∈ Metric.ball 0 R, ‖fderiv ℝ (gradient (planeWindowLift e ψ χ)) x‖≤K)
    (hh : ∀ x ∈ perimeterSupport E ∩ Metric.ball 0 R, |inner ℝ v x|≤a)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x ∈ E ↔ inner ℝ v x<0)) :
    |∫ y, chartFiber v e a (cutoffPhaseError E v η) y * divergence (gradient ψ) y| ≤
      2*K*(Real.sqrt (orientedTilt E v (Metric.ball 0 R))*
        Real.sqrt ((perimeter E (Metric.ball 0 R)).toReal)) +
      (M*b/(2*a))*orientedTilt E v (Metric.ball 0 R) := by
  let φ := chartLaplacianTest e ψ
  have hcφ := chartLaplacianTest_hasCompactSupport e hcψ
  have hm := actual_fiber_first_moment_error hn hmin hv
    (chartLaplacianTest_continuous e hψ) hcφ (fun y ↦ hM (e.symm y))
    ha.le hδ hab hR hKR hh hphase
  have he := chartFiber_test_eq_exact (A := a) hmin.1 hv e ha.le
    (by linarith : a<b) hηs φ hηone hphase
  have hj : (∫ x in Metric.ball 0 R, normalWindowTest v φ b 1 x ∂perimeterMeasure E) =
      ∫ x in Metric.ball 0 R, (inner ℝ v x-0)*
        planarDivergence v (gradient (planeWindowLift e ψ χ)) x ∂perimeterMeasure E := by
    apply integral_congr_ae
    have hsup : ∀ᵐ x ∂perimeterMeasure E, x ∈ perimeterSupport E := by
      rw [← perimeterMeasure_support]; exact (perimeterMeasure E).support_mem_ae
    filter_upwards [ae_restrict_of_ae hsup,ae_restrict_mem measurableSet_ball] with x hx hxB
    have hxH := hh x ⟨hx,hxB⟩
    have hxb : |inner ℝ v x|≤b := hxH.trans (by linarith)
    rw [planeWindowLift_laplacian e hψ hχone (hxH.trans_lt hab₀)]
    unfold normalWindowTest
    rw [Set.indicator_of_mem (show x ∈ {z : Euc n | |inner ℝ v z|≤b} from hxb)]
    simp only [sub_zero,pow_one,φ,chartLaplacianTest,chartProjection,ContinuousLinearMap.comp_apply]
    exact mul_comm _ _
  have hr := minimizing_height_planar_residual hn hmin (0:Euc n) hR hv 0
    (planeWindowLift_contDiff e hψ hχ) (planeWindowLift_hasCompactSupport hv e hcψ hcχ)
    hs ha.le hK (by simpa only [sub_zero] using hh) hd
  have hI : |∫ y in tsupport φ, φ y*exactFiberHeight E v b y| ≤
      2*a*K*(Real.sqrt (orientedTilt E v (Metric.ball 0 R))*
        Real.sqrt ((perimeter E (Metric.ball 0 R)).toReal)) +
      (M*b/2)*orientedTilt E v (Metric.ball 0 R) := by
    have ht := abs_sub_le (∫ y in tsupport φ, φ y*exactFiberHeight E v b y)
      (∫ x in Metric.ball 0 R, normalWindowTest v φ b 1 x ∂perimeterMeasure E) 0
    rw [sub_zero,sub_zero,abs_sub_comm] at ht
    rw [hj] at hm ht
    linarith
  have he' : (∫ y, chartFiber v e a (cutoffPhaseError E v η) y * divergence (gradient ψ) y) =
      a⁻¹ * ∫ y in tsupport φ, φ y*exactFiberHeight E v b y := by
    simpa only [φ,chartLaplacianTest,e.symm_apply_apply] using he
  rw [he',abs_mul,abs_inv,abs_of_pos ha]
  apply (mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr ha.le)).trans_eq
  field_simp

end RPISingularHarnack

end

end OAI
