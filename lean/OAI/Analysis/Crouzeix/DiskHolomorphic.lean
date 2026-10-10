import Mathlib
import OAI.Analysis.Crouzeix.CauchyProjection
import OAI.Analysis.Crouzeix.HilbertExtension

namespace OAI

/-! Disk Holomorphic. -/

noncomputable section

open MeasureTheory Set Filter

open scoped Topology TensorProduct Matrix.Norms.L2Operator

namespace CrouzeixHilbert

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance diskHolomorphicOperatorRealNormedSpace (size : ℕ) :
    NormedSpace ℝ (Operator (Amplification H size)) :=
  NormedSpace.restrictScalars ℝ ℂ _

section DensityIntegral

variable {α : Type v} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [CompactSpace α] (μ : Measure α) [IsFiniteMeasure μ]

def densityIntegralCLM (Λ : C(α, Operator H)) (m : ℕ) :
    C(α, Coeff m) →L[ℂ] Operator (Amplification H m) := by
  let : Module ℝ (Operator (Amplification H m)) :=
    (diskHolomorphicOperatorRealNormedSpace m).toModule
  let : SMulCommClass ℝ ℂ (Operator (Amplification H m)) :=
    IsScalarTower.to_smulCommClass
  have hc (F : C(α, Coeff m)) :
      Continuous (fun t => tensorOperator (Λ t) (F t)) :=
    ((tensorBilinearCLM m).continuous.comp Λ.continuous).clm_apply F.continuous
  have hi (F : C(α, Coeff m)) :
      Integrable (fun t => tensorOperator (Λ t) (F t)) μ :=
    (hc F).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let L : C(α, Coeff m) →ₗ[ℂ] Operator (Amplification H m) := {
    toFun F := ∫ t, tensorOperator (Λ t) (F t) ∂μ
    map_add' F G := by
      simp only [ContinuousMap.add_apply, ← tensorCoefficientCLM_apply, map_add]
      exact integral_add (hi F) (hi G)
    map_smul' c F := by
      simp only [ContinuousMap.smul_apply, ← tensorCoefficientCLM_apply, map_smul,
        integral_smul, RingHom.id_apply] }
  refine L.mkContinuous (‖Λ‖ * μ.real univ) fun F => ?_
  have hb : ∀ᵐ t ∂μ, ‖tensorOperator (Λ t) (F t)‖ ≤ ‖Λ‖ * ‖F‖ :=
    Eventually.of_forall fun t => (norm_tensorOperator_le _ _).trans
      (mul_le_mul (Λ.norm_coe_le_norm t) (F.norm_coe_le_norm t)
        (norm_nonneg _) (norm_nonneg _))
  exact (norm_integral_le_of_norm_le_const hb).trans_eq (by ring)

@[simp] theorem densityIntegralCLM_apply (Λ : C(α, Operator H)) {m : ℕ}
    (F : C(α, Coeff m)) :
    densityIntegralCLM μ Λ m F = ∫ t, tensorOperator (Λ t) (F t) ∂μ := rfl

end DensityIntegral

namespace Disk

local instance diskHolomorphicFactZeroLtOne : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

theorem integral_matrixHolomorphic (D : Operator H) (hN : ‖D‖ ≤ 1)
    (hD : spectralRadius ℂ D < 1) {m : ℕ} {U : Set ℂ} {F : ℂ → Coeff m}
    (hU : IsOpen U) (hKU : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (hF : EntrywiseHolomorphic U F) :
    (∫ t : CircleSpace, tensorOperator (phi D t) (F (fourier 1 t)) ∂σ) =
      matrixHolomorphicEval D U F := by
  let K : Set ℂ := Metric.closedBall 0 1
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKc : Convex ℝ K := convex_closedBall _ _
  have hKn : K.Nonempty := ⟨0, by simp [K]⟩
  have hDK : numericalClosure D ⊆ K :=
    (numericalClosure_subset_closedBall D).trans (Metric.closedBall_subset_closedBall hN)
  obtain ⟨ε, hε, hεU⟩ := hK.exists_cthickening_subset_open hU hKU
  let L := Metric.cthickening ε K
  have hKL : K ⊆ interior L :=
    (Metric.self_subset_thickening hε _).trans (Metric.thickening_subset_interior_cthickening _ _)
  obtain ⟨Γ⟩ := exists_calculusContour hK hKc hKn isOpen_interior hKL
  let Δ : CalculusContour (numericalClosure D) U := {
    toSmoothContour := Γ.toSmoothContour
    avoids := fun t ht => ⟨hεU (interior_subset (Γ.avoids t ht).1),
      fun hz => (Γ.avoids t ht).2 (hDK hz)⟩
    index_inside := fun z hz => Γ.index_inside z (hDK hz)
    index_outside := fun z hz => Γ.index_outside z
      (fun he => hz (hεU (interior_subset he))) }
  obtain ⟨degrees, B, happ⟩ := exists_matrixPolynomial_tendstoUniformlyOn
    (show IsCompact L from hK.cthickening) (hKc.cthickening ε) hU hεU hF
  have ht : Δ.toSmoothContour.trace ⊆ L := by
    rintro z ⟨t, ht, rfl⟩
    exact interior_subset (Γ.avoids t ht).1
  have heval : Tendsto (fun n => polynomialEval D (B n)) atTop
      (𝓝 (matrixHolomorphicEval D U F)) := by
    have h := tendsto_matrixContourEval D Δ
      (fun n => (continuous_matrixPolynomial (B n)).continuousOn) (happ.mono ht)
    simp_rw [matrixContourEval_matrixPolynomial] at h
    have he : matrixContourEval D Δ.toSmoothContour F = matrixHolomorphicEval D U F := by
      unfold matrixContourEval matrixHolomorphicEval
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [holomorphicEval_eq_contourEval D hU (hF i j) Δ]
    rwa [he] at h
  have hcircle (t : CircleSpace) : fourier 1 t ∈ K := by
    simpa only [K, Metric.mem_closedBall, dist_zero_right, norm_fourier] using (le_refl (1 : ℝ))
  let F₀ : C(CircleSpace, Coeff m) :=
    ⟨fun t => F (fourier 1 t), hF.continuousOn.comp_continuous (fourier 1).continuous
      (fun t => hKU (hcircle t))⟩
  let Fn (n : ℕ) : C(CircleSpace, Coeff m) :=
    ⟨fun t => matrixPolynomial (B n) (fourier 1 t),
      (continuous_matrixPolynomial (B n)).comp (fourier 1).continuous⟩
  have hFns : Tendsto Fn atTop (𝓝 F₀) := by
    rw [ContinuousMap.tendsto_iff_tendstoUniformly]
    apply Metric.tendstoUniformly_iff.mpr
    intro δ hδ
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp happ δ hδ] with n hn t
    exact hn _ (interior_subset (hKL (hcircle t)))
  let Λ : C(CircleSpace, Operator H) := ⟨phi D, continuous_phi D hD⟩
  have hi := (densityIntegralCLM σ Λ m).continuous.tendsto F₀ |>.comp hFns
  simp only [Function.comp_def, densityIntegralCLM_apply, Fn, Λ, ContinuousMap.coe_mk,
    integral_matrixPolynomial D hD] at hi
  let : MetricSpace (Operator (Amplification H m)) :=
    ContinuousLinearMap.toNormedAddCommGroup.toMetricSpace
  let : T0Space (Operator (Amplification H m)) := MetricSpace.instT0Space
  let : RegularSpace (Operator (Amplification H m)) := UniformSpace.to_regularSpace
  let : T2Space (Operator (Amplification H m)) :=
    R1Space.t2Space_iff_t0Space.mpr inferInstance
  exact tendsto_nhds_unique hi heval

theorem holomorphic_bound_spectralRadius_lt_one (D : Operator H) (hN : ‖D‖ ≤ 1)
    (hD : spectralRadius ℂ D < 1) {m : ℕ} {U : Set ℂ} {F : ℂ → Coeff m}
    (hU : IsOpen U) (hKU : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (hF : EntrywiseHolomorphic U F) :
    ‖matrixHolomorphicEval D U F‖ ≤ supNorm (Metric.sphere (0 : ℂ) 1) F := by
  let Λ : C(CircleSpace, Operator H) := ⟨phi D, continuous_phi D hD⟩
  have hΛ : ∀ t, 0 ≤ Λ t := fun t =>
    ContinuousLinearMap.nonneg_iff_isPositive.mpr (phi_isPositive D hN hD t)
  have hcircle (t : CircleSpace) : fourier 1 t ∈ Metric.sphere (0 : ℂ) 1 := by
    simp only [Metric.mem_sphere, dist_zero_right, norm_fourier]
  let F₀ : C(CircleSpace, Coeff m) :=
    ⟨fun t => F (fourier 1 t), hF.continuousOn.comp_continuous (fourier 1).continuous
      (fun t => hKU (Metric.sphere_subset_closedBall (hcircle t)))⟩
  have hb := supNorm_bddAbove (isCompact_sphere (0 : ℂ) 1)
    (hF.continuousOn.mono (Metric.sphere_subset_closedBall.trans hKU))
  rw [← integral_matrixHolomorphic D hN hD hU hKU hF]
  exact norm_integral_tensor_density_le Λ hΛ (integral_phi D hD) F₀ _
    (supNorm_nonneg hb) (fun t => norm_le_supNorm hb (hcircle t))

end Disk

end CrouzeixHilbert

end

end OAI
