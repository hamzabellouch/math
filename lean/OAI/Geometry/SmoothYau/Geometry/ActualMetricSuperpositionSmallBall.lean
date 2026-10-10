import Mathlib
import OAI.Geometry.SmoothYau.Estimates.PhysicalFiniteSuperpositionSmallBall

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set Filter
open scoped Topology ContDiff
section CoordinateProfiles
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma coordinateMetricGradient_pairing (g : SmoothMetric E E) (φ : E → ℝ) (p v : E) :
    selfMetricFlat g p (coordinateMetricGradient g φ p) v = fderiv ℝ φ p v := by
  have h := (selfMetricFlat_invertible g p).inverse_apply_eq.mp
    (show (selfMetricFlat g p).inverse (fderiv ℝ φ p) = coordinateMetricGradient g φ p from rfl)
  exact congrArg (fun l : E →L[ℝ] ℝ => l v) h.symm
end CoordinateProfiles

lemma normalWaveProfile_gradient_pairing
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (q : NormalWaveParameter)
    (v : NormalWaveSpace) :
    inner ℝ (gradient (normalWaveProfile g φ q) 0) v = fderiv ℝ φ q.1 (q.2 v) := by
  rw [inner_gradient_left]
  exact normalJetMap_first_phase_jet q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)
    (fun v w => metricChristoffel_symm g q.1 (q.2 v) (q.2 w)) hφ v

lemma normalWaveProfile_hessian
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (q : NormalWaveParameter)
    (v w : NormalWaveSpace) :
    actualHessianForm (normalWaveProfile g φ q) v w =
      actualCoordinateHessian g φ q.1 (q.2 v) (q.2 w) := by
  exact metricNormal_second_phase_jet g q.1 q.2 hφ v w

lemma metric_frame_gradient
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) {K : Set NormalWaveSpace}
    {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K) :
    q.2 (gradient (normalWaveProfile g φ q) 0) = coordinateMetricGradient g φ q.1 := by
  obtain ⟨A,hA⟩ := metricFrameSet_equiv g hq
  apply (selfMetricFlat_invertible g q.1).injective
  ext w
  obtain ⟨v,rfl⟩ := A.surjective w
  have hAv : A v = q.2 v := congrArg (fun L : NormalWaveSpace →L[ℝ] NormalWaveSpace => L v) hA
  rw [hAv,hq.2,coordinateMetricGradient_pairing]
  exact normalWaveProfile_gradient_pairing g hφ q v

lemma actualProfileStrict_normal_direction
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) {K : Set NormalWaveSpace}
    {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K)
    (hs : actualProfileStrict g φ q.1) :
    ∃ b : PhaseSpace,
      inner ℝ (gradient (normalWaveProfile g φ q) 0) b = 0 ∧
      ‖b‖^2 = 1+‖gradient (normalWaveProfile g φ q) 0‖^2 ∧
      0 < actualHessianForm (normalWaveProfile g φ q) (gradient (normalWaveProfile g φ q) 0)
        (gradient (normalWaveProfile g φ q) 0)+actualHessianForm (normalWaveProfile g φ q) b b := by
  obtain ⟨A,hA⟩ := metricFrameSet_equiv g hq
  obtain ⟨v,hv,hav,hpos⟩ := hs
  let w := A.symm v
  let a := gradient (normalWaveProfile g φ q) 0
  let H := actualHessianForm (normalWaveProfile g φ q)
  have hAw : q.2 w = v := by rw [←hA]; exact A.apply_symm_apply v
  have hAa : q.2 a = coordinateMetricGradient g φ q.1 := metric_frame_gradient g hφ hq
  have hw : w ≠ 0 := by
    intro hw0
    have hv0 : v = 0 := by rw [←hAw,hw0,map_zero]
    rw [hv0,norm_zero] at hv
    norm_num at hv
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hwperp : inner ℝ a w = 0 := by
    rw [normalWaveProfile_gradient_pairing g hφ q w,hAw]
    simpa only [InnerProductSpace.toDual_symm_apply] using hav
  have hmetric (y : NormalWaveSpace) : selfMetricFlat g q.1 (q.2 y) (q.2 y) = ‖y‖^2 := by
    rw [hq.2,real_inner_self_eq_norm_sq]
  have htrace : 0 < ‖w‖^2*H a a+(1+‖a‖^2)*H w w := by
    change 0 < metricProfileTraceForm _ _ _ v v at hpos
    rw [metricProfileTraceForm_apply,←hAw,←hAa,hmetric,hmetric] at hpos
    simpa only [←normalWaveProfile_hessian g hφ q] using hpos
  let L := Real.sqrt (1+‖a‖^2)
  have hL0 : 0 < L := Real.sqrt_pos.mpr (by positivity)
  have hLsq : L^2 = 1+‖a‖^2 := Real.sq_sqrt (by positivity)
  let b := (L/‖w‖) • w
  have hbsq : ‖b‖^2 = 1+‖a‖^2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hL0 hwn),mul_pow,div_pow]
    field_simp
    exact hLsq
  refine ⟨b,?_,hbsq,?_⟩
  · change inner ℝ a ((L/‖w‖) • w) = 0
    rw [inner_smul_right,hwperp,mul_zero]
  · have hbH : H b b = (L/‖w‖)^2*H w w := by
      dsimp only [b]
      rw [show H ((L/‖w‖) • w) = (L/‖w‖) • H w from H.map_smul _ _]
      change (L/‖w‖)*(H w ((L/‖w‖) • w)) = _
      rw [(H w).map_smul]
      change (L/‖w‖)*((L/‖w‖)*H w w) = _
      ring
    have heq : ‖w‖^2*(H a a+H b b) = ‖w‖^2*H a a+(1+‖a‖^2)*H w w := by
      rw [hbH,div_pow]
      field_simp
      rw [hLsq]
      ring
    change 0 < H a a+H b b
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hwn)).mp (heq.symm ▸ htrace)

lemma actualCriticalPlane_normal
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) {K : Set NormalWaveSpace}
    {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K)
    (hc : ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ q.1 v v) :
    ∃ P : Submodule ℝ PhaseSpace, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, v ≠ 0 → 0 < actualHessianForm (normalWaveProfile g φ q) v v := by
  obtain ⟨A,hA⟩ := metricFrameSet_equiv g hq
  obtain ⟨P,hP,hpos⟩ := hc
  refine ⟨P.map A.symm.toLinearEquiv.toLinearMap,?_,?_⟩
  · exact (A.symm.toLinearEquiv.finrank_map_eq P).trans hP
  · intro v hv hv0
    obtain ⟨w,hw,rfl⟩ := hv
    rw [normalWaveProfile_hessian g hφ q,←hA]
    change 0 < actualCoordinateHessian g φ q.1 (A (A.symm w)) (A (A.symm w))
    rw [A.apply_symm_apply]
    exact hpos w hw (by intro h; apply hv0; simp [h])
end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set Filter
open scoped Topology ContDiff
lemma normalWaveProfile_gradient_zero_iff
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) {K : Set NormalWaveSpace}
    {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K) :
    gradient (normalWaveProfile g φ q) 0 = 0 ↔ fderiv ℝ φ q.1 = 0 := by
  obtain ⟨A,hA⟩ := metricFrameSet_equiv g hq
  constructor
  · intro ha
    ext v
    obtain ⟨w,rfl⟩ := A.surjective v
    have h := normalWaveProfile_gradient_pairing g hφ q w
    rw [ha,inner_zero_left] at h
    have hv : A w = q.2 w := congrArg (fun L : NormalWaveSpace →L[ℝ] NormalWaveSpace => L w) hA
    simpa only [hv,_root_.zero_apply] using h.symm
  · intro h
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [normalWaveProfile_gradient_pairing g hφ q,h,_root_.zero_apply]
end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

theorem actual_metric_superposition_smallBall
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    (hnc : ∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x)
    (hcrit : ∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v)
    (m D : ℕ) :
    ∃ ρ > 0, ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Metric.ball 0 ρ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
    ∃ T > 0, ∃ C > 0, ∃ r₀ > 0, ∃ N : ℝ, 1 ≤ N ∧
      ∀ n : ℝ, N ≤ n →
      ∃ U : metricFrameSet g K → Fin 3 → NormalWaveSpace → ℂ,
        (∀ q ℓ, ContDiff ℝ ∞ (U q ℓ) ∧ HasCompactSupport (U q ℓ) ∧
          U q ℓ q.1.1 = Complex.exp ((n : ℂ)*(φ q.1.1 : ℂ)) ∧
          ∀ y : NormalWaveSpace, ∀ k ≤ m,
            ‖iteratedFDeriv ℝ k (U q ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y) ∧
            ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U q ℓ) w +
              (n : ℂ)*((n : ℂ)+2)*U q ℓ w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
        ∀ (I : Type) [Fintype I] (p : I → metricFrameSet g K)
          (w : NormalWaveSpace → ℝ), ContDiff ℝ ∞ w → ∀ i₀ : I,
        ∀ x : Fin 3 → ℝ, ‖x‖ < r₀ → ‖x‖ ≤ 1/n →
        let y := normalCoordinateMap g (p i₀) x
        ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*φ (normalWaveEquiv y)) →
        let W := Real.exp (n*φ (normalWaveEquiv y))+R
        ∀ r : ℝ, 0 ≤ r →
        (Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
          {γ | ‖realWaveJet n W (finiteWaveSuperposition (w ∘ normalWaveEquiv)
            (fun i ℓ => U (p i) ℓ ∘ normalWaveEquiv) γ) y‖ ≤ r} ≤
          ENNReal.ofReal (C*n^28*r^4) := by
  apply physical_finite_superposition_smallBall g φ hφ hK _ _ m D
  · intro q hq ha
    apply actualProfileStrict_normal_direction g hφ hq
    exact hnc q.1 hq.1 (mt (normalWaveProfile_gradient_zero_iff g hφ hq).mpr ha)
  · intro q hq ha
    exact actualCriticalPlane_normal g hφ hq (hcrit q.1 hq.1
      ((normalWaveProfile_gradient_zero_iff g hφ hq).mp ha))


end YauCounterexamples
end

end OAI
