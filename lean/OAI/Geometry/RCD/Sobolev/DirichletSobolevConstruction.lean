import OAI.Geometry.RCD.Coordinates.NormalizedSobolevMoment
import OAI.Geometry.RCD.Sobolev.DirichletSobolevInput

namespace OAI

/-! # The local Dirichlet Sobolev input from RCD transport and volume bounds -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

private theorem scaled_power_bound {I V T C c p : ℝ}
    (hI : 0 ≤ I) (hV : 0 < V) (hC : 0 < C) (hc : 0 < c) (hp : 0 < p)
    (hscale : c^2*T = V) (hbound : c^p*I ≤ C*V) :
    I^(2/p) ≤ C^(2/p)*T*V^(2/p-1) := by
  have hlam : (c^p)^(2/p) = c^2 := by
    rw [← Real.rpow_mul hc.le]
    have he : p*(2/p) = 2 := by field_simp
    rw [he, Real.rpow_two]
  have hpow := Real.rpow_le_rpow
    (mul_nonneg (Real.rpow_nonneg hc.le _) hI) hbound (by positivity : 0≤2/p)
  rw [Real.mul_rpow (Real.rpow_nonneg hc.le _) hI, hlam,
    Real.mul_rpow hC.le hV.le] at hpow
  have hvpow : V^(2/p) = V^(2/p-1)*V := by
    calc
      _ = V^((2/p-1)+1) := by congr 1; ring
      _ = V^(2/p-1)*V^((1:ℝ)) := Real.rpow_add hV _ _
      _ = _ := by rw [Real.rpow_one]
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hc)).mp
  calc
    _ ≤ C^(2/p)*V^(2/p) := hpow
    _ = C^(2/p)*V^(2/p-1)*(c^2*T) := by rw [hscale, hvpow]; ring
    _ = _ := by ring

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The superquadratic zero-boundary estimate required by the Poisson
construction is a consequence of actual RCD transport and finite covers. -/
theorem NoncollapsedRCD.localDirichletSobolevInput {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) : LocalDirichletSobolevInput hX := by
  intro hn
  obtain ⟨p, C, hp, hC, hnormalized⟩ := hX.normalized_dirichlet_moment hn
  obtain ⟨P, hP, hPoincare⟩ := hX.uniform_annular_coercivity hn
  have hp0 : 0 < p := by linarith
  refine ⟨p/2, C^(2/p), by linarith, Real.rpow_pos_of_pos hC _, ?_⟩
  intro x R hR hcurv hann w
  have hcurv2 : -1 ≤ K*(2*R)^2 := by
    by_cases hK : 0 ≤ K
    · exact (by norm_num : (-1:ℝ)≤0).trans (mul_nonneg hK (sq_nonneg _))
    · have hh := mul_le_mul_of_nonpos_left (show (2*R)^2 ≤ (64*R)^2 by nlinarith)
        (le_of_not_ge hK)
      linarith
  let μ := hausdorff n X
  let u := SobolevSpace.toLp μ hX.quadratic w.val
  let V := μ.real (ball x R)
  let E := energyForm μ hX.quadratic w.val w.val
  let I := ∫ y in ball x R, |u y|^p ∂μ
  have hV : 0 < V := ENNReal.toReal_pos (hX.fullSupport x R hR).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hE : 0 ≤ E := by
    dsimp only [E]
    rw [energyForm_self]
    exact mul_nonneg (by norm_num) (SobolevSpace.energy_nonneg μ hX.quadratic w.val)
  have hI : 0 ≤ I := integral_nonneg fun y => Real.rpow_nonneg (abs_nonneg (u y)) _
  have he : (1:ℝ)/(p/2) = 2/p := by field_simp
  change (∫ y in ball x R, |u y|^(2*(p/2)) ∂μ)^(1/(p/2)) ≤
    (C^(2/p)*R^2*V^(1/(p/2)-1))*E
  rw [show 2*(p/2) = p by ring, he]
  change I^(2/p) ≤ (C^(2/p)*R^2*V^(2/p-1))*E
  by_cases hEz : E = 0
  · have hl2 := hPoincare x R hR hcurv2 hann w
    change ‖u‖^2 ≤ P*R^2*E at hl2
    rw [hEz, mul_zero] at hl2
    have huz : u = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hl2 (sq_nonneg _)))
    have hu0 : u =ᵐ[μ] fun _ => 0 := huz ▸ Lp.coeFn_zero _ _ _
    have hIz : I = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_of_ae hu0] with y hy
      simp only [hy, abs_zero, Real.zero_rpow hp0.ne', Pi.zero_apply]
    rw [hIz, Real.zero_rpow (by positivity : (2/p:ℝ)≠0), hEz, mul_zero]
  have hEpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hEz)
  let c := Real.sqrt (V/(R^2*E))
  have hc : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hc2 : c^2 = V/(R^2*E) := Real.sq_sqrt (by positivity)
  let v : SobolevSpace.dirichlet μ hX.quadratic (ball x R) := c • w
  have hEv : energyForm μ hX.quadratic v.val v.val = c^2*E := by
    change energyForm μ hX.quadratic (c • w.val) (c • w.val) = _
    rw [energyForm_smul_left, energyForm_smul_right]
    ring
  have hscale : c^2*(R^2*E) = V := by
    rw [hc2]
    exact div_mul_cancel₀ V (by positivity)
  have hnormalize : R^2*energyForm μ hX.quadratic v.val v.val ≤ V := by
    rw [hEv]
    nlinarith [hscale]
  obtain ⟨_, hvbound⟩ := hnormalized x R hR hcurv2 hann v hnormalize
  have hvrep : SobolevSpace.toLp μ hX.quadratic v.val =ᵐ[μ] fun y => c*u y := by
    change SobolevSpace.toLp μ hX.quadratic (c • w.val) =ᵐ[μ] _
    rw [map_smul]
    exact Lp.coeFn_smul _ _
  have hmoment : c^p*I ≤ C*V := by
    calc
      _ = ∫ y in ball x R, |SobolevSpace.toLp μ hX.quadratic v.val y|^p ∂μ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hvrep] with y hy
        rw [hy, abs_mul, abs_of_pos hc, Real.mul_rpow hc.le (abs_nonneg _)]
      _ ≤ _ := hvbound
  have hout := scaled_power_bound hI hV hC hc hp0 hscale hmoment
  nlinarith only [hout]

end RegularPointCoordinates

end

end OAI
