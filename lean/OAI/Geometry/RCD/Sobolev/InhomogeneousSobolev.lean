import OAI.Geometry.RCD.Coordinates.NormalizedL2SobolevMoment

namespace OAI

/-! # Relative Dirichlet Sobolev inequality with an L² term

Keeping the L² term removes the exterior-annulus condition. This is the
form used by the local harmonic boundedness iteration.
-/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

private theorem inhomogeneous_power_bound {I V T C c p : ℝ}
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

/-- A fixed exponent above two, with an inhomogeneous energy term, at
bounded rescaled curvature. No exterior-annulus assumption is needed. -/
theorem NoncollapsedRCD.inhomogeneous_dirichlet_sobolev {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) :
    ∃ p C : ℝ, 2 < p ∧ 0 < C ∧ ∀ (x : X) (R : ℝ), 0 < R → -1 ≤ K*R^2 →
      ∀ w : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball x R),
      IntegrableOn (fun y => |SobolevSpace.toLp (hausdorff n X) hX.quadratic w.val y|^p)
        (ball x R) (hausdorff n X) ∧
      (∫ y in ball x R, |SobolevSpace.toLp (hausdorff n X) hX.quadratic w.val y|^p
        ∂hausdorff n X)^(2/p) ≤
      C*((hausdorff n X).real (ball x R))^(2/p-1)*
        (R^2*energyForm (hausdorff n X) hX.quadratic w.val w.val+
          ‖SobolevSpace.toLp (hausdorff n X) hX.quadratic w.val‖^2) := by
  obtain ⟨p,C,hp,hC,hnormalized⟩ := hX.normalized_dirichlet_l2_moment hn
  have hp0 : 0 < p := by linarith
  refine ⟨p,C^(2/p),hp,Real.rpow_pos_of_pos hC _,?_⟩
  intro x R hR hcurv w
  let μ := hausdorff n X
  let u := SobolevSpace.toLp μ hX.quadratic w.val
  let V := μ.real (ball x R)
  let E := energyForm μ hX.quadratic w.val w.val
  let T := R^2*E+‖u‖^2
  let I := ∫ y in ball x R, |u y|^p ∂μ
  have hV : 0 < V := ENNReal.toReal_pos (hX.fullSupport x R hR).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hE : 0 ≤ E := by
    dsimp only [E]
    rw [energyForm_self]
    exact mul_nonneg (by norm_num) (SobolevSpace.energy_nonneg μ hX.quadratic w.val)
  have hT : 0 ≤ T := add_nonneg (mul_nonneg (sq_nonneg R) hE) (sq_nonneg _)
  have hI : 0 ≤ I := integral_nonneg fun y => Real.rpow_nonneg (abs_nonneg (u y)) _
  change IntegrableOn (fun y => |u y|^p) (ball x R) μ ∧
    I^(2/p) ≤ C^(2/p)*V^(2/p-1)*T
  by_cases hTz : T = 0
  · have huz : u = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp (by
      have hh : ‖u‖^2 ≤ T := le_add_of_nonneg_left (mul_nonneg (sq_nonneg R) hE)
      exact le_antisymm (hTz ▸ hh) (sq_nonneg _)))
    have hu0 : u =ᵐ[μ] fun _ => 0 := huz ▸ Lp.coeFn_zero _ _ _
    have hzero : (fun y => |u y|^p) =ᵐ[μ.restrict (ball x R)] fun _ => 0 := by
      filter_upwards [ae_restrict_of_ae hu0] with y hy
      simp only [hy, abs_zero, Real.zero_rpow hp0.ne']
    refine ⟨(integrable_zero _ _ _).congr hzero.symm, ?_⟩
    have hIz : I = 0 := (integral_congr_ae hzero).trans (integral_zero _ _)
    rw [hIz, Real.zero_rpow (by positivity : (2/p:ℝ)≠0), hTz, mul_zero]
  have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hTz)
  let c := Real.sqrt (V/T)
  have hc : 0 < c := Real.sqrt_pos.mpr (div_pos hV hTpos)
  have hc2 : c^2 = V/T := Real.sq_sqrt (div_nonneg hV.le hTpos.le)
  have hscale : c^2*T = V := by rw [hc2]; exact div_mul_cancel₀ V hTpos.ne'
  let v : SobolevSpace.dirichlet μ hX.quadratic (ball x R) := c • w
  have hEv : energyForm μ hX.quadratic v.val v.val = c^2*E := by
    change energyForm μ hX.quadratic (c • w.val) (c • w.val) = _
    rw [energyForm_smul_left, energyForm_smul_right]
    ring
  have hUv : ‖SobolevSpace.toLp μ hX.quadratic v.val‖^2 = c^2*‖u‖^2 := by
    change ‖SobolevSpace.toLp μ hX.quadratic (c • w.val)‖^2 = _
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_pow]
  have hsum : R^2*energyForm μ hX.quadratic v.val v.val+
      ‖SobolevSpace.toLp μ hX.quadratic v.val‖^2 = V := by
    rw [hEv,hUv]
    calc
      _ = c^2*T := by dsimp only [T]; ring
      _ = V := hscale
  have hEn : 0 ≤ R^2*energyForm μ hX.quadratic v.val v.val := by rw [hEv]; positivity
  obtain ⟨hvi,hvb⟩ := hnormalized x R hR hcurv v
    (by linarith [sq_nonneg ‖SobolevSpace.toLp μ hX.quadratic v.val‖])
    (by linarith [sq_nonneg ‖SobolevSpace.toLp μ hX.quadratic v.val‖])
  have hvrep : SobolevSpace.toLp μ hX.quadratic v.val =ᵐ[μ] fun y => c*u y := by
    change SobolevSpace.toLp μ hX.quadratic (c • w.val) =ᵐ[μ] _
    rw [map_smul]
    exact Lp.coeFn_smul _ _
  have hpowrep : (fun y => |SobolevSpace.toLp μ hX.quadratic v.val y|^p) =ᵐ[
      μ.restrict (ball x R)] fun y => c^p*|u y|^p := by
    filter_upwards [ae_restrict_of_ae hvrep] with y hy
    rw [hy,abs_mul,abs_of_pos hc,Real.mul_rpow hc.le (abs_nonneg _)]
  have hui : IntegrableOn (fun y => |u y|^p) (ball x R) μ :=
    (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr
      (Real.rpow_pos_of_pos hc p).ne') _).mp (hvi.congr hpowrep)
  have hmoment : c^p*I ≤ C*V := by
    rw [← integral_const_mul, ← integral_congr_ae hpowrep]
    exact hvb
  refine ⟨hui, ?_⟩
  have hout := inhomogeneous_power_bound hI hV hC hc hp0 hscale hmoment
  nlinarith only [hout]

end RegularPointCoordinates

end

end OAI
