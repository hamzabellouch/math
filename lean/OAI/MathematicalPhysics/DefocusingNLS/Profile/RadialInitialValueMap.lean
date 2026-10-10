import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVolterraWeight
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialGreenOperator

namespace OAI

/-! The weighted Picard map for the radial amplitude initial-value problem. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

noncomputable def radialInitialForcing (R η : ℝ) (N : ℝ → ℝ → ℝ)
    (v : ℝ →ᵇ ℝ) (r : ℝ) : ℝ :=
  N (radialClamp R r) (Real.exp (η*radialClamp R r)*v (radialClamp R r))

noncomputable def radialInitialPicard (R η a₀ : ℝ) (N : ℝ → ℝ → ℝ)
    (v : ℝ →ᵇ ℝ) (r : ℝ) : ℝ :=
  Real.exp (-η*radialClamp R r)*(a₀+radialVolterra (radialInitialForcing R η N v) (radialClamp R r))

theorem continuous_radialInitialForcing (R η : ℝ) (N : ℝ → ℝ → ℝ)
    (hN : Continuous (Function.uncurry N)) (v : ℝ →ᵇ ℝ) :
    Continuous (radialInitialForcing R η N v) := by
  unfold radialInitialForcing
  exact hN.comp ((continuous_radialClamp R).prodMk
    ((Real.continuous_exp.comp (continuous_const.mul (continuous_radialClamp R))).mul
      (v.continuous.comp (continuous_radialClamp R))))

theorem radialInitialForcing_difference (R η L : ℝ) (hL : 0 ≤ L)
    (N : ℝ → ℝ → ℝ)
    (hN : ∀ t ∈ Icc 0 R, ∀ x y : ℝ, ‖N t x-N t y‖ ≤ L*‖x-y‖)
    (u v : ℝ →ᵇ ℝ) (t : ℝ) (ht : t ∈ Icc 0 R) :
    ‖radialInitialForcing R η N u t-radialInitialForcing R η N v t‖ ≤
      (L*‖u-v‖)*Real.exp (η*t) := by
  simp only [radialInitialForcing,radialClamp_eq R t ht]
  calc
    _ ≤ L*‖Real.exp (η*t)*u t-Real.exp (η*t)*v t‖ := hN t ht _ _
    _ = (L*Real.exp (η*t))*‖u t-v t‖ := by
      rw [← mul_sub,norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      ring
    _ ≤ (L*Real.exp (η*t))*‖u-v‖ :=
      mul_le_mul_of_nonneg_left ((u-v).norm_coe_le_norm t)
        (mul_nonneg hL (Real.exp_pos _).le)
    _ = _ := by ring

theorem continuous_radialInitialPicard (R η a₀ : ℝ) (N : ℝ → ℝ → ℝ)
    (hN : Continuous (Function.uncurry N)) (v : ℝ →ᵇ ℝ) :
    Continuous (radialInitialPicard R η a₀ N v) := by
  have hf := continuous_radialInitialForcing R η N hN v
  have hV : Continuous (radialVolterra (radialInitialForcing R η N v)) :=
    (show Differentiable ℝ (radialVolterra (radialInitialForcing R η N v)) from
      fun r => (hasDerivAt_radialVolterra _ hf r).differentiableAt).continuous
  exact (Real.continuous_exp.comp (continuous_const.mul (continuous_radialClamp R))).mul
    (continuous_const.add (hV.comp (continuous_radialClamp R)))

theorem radialInitialPicard_bound (R η a₀ M : ℝ) (hR : 0 ≤ R) (hη : 0 ≤ η)
    (hM : 0 ≤ M) (N : ℝ → ℝ → ℝ)
    (hN : ∀ t ∈ Icc 0 R, ∀ x : ℝ, ‖N t x‖ ≤ M) (v : ℝ →ᵇ ℝ) (r : ℝ) :
    ‖radialInitialPicard R η a₀ N v r‖ ≤ ‖a₀‖+M*R^2/24 := by
  let t := radialClamp R r
  obtain ⟨ht,htR⟩ := radialClamp_mem R r hR
  have hf : ∀ s ∈ Icc 0 t, ‖radialInitialForcing R η N v s‖ ≤ M := by
    intro s hs
    simp only [radialInitialForcing,radialClamp_eq R s ⟨hs.1,hs.2.trans htR⟩]
    exact hN s ⟨hs.1,hs.2.trans htR⟩ _
  have hV := radialVolterra_norm_le (radialInitialForcing R η N v) M t ht hf
  have he : Real.exp (-η*t) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith
  change ‖Real.exp (-η*t)*(a₀+radialVolterra _ t)‖ ≤ _
  rw [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ 1*‖a₀+radialVolterra _ t‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
    _ ≤ ‖a₀‖+‖radialVolterra _ t‖ := by simpa only [one_mul] using norm_add_le a₀ _
    _ ≤ ‖a₀‖+M*t^2/24 := add_le_add_right hV _
    _ ≤ ‖a₀‖+M*R^2/24 := by gcongr

theorem radialInitialPicard_lipschitz (R η a₀ L : ℝ) (hR : 0 ≤ R)
    (hη : 0 < η) (hL : 0 ≤ L) (N : ℝ → ℝ → ℝ)
    (hN : Continuous (Function.uncurry N))
    (hLip : ∀ t ∈ Icc 0 R, ∀ x y : ℝ, ‖N t x-N t y‖ ≤ L*‖x-y‖)
    (u v : ℝ →ᵇ ℝ) (r : ℝ) :
    ‖radialInitialPicard R η a₀ N u r-radialInitialPicard R η a₀ N v r‖ ≤
      (L*R/(12*η))*‖u-v‖ := by
  let t := radialClamp R r
  obtain ⟨ht,htR⟩ := radialClamp_mem R r hR
  have hu := continuous_radialInitialForcing R η N hN u
  have hv := continuous_radialInitialForcing R η N hN v
  have hd := radialVolterra_exponential_bound
    (radialInitialForcing R η N u-radialInitialForcing R η N v)
    (L*‖u-v‖) η t (mul_nonneg hL (norm_nonneg _)) hη ht
    (fun s hs => radialInitialForcing_difference R η L hL N hLip u v s ⟨hs.1,hs.2.trans htR⟩)
  change ‖Real.exp (-η*t)*(a₀+radialVolterra _ t)-
    Real.exp (-η*t)*(a₀+radialVolterra _ t)‖ ≤ _
  rw [← mul_sub,add_sub_add_left_eq_sub,← radialVolterra_sub _ _ hu hv,norm_mul,
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-η*t)*((L*‖u-v‖)*t/(12*η)*Real.exp (η*t)) :=
      mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le
    _ = (L*t/(12*η))*‖u-v‖ := by
      rw [show -η*t= -(η*t) by ring,Real.exp_neg]
      field_simp [hη.ne',ne_of_gt (Real.exp_pos (η*t))]
    _ ≤ (L*R/(12*η))*‖u-v‖ := by gcongr

end DefocusingNLS

end OAI
