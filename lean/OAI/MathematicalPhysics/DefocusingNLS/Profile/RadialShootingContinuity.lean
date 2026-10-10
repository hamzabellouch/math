import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInitialValueExistence

namespace OAI

/-! Continuous dependence on the central amplitude for radial shooting. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem radialInitialPicard_initial_difference (R η a b M : ℝ) (hR : 0 ≤ R)
    (hη : 0 ≤ η) (hM : 0 ≤ M) (N : ℝ → ℝ → ℝ)
    (hN : Continuous (Function.uncurry N))
    (hBound : ∀ t ∈ Icc 0 R, ∀ x : ℝ, ‖N t x‖ ≤ M) (v : ℝ →ᵇ ℝ) :
    dist (boundedRadialInitialPicard R η a M hR hη hM N hN hBound v)
      (boundedRadialInitialPicard R η b M hR hη hM N hN hBound v) ≤ ‖a-b‖ := by
  rw [dist_eq_norm]
  apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).2
  intro r
  obtain ⟨hr,-⟩ := radialClamp_mem R r hR
  have he : Real.exp (-η*radialClamp R r) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith
  change ‖Real.exp (-η*radialClamp R r)*(a+radialVolterra _ _)-
    Real.exp (-η*radialClamp R r)*(b+radialVolterra _ _)‖ ≤ _
  rw [← mul_sub,add_sub_add_right_eq_sub,norm_mul,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (norm_nonneg _) he

noncomputable def radialShootingState (R L M : ℝ) (hR : 0 ≤ R)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (N : ℝ → ℝ → ℝ)
    (hN : Continuous (Function.uncurry N))
    (hBound : ∀ t ∈ Icc 0 R, ∀ x : ℝ, ‖N t x‖ ≤ M)
    (hLip : ∀ t ∈ Icc 0 R, ∀ x y : ℝ, ‖N t x-N t y‖ ≤ L*‖x-y‖)
    (a : ℝ) : ℝ →ᵇ ℝ :=
  (radialInitialPicard_contracting R a L M hR hL hM N hN hBound hLip).fixedPoint
    (boundedRadialInitialPicard R (1+L*R) a M hR (by positivity) hM N hN hBound)

theorem radialShootingState_fixed (R L M : ℝ) (hR : 0 ≤ R)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (N : ℝ → ℝ → ℝ)
    (hN : Continuous (Function.uncurry N))
    (hBound : ∀ t ∈ Icc 0 R, ∀ x : ℝ, ‖N t x‖ ≤ M)
    (hLip : ∀ t ∈ Icc 0 R, ∀ x y : ℝ, ‖N t x-N t y‖ ≤ L*‖x-y‖)
    (a r : ℝ) :
    radialShootingState R L M hR hL hM N hN hBound hLip a r=
      radialInitialPicard R (1+L*R) a N
        (radialShootingState R L M hR hL hM N hN hBound hLip a) r := by
  exact congrArg (fun v : ℝ →ᵇ ℝ => v r)
    (radialInitialPicard_contracting R a L M hR hL hM N hN hBound hLip).fixedPoint_isFixedPt.symm

theorem radialShootingState_lipschitz (R L M : ℝ) (hR : 0 ≤ R)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (N : ℝ → ℝ → ℝ)
    (hN : Continuous (Function.uncurry N))
    (hBound : ∀ t ∈ Icc 0 R, ∀ x : ℝ, ‖N t x‖ ≤ M)
    (hLip : ∀ t ∈ Icc 0 R, ∀ x y : ℝ, ‖N t x-N t y‖ ≤ L*‖x-y‖) :
    LipschitzWith ⟨12/11, by norm_num⟩
      (radialShootingState R L M hR hL hM N hN hBound hLip) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have hPa := radialInitialPicard_contracting R a L M hR hL hM N hN hBound hLip
  have h := hPa.dist_fixedPoint_fixedPoint_of_dist_le'
      (boundedRadialInitialPicard R (1+L*R) b M hR (by positivity) hM N hN hBound)
      (radialInitialPicard_contracting R a L M hR hL hM N hN hBound hLip).fixedPoint_isFixedPt
      (radialInitialPicard_contracting R b L M hR hL hM N hN hBound hLip).fixedPoint_isFixedPt
      (radialInitialPicard_initial_difference R (1+L*R) a b M hR (by positivity) hM N hN hBound)
  change dist _ _ ≤ (12/11 : ℝ)*dist a b
  convert! h using 1
  rw [dist_eq_norm]
  change (12/11 : ℝ)*‖a-b‖=‖a-b‖/(1-(1/12 : ℝ))
  norm_num
  ring

theorem continuous_radialShootingEndpoint (R L M : ℝ) (hR : 0 ≤ R)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (N : ℝ → ℝ → ℝ)
    (hN : Continuous (Function.uncurry N))
    (hBound : ∀ t ∈ Icc 0 R, ∀ x : ℝ, ‖N t x‖ ≤ M)
    (hLip : ∀ t ∈ Icc 0 R, ∀ x y : ℝ, ‖N t x-N t y‖ ≤ L*‖x-y‖) :
    Continuous (fun a => Real.exp ((1+L*R)*R)*
      radialShootingState R L M hR hL hM N hN hBound hLip a R) := by
  exact continuous_const.mul
    ((BoundedContinuousFunction.lipschitz_eval_const R).continuous.comp
      (radialShootingState_lipschitz R L M hR hL hM N hN hBound hLip).continuous)

end DefocusingNLS

end OAI
