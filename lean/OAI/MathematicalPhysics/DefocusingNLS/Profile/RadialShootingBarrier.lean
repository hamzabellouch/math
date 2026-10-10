import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialShootingEquation

namespace OAI

/-! Constant barriers for the radial shooting family, proved along Picard iterates. -/

open Set Filter Topology
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem radialVolterra_nonneg (f : ℝ → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hf : ∀ t ∈ Icc 0 r, 0 ≤ f t) : 0 ≤ radialVolterra f r := by
  simpa only [radialVolterra,radialDirichletKernel] using
    radialDirichletKernel_nonneg r 0 f le_rfl hr hf

theorem radialVolterra_nonpos (f : ℝ → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hf : ∀ t ∈ Icc 0 r, f t ≤ 0) : radialVolterra f r ≤ 0 := by
  have h := radialVolterra_nonneg (-f) r hr (fun t ht => neg_nonneg.2 (hf t ht))
  simpa only [radialVolterra,radialAverage,Pi.neg_apply,neg_mul,mul_neg,
    intervalIntegral.integral_neg,neg_nonneg] using h

theorem radialInitialPicard_unweight (R η a : ℝ) (N : ℝ → ℝ → ℝ)
    (v : ℝ →ᵇ ℝ) (r : ℝ) (hr : r ∈ Icc 0 R) :
    Real.exp (η*r)*radialInitialPicard R η a N v r=
      a+radialVolterra (radialInitialForcing R η N v) r := by
  simp only [radialInitialPicard,radialClamp_eq R r hr]
  rw [← mul_assoc,← Real.exp_add]
  ring_nf
  simp only [Real.exp_zero,one_mul]

noncomputable def radialWeightedConstant (R η a : ℝ) (hR : 0 ≤ R) (hη : 0 ≤ η) :
    ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun r => Real.exp (-η*radialClamp R r)*a)
    ((Real.continuous_exp.comp (continuous_const.mul (continuous_radialClamp R))).mul
      continuous_const) ‖a‖ (by
      intro r
      have hr := (radialClamp_mem R r hR).1
      have he : Real.exp (-η*radialClamp R r) ≤ 1 := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        nlinarith
      rw [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_left (norm_nonneg _) he)

theorem radialWeightedConstant_unweight (R η a : ℝ) (hR : 0 ≤ R) (hη : 0 ≤ η)
    (r : ℝ) (hr : r ∈ Icc 0 R) :
    Real.exp (η*r)*radialWeightedConstant R η a hR hη r=a := by
  change Real.exp (η*r)*(Real.exp (-η*radialClamp R r)*a)=a
  rw [radialClamp_eq R r hr,← mul_assoc,← Real.exp_add]
  ring_nf
  simp only [Real.exp_zero,one_mul]

theorem radialShooting_lower_start (R L M : ℝ) (hR : 0 ≤ R)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (N : ℝ → ℝ → ℝ)
    (hN : Continuous (Function.uncurry N))
    (hBound : ∀ t ∈ Icc 0 R, ∀ x : ℝ, ‖N t x‖ ≤ M)
    (hLip : ∀ t ∈ Icc 0 R, ∀ x y : ℝ, ‖N t x-N t y‖ ≤ L*‖x-y‖)
    (a : ℝ) (ha : ∀ t ∈ Icc 0 R, ∀ x ≤ a, N t x ≤ 0) :
    ∀ r ∈ Icc 0 R, radialShootingAmplitude R L M hR hL hM N hN hBound hLip a r ≤ a := by
  let η := 1+L*R
  have hη : 0 ≤ η := by dsimp only [η]; positivity
  let P := boundedRadialInitialPicard R η a M hR hη hM N hN hBound
  let b := radialWeightedConstant R η a hR hη
  have hP : ContractingWith ⟨1/12, by norm_num⟩ P :=
    radialInitialPicard_contracting R a L M hR hL hM N hN hBound hLip
  have hi : ∀ n : ℕ, ∀ r ∈ Icc 0 R, Real.exp (η*r)*(P^[n] b) r ≤ a := by
    intro n
    induction n with
    | zero =>
      intro r hr
      exact (radialWeightedConstant_unweight R η a hR hη r hr).le
    | succ n hn =>
      intro r hr
      rw [Function.iterate_succ_apply']
      change Real.exp (η*r)*radialInitialPicard R η a N (P^[n] b) r ≤ a
      rw [radialInitialPicard_unweight R η a N _ r hr]
      have hV := radialVolterra_nonpos (radialInitialForcing R η N (P^[n] b)) r hr.1 (by
        intro t ht
        have htR : t ∈ Icc 0 R := ⟨ht.1,ht.2.trans hr.2⟩
        simp only [radialInitialForcing,radialClamp_eq R t htR]
        exact ha t htR _ (hn t htR))
      linarith
  intro r hr
  rw [radialShootingAmplitude_eq R L M hR hL hM N hN hBound hLip a r hr]
  have ht : Tendsto (fun n => (P^[n] b) r) atTop (𝓝 (hP.fixedPoint P r)) :=
    ((BoundedContinuousFunction.lipschitz_eval_const r).continuous.continuousAt.tendsto).comp
      (hP.tendsto_iterate_fixedPoint b)
  exact le_of_tendsto (ht.const_mul (Real.exp (η*r))) (Eventually.of_forall (fun n => hi n r hr))

theorem radialShooting_upper_start (R L M : ℝ) (hR : 0 ≤ R)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (N : ℝ → ℝ → ℝ)
    (hN : Continuous (Function.uncurry N))
    (hBound : ∀ t ∈ Icc 0 R, ∀ x : ℝ, ‖N t x‖ ≤ M)
    (hLip : ∀ t ∈ Icc 0 R, ∀ x y : ℝ, ‖N t x-N t y‖ ≤ L*‖x-y‖)
    (a : ℝ) (ha : ∀ t ∈ Icc 0 R, ∀ x, a ≤ x → 0 ≤ N t x) :
    ∀ r ∈ Icc 0 R, a ≤ radialShootingAmplitude R L M hR hL hM N hN hBound hLip a r := by
  let η := 1+L*R
  have hη : 0 ≤ η := by dsimp only [η]; positivity
  let P := boundedRadialInitialPicard R η a M hR hη hM N hN hBound
  let b := radialWeightedConstant R η a hR hη
  have hP : ContractingWith ⟨1/12, by norm_num⟩ P :=
    radialInitialPicard_contracting R a L M hR hL hM N hN hBound hLip
  have hi : ∀ n : ℕ, ∀ r ∈ Icc 0 R, a ≤ Real.exp (η*r)*(P^[n] b) r := by
    intro n
    induction n with
    | zero =>
      intro r hr
      exact (radialWeightedConstant_unweight R η a hR hη r hr).ge
    | succ n hn =>
      intro r hr
      rw [Function.iterate_succ_apply']
      change a ≤ Real.exp (η*r)*radialInitialPicard R η a N (P^[n] b) r
      rw [radialInitialPicard_unweight R η a N _ r hr]
      have hV := radialVolterra_nonneg (radialInitialForcing R η N (P^[n] b)) r hr.1 (by
        intro t ht
        have htR : t ∈ Icc 0 R := ⟨ht.1,ht.2.trans hr.2⟩
        simp only [radialInitialForcing,radialClamp_eq R t htR]
        exact ha t htR _ (hn t htR))
      linarith
  intro r hr
  rw [radialShootingAmplitude_eq R L M hR hL hM N hN hBound hLip a r hr]
  have ht : Tendsto (fun n => (P^[n] b) r) atTop (𝓝 (hP.fixedPoint P r)) :=
    ((BoundedContinuousFunction.lipschitz_eval_const r).continuous.continuousAt.tendsto).comp
      (hP.tendsto_iterate_fixedPoint b)
  exact ge_of_tendsto (ht.const_mul (Real.exp (η*r))) (Eventually.of_forall (fun n => hi n r hr))

end DefocusingNLS

end OAI
