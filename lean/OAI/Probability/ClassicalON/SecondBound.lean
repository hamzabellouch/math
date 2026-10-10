import OAI.Probability.ClassicalON.SecondGauge

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] in
theorem complexEnergy_normSq_re (S : SpinSystem 3 V E) (M : SpinOperator 3)
    (u : E → ℂ) (σ : V → Spin 3) :
    (S.complexEnergy M (fun e => u e * conj (u e)) σ).re =
      ∑ e, S.localCoefficient M σ e * ‖u e‖^2 := by
  simp [complexEnergy, MixedAlgebra.weighted, Complex.mul_conj, Complex.normSq_eq_norm_sq, -Complex.ofReal_pow]

theorem complexSecondResponse_upper (S : SpinSystem 3 V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β) (u : E → ℂ) :
    -(S.complexSecondResponse u (fun e => conj (u e))).re ≤ β*∑ e, ‖u e‖^2 := by
  unfold complexSecondResponse
  rw [S.averageComplex_re]
  have h (σ : V → Spin 3) :
      -(β*∑ e, ‖u e‖^2) ≤
        reObservable (S.complexSecondObservable u (fun e => conj (u e))) σ := by
    change _ ≤ (S.complexEnergy (axisC^2) (u*(fun e => conj (u e))) σ +
      S.complexEnergy axisC u σ * S.complexEnergy axisC (fun e => conj (u e)) σ).re
    rw [complexEnergy_conj, Complex.mul_conj, Complex.add_re, Complex.ofReal_re]
    have hc := S.complexEnergy_normSq_re (axisC^2) u σ
    change (S.complexEnergy (axisC^2) (u*(fun e => conj (u e))) σ).re = _ at hc
    rw [hc]
    have he : -(β*∑ e, ‖u e‖^2) ≤ ∑ e, S.localCoefficient (axisC^2) σ e*‖u e‖^2 := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro e _
      have hb' := (abs_le.mp (S.abs_localCoefficient_le β hb (axisC^2)
        (norm_square_le_one axisC axisC_norm_le) σ e)).1
      nlinarith [sq_nonneg ‖u e‖]
    exact he.trans (le_add_of_nonneg_right (Complex.normSq_nonneg _))
  have hm := S.averageLinear_mono (ContinuousMap.const _ (-(β*∑ e, ‖u e‖^2)))
    (reObservable (S.complexSecondObservable u (fun e => conj (u e)))) h
  rw [S.averageLinear_const] at hm
  linarith

omit [Fintype V] [Fintype E] in

def commutatorForm (S : SpinSystem 3 V E) (f g : V → ℂ) : E → ℂ :=
  (1/2 : ℂ) • S.complexCross f g

omit [Fintype V] [Fintype E] in
theorem commutatorForm_adjust (S : SpinSystem 3 V E) (f g : V → ℂ) :
    S.commutatorForm f g + S.differential ((1/2 : ℂ) • (f*g)) =
      fun e => ((f (S.left e)+f (S.right e))/2) * S.differential g e := by
  ext e
  simp only [commutatorForm, complexCross, differential, Pi.add_apply, Pi.mul_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype E] in
theorem commutatorForm_adjust_norm (S : SpinSystem 3 V E) (f g : V → ℂ) (e : E) :
    ‖((f (S.left e)+f (S.right e))/2) * S.differential g e‖ ≤
      ‖f‖ * ‖S.differential g e‖ := by
  rw [norm_mul, norm_div]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  norm_num
  have h := norm_add_le (f (S.left e)) (f (S.right e))
  have hx := norm_le_pi_norm f (S.left e)
  have hy := norm_le_pi_norm f (S.right e)
  linarith

theorem commutatorForm_bound_left (S : SpinSystem 3 V E) (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (f g : V → ℂ) (hP : ∀ x s, S.pin x = some s → f x = 0) :
    -(S.complexSecondResponse (S.commutatorForm f g)
      (fun e => conj (S.commutatorForm f g e))).re ≤
        β*(‖f‖^2*∑ e, ‖S.differential g e‖^2) := by
  let F : V → ℂ := (1/2 : ℂ) • (f*g)
  have hp (x) (s) (hs : S.pin x = some s) : F x = 0 := by
    simp only [F, Pi.smul_apply, Pi.mul_apply, hP x s hs, zero_mul, smul_zero]
  have hq (x) (s) (hs : S.pin x = some s) : conj (F x) = 0 := by rw [hp x s hs, map_zero]
  have hd : S.differential (fun x => conj (F x)) = fun e => conj (S.differential F e) := by
    ext e
    simp only [differential, map_sub]
  have hid := S.complexSecondResponse_add_gradients (S.commutatorForm f g)
    (fun e => conj (S.commutatorForm f g e)) F (fun x => conj (F x)) hp hq
  rw [hd] at hid
  have hc : ((fun e => conj (S.commutatorForm f g e)) + (fun e => conj (S.differential F e))) =
      (fun e => conj ((S.commutatorForm f g + S.differential F) e)) := by
    ext e
    simp only [Pi.add_apply, map_add]
  rw [hc] at hid
  rw [← hid]
  apply (S.complexSecondResponse_upper β hb _).trans
  apply mul_le_mul_of_nonneg_left _ hβ
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  change ‖(S.commutatorForm f g + S.differential ((1/2 : ℂ) • (f*g))) e‖^2 ≤ _
  rw [S.commutatorForm_adjust]
  have h := S.commutatorForm_adjust_norm f g e
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (mul_pow _ _ _)

end ClassicalON.SpinSystem

end

end OAI
