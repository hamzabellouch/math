import OAI.Probability.ClassicalON.SecondBound

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] in
theorem complexEnergy_norm_le (S : SpinSystem 3 V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (M : SpinOperator 3) (hM : ‖M‖ ≤ 1) (u : E → ℂ) (σ : V → Spin 3) :
    ‖S.complexEnergy M u σ‖ ≤ β*∑ e, ‖u e‖ := by
  unfold complexEnergy MixedAlgebra.weighted
  calc _ ≤ ∑ e, ‖(S.localCoefficient M σ e : ℂ)*u e‖ := norm_sum_le _ _
       _ ≤ ∑ e, β*‖u e‖ := by
         apply Finset.sum_le_sum
         intro e _
         rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
         exact mul_le_mul_of_nonneg_right (S.abs_localCoefficient_le β hb M hM σ e) (norm_nonneg _)
       _ = _ := (Finset.mul_sum _ _ _).symm

omit [Fintype V] in
@[simp] theorem complexEnergy_sub (S : SpinSystem 3 V E) (M : SpinOperator 3)
    (u v : E → ℂ) (σ : V → Spin 3) :
    S.complexEnergy M (u-v) σ = S.complexEnergy M u σ - S.complexEnergy M v σ := by
  simp only [complexEnergy, MixedAlgebra.weighted, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

def quadraticObservable (S : SpinSystem 3 V E) (u : E → ℂ) : C((V → Spin 3), ℝ) :=
  reObservable (S.currentObservable (axisC^2) (u*(fun e => conj (u e))))

omit [Fintype V] in
@[simp] theorem quadraticObservable_apply (S : SpinSystem 3 V E) (u : E → ℂ) (σ) :
    S.quadraticObservable u σ = ∑ e, S.localCoefficient (axisC^2) σ e*‖u e‖^2 :=
  S.complexEnergy_normSq_re (axisC^2) u σ

omit [Fintype V] in
theorem quadraticObservable_lower (S : SpinSystem 3 V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β) (u : E → ℂ) (σ) :
    -(β*∑ e, ‖u e‖^2) ≤ S.quadraticObservable u σ := by
  rw [quadraticObservable_apply, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro e _
  have h := (abs_le.mp (S.abs_localCoefficient_le β hb (axisC^2)
    (norm_square_le_one axisC axisC_norm_le) σ e)).1
  nlinarith [sq_nonneg ‖u e‖]

theorem complexSecondResponse_re_decomposition (S : SpinSystem 3 V E) (u : E → ℂ) :
    (S.complexSecondResponse u (fun e => conj (u e))).re =
      S.averageLinear (S.quadraticObservable u) +
        S.averageLinear (normObservable (S.currentObservable axisC u) *
          normObservable (S.currentObservable axisC u)) := by
  unfold complexSecondResponse
  rw [S.averageComplex_re, ← map_add]
  congr 1
  ext σ
  change (S.complexEnergy (axisC^2) (u*(fun e => conj (u e))) σ +
    S.complexEnergy axisC u σ*S.complexEnergy axisC (fun e => conj (u e)) σ).re = _
  rw [complexEnergy_conj, Complex.add_re, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]
  change _ + ‖S.complexEnergy axisC u σ‖^2 = _ + ‖S.complexEnergy axisC u σ‖*‖S.complexEnergy axisC u σ‖
  exact congrArg ((S.complexEnergy (axisC^2) (u*(fun e => conj (u e))) σ).re + ·) (pow_two _)

theorem current_moment_of_response_nonpos (S : SpinSystem 3 V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β) (u : E → ℂ)
    (hR : (S.complexSecondResponse u (fun e => conj (u e))).re ≤ 0) :
    S.averageLinear (normObservable (S.currentObservable axisC u) *
      normObservable (S.currentObservable axisC u)) ≤ β*∑ e, ‖u e‖^2 := by
  rw [S.complexSecondResponse_re_decomposition] at hR
  have h := S.averageLinear_mono (ContinuousMap.const _ (-(β*∑ e, ‖u e‖^2)))
    (S.quadraticObservable u) (S.quadraticObservable_lower β hb u)
  rw [S.averageLinear_const] at h
  linarith

theorem current_moment_difference (S : SpinSystem 3 V E)
    (F G : C((V → Spin 3), ℂ)) (b v : ℝ) (hb : 0 ≤ b)
    (hFG : ∀ σ, ‖F σ-G σ‖ ≤ b)
    (hF : S.averageLinear (normObservable F * normObservable F) ≤ v) :
    S.averageLinear (normObservable G * normObservable G) -
      S.averageLinear (normObservable F * normObservable F) ≤ 2*b*Real.sqrt v+b^2 := by
  have hpt (σ : V → Spin 3) : (normObservable G * normObservable G) σ ≤
      (normObservable F * normObservable F + (2*b) • normObservable F + ContinuousMap.const (V → Spin 3) (b^2)) σ := by
    change ‖G σ‖*‖G σ‖ ≤ ‖F σ‖*‖F σ‖+2*b*‖F σ‖+b^2
    have hn : ‖G σ‖ ≤ ‖F σ‖+b := by
      calc _ ≤ ‖F σ‖+‖G σ-F σ‖ := norm_le_insert' _ _
           _ ≤ _ := by rw [norm_sub_rev]; exact add_le_add le_rfl (hFG σ)
    nlinarith [norm_nonneg (F σ), norm_nonneg (G σ)]
  have hm := S.averageLinear_mono _ _ hpt
  simp only [map_add, map_smul, smul_eq_mul, S.averageLinear_const] at hm
  have hav := (S.averageLinear_norm_le_sqrt F).trans (Real.sqrt_le_sqrt hF)
  have hmul := mul_le_mul_of_nonneg_left hav (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hb)
  linarith

theorem abs_norm_sq_sub_norm_sq (z w : ℂ) :
    |‖z‖^2-‖w‖^2| ≤ ‖z-w‖*(‖z‖+‖w‖) := by
  calc _ = |‖z‖-‖w‖| * (‖z‖+‖w‖) := by
          rw [← abs_of_nonneg (add_nonneg (norm_nonneg z) (norm_nonneg w)), ← abs_mul]
          congr 1
          ring
       _ ≤ _ := mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le z w)
          (add_nonneg (norm_nonneg z) (norm_nonneg w))

omit [Fintype V] in
theorem quadraticObservable_difference (S : SpinSystem 3 V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β) (u v : E → ℂ) (σ) :
    S.quadraticObservable v σ - S.quadraticObservable u σ ≤
      β*∑ e, ‖u e-v e‖*(‖u e‖+‖v e‖) := by
  simp only [quadraticObservable_apply, ← Finset.sum_sub_distrib, Finset.mul_sum, ← mul_sub]
  apply Finset.sum_le_sum
  intro e _
  calc _ ≤ |S.localCoefficient (axisC^2) σ e*(‖v e‖^2-‖u e‖^2)| := le_abs_self _
       _ = |S.localCoefficient (axisC^2) σ e| * |‖v e‖^2-‖u e‖^2| := abs_mul _ _
       _ ≤ β*(‖u e-v e‖*(‖u e‖+‖v e‖)) := by
         apply mul_le_mul (S.abs_localCoefficient_le β hb (axisC^2)
           (norm_square_le_one axisC axisC_norm_le) σ e) _ (abs_nonneg _)
           (abs_nonneg _ |>.trans (S.abs_localCoefficient_le β hb (axisC^2)
             (norm_square_le_one axisC axisC_norm_le) σ e))
         simpa only [abs_sub_comm] using abs_norm_sq_sub_norm_sq (u e) (v e)

theorem response_transfer (S : SpinSystem 3 V E) (β a : ℝ) (hβ : 0 ≤ β) (ha : 0 ≤ a)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β) (u v : E → ℂ)
    (hr : -(S.complexSecondResponse v (fun e => conj (v e))).re ≤ a) :
    -(S.complexSecondResponse u (fun e => conj (u e))).re ≤ a +
      β*∑ e, ‖u e-v e‖*(‖u e‖+‖v e‖) +
      2*(β*∑ e, ‖u e-v e‖)*Real.sqrt (β*∑ e, ‖u e‖^2) +
      (β*∑ e, ‖u e-v e‖)^2 := by
  have hb' : 0 ≤ β*∑ e, ‖u e-v e‖ := mul_nonneg hβ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hl : 0 ≤ β*∑ e, ‖u e-v e‖*(‖u e‖+‖v e‖) := mul_nonneg hβ
    (Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  by_cases hR : (S.complexSecondResponse u (fun e => conj (u e))).re ≤ 0
  · have hm := S.current_moment_difference (S.currentObservable axisC u) (S.currentObservable axisC v)
      (β*∑ e, ‖u e-v e‖) (β*∑ e, ‖u e‖^2) hb'
      (fun σ => by
        change ‖S.complexEnergy axisC u σ-S.complexEnergy axisC v σ‖ ≤ _
        rw [← S.complexEnergy_sub]
        exact S.complexEnergy_norm_le β hb axisC axisC_norm_le (u-v) σ)
      (S.current_moment_of_response_nonpos β hb u hR)
    have hq := S.averageLinear_mono (S.quadraticObservable v-S.quadraticObservable u)
      (ContinuousMap.const _ (β*∑ e, ‖u e-v e‖*(‖u e‖+‖v e‖)))
      (S.quadraticObservable_difference β hb u v)
    rw [map_sub, S.averageLinear_const] at hq
    rw [S.complexSecondResponse_re_decomposition] at hr ⊢
    linarith
  · have he : 0 ≤ 2*(β*∑ e, ‖u e-v e‖)*Real.sqrt (β*∑ e, ‖u e‖^2) :=
      mul_nonneg (mul_nonneg (by norm_num) hb') (Real.sqrt_nonneg _)
    linarith [sq_nonneg (β*∑ e, ‖u e-v e‖)]

end ClassicalON.SpinSystem

end

end OAI
