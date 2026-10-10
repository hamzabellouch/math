import OAI.Probability.FKPressure.Coefficients

namespace OAI

 

noncomputable section
open Finset FormalMultilinearSeries
open scoped Classical Topology NNReal ENNReal
namespace BelowOne.PressureSeries
open MultiaffineDerivative
variable {V : Type*} [Fintype V]

def complexify (p : FormalMultilinearSeries ℝ (V → ℝ) ℝ) :
    FormalMultilinearSeries ℂ (V → ℂ) ℂ := fun n =>
  ∑ τ : Fin n → V, (weight p ⟨n,τ⟩ : ℂ) •
    (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compContinuousLinearMap
      (fun j => ContinuousLinearMap.proj (τ j))

lemma complexify_apply (p : FormalMultilinearSeries ℝ (V → ℝ) ℝ)
    (n : ℕ) (x : Fin n → V → ℂ) :
    complexify p n x = ∑ τ : Fin n → V, (weight p ⟨n,τ⟩ : ℂ) * ∏ j, x j (τ j) := by
  simp only [complexify, _root_.sum_apply, _root_.smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

lemma complexify_real (p : FormalMultilinearSeries ℝ (V → ℝ) ℝ)
    (n : ℕ) (x : Fin n → V → ℝ) :
    complexify p n (fun j i => (x j i : ℂ)) = (p n x : ℂ) := by
  rw [complexify_apply, PositiveMultilinear.expansion]
  push_cast
  apply sum_congr rfl
  intro τ hτ
  exact mul_comm _ _

lemma complexify_norm_le (p : FormalMultilinearSeries ℝ (V → ℝ) ℝ)
    (hp : ∀ a, 0 ≤ weight p a) (n : ℕ) : ‖complexify p n‖ ≤ ‖p n‖ := by
  have hpos : 0 ≤ p n (fun _ _ => 1) :=
    PositiveMultilinear.nonneg _ (fun τ => hp ⟨n,τ⟩) _ (fun _ _ => zero_le_one)
  have hle : ‖complexify p n‖ ≤ p n (fun _ _ => 1) := by
    apply (complexify p n).opNorm_le_bound hpos
    intro x
    rw [complexify_apply, PositiveMultilinear.ones_eq_sum, sum_mul]
    refine (norm_sum_le _ _).trans (sum_le_sum ?_)
    intro τ hτ
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp ⟨n,τ⟩), norm_prod]
    apply mul_le_mul_of_nonneg_left _ (hp ⟨n,τ⟩)
    exact prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => norm_le_pi_norm (x j) (τ j))
  apply hle.trans
  rw [← Real.norm_of_nonneg hpos]
  apply (p n).le_opNorm _ |>.trans
  have hb : ‖(fun _ : V => (1 : ℝ))‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun _ => by simp)
  have hprod : (∏ _ : Fin n, ‖(fun _ : V => (1 : ℝ))‖) ≤ 1 := by
    exact prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hb)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod (norm_nonneg (p n))

lemma complexify_radius (p : FormalMultilinearSeries ℝ (V → ℝ) ℝ)
    (hp : ∀ a, 0 ≤ weight p a) : p.radius ≤ (complexify p).radius := by
  unfold FormalMultilinearSeries.radius
  apply iSup_le
  intro r
  apply iSup_le
  intro C
  apply iSup_le
  intro hC
  apply (complexify p).le_radius_of_bound C
  intro n
  exact (mul_le_mul_of_nonneg_right (complexify_norm_le p hp n) (by positivity)).trans (hC n)

lemma norm_lt_of_coordinates {r : ℝ} (hr : 0 < r) {x : V → ℂ}
    (hx : ∀ i, ‖x i‖ < r) : ‖x‖ < r := by
  exact (pi_norm_lt_iff hr).mpr hx

lemma complexify_hasSum (p : FormalMultilinearSeries ℝ (V → ℝ) ℝ)
    (hp : ∀ a, 0 ≤ weight p a) {r : ℝ} (hr : 0 < r)
    (hR : ENNReal.ofReal r < p.radius) (x : V → ℂ) (hx : ∀ i, ‖x i‖ < r) :
    HasSum (fun m : V → ℕ => (coefficient p m : ℂ) * ∏ i, x i ^ m i) ((complexify p).sum x) := by
  have hnorm := norm_lt_of_coordinates hr hx
  have he : ‖x‖ₑ < (complexify p).radius := by
    exact (show ‖x‖ₑ ≤ ENNReal.ofReal r by
      simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hnorm.le).trans_lt
        (hR.trans_le (complexify_radius p hp))
  apply hasSum_coefficients_of_complex_degrees p hp hr.le hR x (fun i => (hx i).le)
  exact ((complexify p).summable (mem_eball_zero_iff.mpr he)).hasSum.congr_fun
    (fun n => (complexify_apply p n (fun _ => x)).symm)

lemma complexify_sum_real (p : FormalMultilinearSeries ℝ (V → ℝ) ℝ)
    (x : V → ℝ) : (complexify p).sum (fun i => (x i : ℂ)) = (p.sum x : ℂ) := by
  simp only [FormalMultilinearSeries.sum, complexify_real, Complex.ofReal_tsum]

end BelowOne.PressureSeries

end

end OAI
