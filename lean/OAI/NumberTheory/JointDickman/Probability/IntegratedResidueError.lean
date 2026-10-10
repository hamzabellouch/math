import OAI.NumberTheory.JointDickman.Probability.ResidueProductError
import OAI.NumberTheory.JointDickman.Counting.IntervalEnergyError

namespace OAI

/-! # Integrating the residue-product errors against a Fourier profile -/

namespace JointDickman
open Finset MeasureTheory

theorem restricted_residue_product_linear_bound {ι : Type*} [Fintype ι]
    (P : ι → Prop) [DecidablePred P] (A B C D : ι → ℂ)
    {e₁ e₂ u v t : ℝ} (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (ht : 0 ≤ t)
    (h₁ : (∑ r, ‖A r-C r‖^2) ≤ (e₁*t)^2)
    (h₂ : (∑ r, ‖B r-D r‖^2) ≤ (e₂*t)^2)
    (hC : (∑ r, ‖C r‖^2) ≤ u^2) (hB : (∑ r, ‖B r‖^2) ≤ v^2) :
    ‖∑ r, if P r then A r*B r-C r*D r else 0‖ ≤ (e₁*v+u*e₂)*t := by
  have hh := restricted_residue_product_error_bound P A B C D h₁ h₂ hC hB
  rw [Real.sqrt_sq (mul_nonneg he₁ ht),Real.sqrt_sq (mul_nonneg he₂ ht),
    Real.sqrt_sq hu,Real.sqrt_sq hv] at hh
  exact hh.trans_eq (by ring)

theorem restricted_residue_integral_error {ι : Type*} [Fintype ι]
    (P : ι → Prop) [DecidablePred P] {l u e₁ e₂ m n : ℝ}
    (hlu : l ≤ u) (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) (hm : 0 ≤ m) (hn : 0 ≤ n)
    (W : ℝ → ℂ) (hW : Continuous W) (A B C D : ℝ → ι → ℂ)
    (h₁ : ∀ ξ ∈ Set.Icc l u, (∑ r, ‖A ξ r-C ξ r‖^2) ≤ (e₁*(1+|ξ|))^2)
    (h₂ : ∀ ξ ∈ Set.Icc l u, (∑ r, ‖B ξ r-D ξ r‖^2) ≤ (e₂*(1+|ξ|))^2)
    (hC : ∀ ξ ∈ Set.Icc l u, (∑ r, ‖C ξ r‖^2) ≤ m^2)
    (hB : ∀ ξ ∈ Set.Icc l u, (∑ r, ‖B ξ r‖^2) ≤ n^2) :
    ‖∫ ξ in l..u, W ξ*(∑ r, if P r then A ξ r*B ξ r-C ξ r*D ξ r else 0)‖ ≤
      (e₁*n+m*e₂)*(∫ ξ in l..u, ‖W ξ‖*(1+|ξ|)) := by
  let V : ℝ → ℝ := fun ξ => (e₁*n+m*e₂)*(‖W ξ‖*(1+|ξ|))
  have hV : Continuous V := continuous_const.mul (hW.norm.mul
    (continuous_const.add continuous_abs))
  calc
    _ ≤ ∫ ξ in l..u, V ξ := intervalIntegral.norm_integral_le_of_norm_le hlu
      (Filter.Eventually.of_forall (fun ξ hξ => by
        have hh := restricted_residue_product_linear_bound P (A ξ) (B ξ) (C ξ) (D ξ)
          he₁ he₂ hm hn (by positivity : 0 ≤ 1+|ξ|)
          (h₁ ξ ⟨hξ.1.le,hξ.2⟩) (h₂ ξ ⟨hξ.1.le,hξ.2⟩)
          (hC ξ ⟨hξ.1.le,hξ.2⟩) (hB ξ ⟨hξ.1.le,hξ.2⟩)
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (by dsimp [V]; ring)))
      (hV.intervalIntegrable l u)
    _ = _ := intervalIntegral.integral_const_mul _ _

end JointDickman

end OAI
