import OAI.NumberTheory.CubicMoment.Transform.MetaplecticLogCounting
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticLongCard

namespace OAI

/-! The counting bound at the source small-level cutoff X^(13/100),
including the actual finite dyads and original logarithmic weights. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
local notation "κ" => (1/10000:ℝ)

theorem LogarithmicWeightFamily.metaplectic_long_small_power
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ}
    (hW : LogarithmicWeightFamily Y W) {B D : ℝ} (hB : 1 ≤ B) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (ℓ : ℤ) (X R U : ℝ),
      2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U → R*U = X →
      (∀ r ∈ S, primary r) → (∀ r ∈ S, Y (w r) ≤ X) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → W (w r) x = 0) →
      (∑ r ∈ S, ‖α r‖) ≤ D*R*X^κ →
      ‖∑ r ∈ S, α r*metaplecticLongCompletion r ℓ (W (w r)) U
        (X^(13/100:ℝ)) (X^2)‖ ≤ K*X^(41/50:ℝ) := by
  obtain ⟨A,hA,hbound⟩ := hW.metaplectic_long_counting
    (by norm_num : 0 < κ) (by norm_num : κ ≤ 1/2) (by norm_num : 0 < κ)
  obtain ⟨J,hJ,hcard⟩ := metaplecticLongDyads_small_power (by norm_num : 0 < κ)
  let T : ℝ := (2⁻¹:ℝ)^(-3/2+κ)
  refine ⟨A*B*T*J*D,by dsimp [T]; positivity,?_⟩
  intro w S α ℓ X R U hX hBX hR hU hRU hS hY hcut hmass
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hUp : 0 < U := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hUX : U ≤ X := by rw [←hRU]; exact le_mul_of_one_le_left hUp.le hR
  have hBU : B*U ≤ X^2 := by nlinarith [mul_le_mul hBX hUX hUp.le hXp.le]
  have hc : ((metaplecticLongDyads (X^(13/100:ℝ)) (X^2)).card:ℝ) ≤ J*X^(2*κ) := by
    apply (hcard _ _ (one_le_pow₀ hX1)).trans_eq
    rw [←Real.rpow_natCast X 2,←Real.rpow_mul hXp.le]
    congr 2
  have hcp : (X^(13/100:ℝ)/2)^(-3/2+κ) = T*X^((13/100)*(-3/2+κ)) := by
    rw [div_eq_mul_inv,Real.mul_rpow (Real.rpow_nonneg hXp.le _) (by norm_num),
      ←Real.rpow_mul hXp.le]
    exact mul_comm _ _
  have hp : X^κ*X^((13/100)*(-3/2+κ))*X^(2*κ)*X^κ*X =
      X^(1+4*κ+(13/100)*(-3/2+κ)) := by
    conv_lhs => rhs; rw [←Real.rpow_one X]
    rw [←Real.rpow_add hXp,←Real.rpow_add hXp,←Real.rpow_add hXp,←Real.rpow_add hXp]
    congr 1
    ring
  have hb := hbound w S α ℓ X U B (X^(13/100:ℝ)) (X^2)
    hX1 hUp hB0 (by positivity) hBU hS hY hcut
  apply hb.trans
  rw [hcp]
  calc
    _ ≤ A*B*U*X^κ*(T*X^((13/100)*(-3/2+κ)))*(J*X^(2*κ))*(D*R*X^κ) := by gcongr
    _ = (A*B*T*J*D)*X^(1+4*κ+(13/100)*(-3/2+κ)) := by
      calc
        _ = (A*B*T*J*D)*(X^κ*X^((13/100)*(-3/2+κ))*X^(2*κ)*X^κ*(R*U)) := by ring
        _ = _ := by rw [hRU,hp]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)) (by dsimp [T]; positivity)

end CubicFirstMoment

end

end OAI
