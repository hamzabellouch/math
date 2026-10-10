import OAI.NumberTheory.CubicMoment.Transform.MetaplecticLongSieve
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticLongCard
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCutoffPowers

namespace OAI

/-! The actual long inverse tail in the large-level branch of low Type I.
The source cutoff is X^(1/50); the completion cutoff is the harmless X^2. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
local notation "κ" => (1/10000:ℝ)

theorem LogarithmicWeightFamily.metaplectic_long_large_power
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ}
    (hW : LogarithmicWeightFamily Y W) {B D : ℝ} (hB : 1 ≤ B) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (ℓ : ℤ) (X R U : ℝ),
      2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U → R*U = X →
      X^(2/5:ℝ) ≤ R → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, Y (w r) ≤ X) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → W (w r) x = 0) →
      (∑ r ∈ S, ‖α r‖^2) ≤ D*R*X^(2*κ) →
      ‖∑ r ∈ S, α r*metaplecticLongCompletion r ℓ (W (w r)) U
        (X^(1/50:ℝ)) (X^2)‖ ≤ K*X^(41/50:ℝ) := by
  obtain ⟨A,hA,hbound⟩ := hW.metaplectic_long_sieve
    (by norm_num : 0 < κ) (by norm_num : κ ≤ 1) (by norm_num : 0 < κ)
  obtain ⟨J,hJ,hcard⟩ := metaplecticLongDyads_small_power (by norm_num : 0 < κ)
  let C : ℝ := A*J^2*D*B*(2*B)^κ
  let H : ℝ := 3*(2+8*B+(16*B)^(2/3:ℝ))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨Real.sqrt (C*H),Real.sqrt_nonneg _,?_⟩
  intro w S α ℓ X R U hX hBX hR hU hRU hRlo hRhi hS hY hcut henergy
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hRp : 0 < R := by linarith
  have hUp : 0 < U := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hUX : U ≤ X := by rw [←hRU]; exact le_mul_of_one_le_left hUp.le hR
  have hBU : B*U ≤ X^2 := by nlinarith [mul_le_mul hBX hUX hUp.le hXp.le]
  have hc : ((metaplecticLongDyads (X^(1/50:ℝ)) (X^2)).card:ℝ) ≤ J*X^(2*κ) := by
    apply (hcard _ _ (one_le_pow₀ hX1)).trans_eq
    rw [←Real.rpow_natCast X 2,←Real.rpow_mul hXp.le]
    congr 2
  have hn : (2*R*(B*U))^κ = (2*B)^κ*X^κ := by
    rw [show 2*R*(B*U) = (2*B)*(R*U) by ring,hRU,Real.mul_rpow (by positivity) hXp.le]
  have hf : (X^2)^(4*κ) = X^(8*κ) := by
    rw [←Real.rpow_natCast X 2,←Real.rpow_mul hXp.le]
    congr 1
    ring
  have hpow : (X^(2*κ))^2 = X^(4*κ) := by
    rw [←Real.rpow_mul_natCast hXp.le]
    congr 1
    norm_num
  have hp : X^(4*κ)*X^(2*κ)*X^κ*X^(8*κ)*X^(2*κ) = X^(17*κ) := by
    rw [←Real.rpow_add hXp,←Real.rpow_add hXp,←Real.rpow_add hXp,←Real.rpow_add hXp]
    congr 1
    ring
  let Q : ℝ := 2*R+8*B*U/(X^(1/50:ℝ))^3+(16*B*X/(X^(1/50:ℝ))^3)^(2/3:ℝ)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hb := hbound w S X (2*R) U B (X^(1/50:ℝ)) (X^2)
    hX1 (by linarith) hUp hB0 (by positivity) (one_le_pow₀ hX1) hBU hS hY hcut α ℓ
  have hsq : ‖∑ r ∈ S, α r*metaplecticLongCompletion r ℓ (W (w r)) U
      (X^(1/50:ℝ)) (X^2)‖^2 ≤ (C*H)*X^(41/25:ℝ) := by
    apply hb.trans
    have hshape : 2*R+8*B*U/(X^(1/50:ℝ))^3+
        (8*(2*R)*B*U/(X^(1/50:ℝ))^3)^(2/3:ℝ) = Q := by
      dsimp [Q]
      rw [show 8*(2*R)*B*U = 16*B*(R*U) by ring,hRU]
    rw [hshape]
    calc
      _ ≤ A*(J*X^(2*κ))^2*X^(2*κ)*(2*R*(B*U))^κ*(B*U)*(X^2)^(4*κ)*Q*
          (D*R*X^(2*κ)) := by gcongr
      _ = C*X^(17*κ)*(X*Q) := by
        rw [mul_pow,hpow,hn,hf]
        calc
          _ = (A*J^2*D*B*(2*B)^κ)*(X^(4*κ)*X^(2*κ)*X^κ*X^(8*κ)*X^(2*κ))*((R*U)*Q) := by ring
          _ = _ := by rw [hp,hRU]
      _ ≤ C*X^(17*κ)*(H*X^(122/75:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact metaplectic_large_sieve_fixed_support hX1 hRp hUp.le hB0 hRU hRlo hRhi
      _ = (C*H)*X^(17*κ+122/75) := by rw [Real.rpow_add hXp]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)) (mul_nonneg hC hH)
  have htarget : (Real.sqrt (C*H)*X^(41/50:ℝ))^2 = (C*H)*X^(41/25:ℝ) := by
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hC hH),←Real.rpow_mul_natCast hXp.le]
    norm_num
  exact (sq_le_sq₀ (_root_.norm_nonneg _) (by positivity)).mp (hsq.trans_eq htarget.symm)

end CubicFirstMoment

end

end OAI
