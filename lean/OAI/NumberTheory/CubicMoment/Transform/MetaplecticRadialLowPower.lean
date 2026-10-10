import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRadialSelected

namespace OAI

/-! The radial lattice and the literal short inverse residue agree with
a power saving at the two source cutoffs. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
local notation "κ" => (1/10000:ℝ)

theorem LogarithmicWeightFamily.radial_model_low_power
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X R U C : ℝ),
      2 ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → R ≤ X^(51/100:ℝ) →
      X^(1/50:ℝ) ≤ C → C ≤ X^(13/100:ℝ) →
      (∀ r ∈ S, primary r ∧ Squarefree r ∧ R ≤ norm r) →
      (∀ r ∈ S, Y (w r) ≤ X) →
      (∑ r ∈ S, ‖α r‖) ≤ D*R*X^κ →
      ‖∑ r ∈ S, α r*(angularSmoothModel r 0 (W (w r)) U-
        metaplecticMain r 0 (W (w r)) U*metaplecticRadialEulerPartial r C)‖ ≤
        K*X^(41/50:ℝ) := by
  obtain ⟨B,K,E,hB,hK,hE,hbound⟩ := hW.radial_selected_error
    (by norm_num : 0 < κ) (by norm_num : 0 < κ) (by norm_num : κ ≤ 1/6)
  refine ⟨(K+E)*D,by positivity,?_⟩
  intro w S α X R U C hX hR hU hRU hRhi hClo hChi hS hY hmass
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hRp : 0 < R := by linarith
  have hUp : 0 < U := by linarith
  have hCp : 0 < C := (Real.rpow_pos_of_pos hXp _).trans_le hClo
  have hRX : R ≤ X := by rw [←hRU]; exact le_mul_of_one_le_right hRp.le hU
  have hCD := metaplectic_radial_cutoff_le_sqrt hX1 hRp hUp hRU hRhi hB hCp.le hChi
  have hb := hbound w S α X R U C hRp hUp hCp hCD hS hY
  have hfirst : (K*X^κ*R^(κ-1/6)*U^(1/3:ℝ))*(D*R*X^κ) ≤
      (K*D)*X^(41/50:ℝ) := by
    have hp := angular_model_level_power hR hU (by simpa only [hRU] using hRhi)
    rw [hRU] at hp
    calc
      _ = (K*D)*(X^κ*X^κ)*(R*(R^(κ-1/6)*U^(1/3:ℝ))) := by ring
      _ = (K*D)*X^(2*κ)*R^κ*(R^(5/6:ℝ)*U^(1/3:ℝ)) := by
        rw [angular_model_outer_power hRp hUp,←Real.rpow_add hXp]
        have he : κ+κ = 2*κ := by ring
        rw [he]
        ring
      _ ≤ (K*D)*X^(2*κ)*X^κ*X^(589/1000:ℝ) := by gcongr
      _ = (K*D)*((X^(2*κ)*X^κ)*X^(589/1000:ℝ)) := by ring
      _ = (K*D)*X^(3*κ+589/1000) := by
        rw [←Real.rpow_add hXp,←Real.rpow_add hXp]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)) (by positivity)
  have hsecond : (E*X^κ*U^(5/6:ℝ)*R^(-1/6:ℝ)*C^(-(99/100):ℝ))*(D*R*X^κ) ≤
      (E*D)*X^(41/50:ℝ) := by
    have hrscale : R*R^(-1/6:ℝ)*U^(5/6:ℝ) = X^(5/6:ℝ) := by
      rw [←hRU,Real.mul_rpow hRp.le hUp.le]
      congr 1
      calc
        _ = R^(1:ℝ)*R^(-1/6:ℝ) := by rw [Real.rpow_one]
        _ = R^((1:ℝ)+(-1/6)) := (Real.rpow_add hRp _ _).symm
        _ = _ := by norm_num
    calc
      _ = (E*D)*(R*R^(-1/6:ℝ)*U^(5/6:ℝ))*C^(-(99/100):ℝ)*(X^κ*X^κ) := by ring
      _ = (E*D)*(X^(5/6:ℝ)*C^(-(99/100):ℝ)*X^(2/10000:ℝ)) := by
        rw [hrscale,←Real.rpow_add hXp]
        norm_num
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (metaplectic_radial_euler_power hX1 hClo) (by positivity)
  apply hb.trans
  calc
    _ ≤ (K*X^κ*R^(κ-1/6)*U^(1/3:ℝ)+
        E*X^κ*U^(5/6:ℝ)*R^(-1/6:ℝ)*C^(-(99/100):ℝ))*(D*R*X^κ) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (K*X^κ*R^(κ-1/6)*U^(1/3:ℝ))*(D*R*X^κ)+
        (E*X^κ*U^(5/6:ℝ)*R^(-1/6:ℝ)*C^(-(99/100):ℝ))*(D*R*X^κ) := by ring
    _ ≤ (K*D)*X^(41/50:ℝ)+(E*D)*X^(41/50:ℝ) := add_le_add hfirst hsecond
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
