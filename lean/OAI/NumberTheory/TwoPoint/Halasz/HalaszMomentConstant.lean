import OAI.NumberTheory.TwoPoint.Halasz.HalaszLogWeightCost
import OAI.NumberTheory.TwoPoint.Halasz.HalaszSelectedDoubleMoment

namespace OAI

/-! The apparently large complete-system constants become a fixed sixth
power after taking the selected double-moment root. -/
namespace TwoPointCorrelations

lemma halasz_moment_constant_nat {k : ℕ} (hk : 2≤k) (R₀ : ℕ) :
    (32*halaszSelectedMoment k)^k*(R₀+k+32)^(512*k^4)*
      (8^(k+2)*(halaszSelectedMoment k+k+1))^k ≤
    (R₀+k+32)^(6*(2*halaszSelectedMoment k*halaszSelectedMoment k)) := by
  let R := R₀+k+32
  let r := halaszSelectedMoment k
  have hRk : k≤R := by dsimp [R]; omega
  have hR32 : 32≤R := by dsimp [R]; omega
  have hR1 : 1≤R := by omega
  have hkk : k≤k^2 := by nlinarith
  have hr : r≤11*k^2 := by dsimp [r,halaszSelectedMoment]; nlinarith only [hkk]
  have hrlo : 10*k^2≤r := by dsimp [r,halaszSelectedMoment]; nlinarith
  have hR2 : k^2≤R^2 := Nat.pow_le_pow_left hRk 2
  have h32 : 1024≤R^2 := by simpa using Nat.pow_le_pow_left hR32 2
  have hbase : 32*r≤R^4 := by
    calc
      _ ≤ 352*k^2 := by nlinarith only [hr]
      _ ≤ 1024*k^2 := by omega
      _ ≤ R^2*k^2 := Nat.mul_le_mul_right _ h32
      _ ≤ R^2*R^2 := Nat.mul_le_mul_left _ hR2
      _ = _ := by ring
  have hshort : r+k+1≤R^3 := by
    have hkpos : 1≤k^2 := by nlinarith
    calc
      _ ≤ 13*k^2 := by nlinarith only [hr,hkk,hkpos]
      _ ≤ 32*k^2 := by omega
      _ ≤ R*k^2 := Nat.mul_le_mul_right _ hR32
      _ ≤ R*R^2 := Nat.mul_le_mul_left _ hR2
      _ = _ := by ring
  have hcost : 8^(k+2)*(r+k+1)≤R^(k+5) := by
    calc
      _ ≤ R^(k+2)*R^3 := Nat.mul_le_mul
        (Nat.pow_le_pow_left (by omega : 8≤R) _) hshort
      _ = _ := by rw [← pow_add]
  have hk4 : k^2≤k^4 := by
    have hh := Nat.pow_le_pow_right (by omega : 1≤k) (by norm_num : 2≤4)
    exact hh
  have hr2 : 100*k^4≤r^2 := by
    have hh := Nat.pow_le_pow_left hrlo 2
    nlinarith only [hh]
  have he : 4*k+512*k^4+(k+5)*k≤6*(2*r*r) := by
    nlinarith only [hkk,hk4,hr2]
  calc
    _ ≤ (R^4)^k*R^(512*k^4)*(R^(k+5))^k :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hbase k))
        (Nat.pow_le_pow_left hcost k)
    _ = R^(4*k+512*k^4+(k+5)*k) := by rw [← pow_mul,← pow_mul,← pow_add,← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right hR1 he

lemma halasz_moment_constant_root {k : ℕ} (hk : 2≤k) (R₀ : ℕ) :
    ((32*(halaszSelectedMoment k:ℝ))^k*(R₀+k+32:ℝ)^(512*k^4)*
      (halaszLogWeightCost k (halaszSelectedMoment k))^k)^
        (((2*halaszSelectedMoment k*halaszSelectedMoment k:ℕ):ℝ)⁻¹) ≤
      (R₀+k+32:ℝ)^6 := by
  have hp : 0<2*halaszSelectedMoment k*halaszSelectedMoment k := by
    have hr := halasz_selected_moment_pos hk
    positivity
  have hB : (32*(halaszSelectedMoment k:ℝ))^k*(R₀+k+32:ℝ)^(512*k^4)*
      (halaszLogWeightCost k (halaszSelectedMoment k))^k ≤
      (R₀+k+32:ℝ)^(6*(2*halaszSelectedMoment k*halaszSelectedMoment k)) := by
    dsimp only [halaszLogWeightCost]
    exact_mod_cast halasz_moment_constant_nat hk R₀
  apply (Real.rpow_inv_le_iff_of_pos (by dsimp only [halaszLogWeightCost]; positivity) (by positivity)
    (by exact_mod_cast hp)).mpr
  simpa only [Real.rpow_natCast,← pow_mul] using hB

end TwoPointCorrelations

end OAI
