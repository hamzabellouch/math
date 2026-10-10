import OAI.Analysis.LipschitzFree.PortGraphs
import OAI.Analysis.LipschitzFree.Model

namespace OAI

/-!
# Quantitative block parameters and strict variation bounds
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree.BlockParameters

def L (p : ℕ) := 10*p
def R (p : ℕ) := 3*L p
def K (p : ℕ) := 10*p*(R p+1)
def D (p : ℕ) := K p+2*L p+5
def B (p : ℕ) := 4*R p+D p
def V (p : ℕ) := 1+4*p*B p

def generators (p : ℕ) := 20*V p+2
def degree (p : ℕ) := 2*generators p
def Q (p : ℕ) := degree p^(2*L p+1)
def H (p : ℕ) := degree p^(D p+1)
def colors (p : ℕ) := 2*degree p*Q p*H p+1

theorem L_pos {p : ℕ} (hp : 1 ≤ p) : 0 < L p := by dsimp [L]; omega

theorem R_pos {p : ℕ} (hp : 1 ≤ p) : 0 < R p := by dsimp [R]; exact Nat.mul_pos (by omega) (L_pos hp)

theorem K_pos {p : ℕ} (hp : 1 ≤ p) : 0 < K p := by dsimp [K]; positivity

theorem small_radius {p : ℕ} (hp : 1 ≤ p) : 2*L p < R p := by dsimp [R]; have := L_pos hp; omega

theorem L_le_K (p : ℕ) : L p ≤ K p := by
  dsimp [L,K]
  have : 1 ≤ R p+1 := by omega
  exact Nat.le_mul_of_pos_right _ this

theorem compatibility_cap (p : ℕ) : K p+2*L p+1 < D p := by dsimp [D]; omega

theorem B_formula (p : ℕ) : (B p : ℝ) = blockBound p := by
  norm_num [B,D,K,R,L,blockBound]
  ring

theorem degree_ge (p : ℕ) : 4 ≤ degree p := by dsimp [degree,generators]; omega

theorem degree_variation (p : ℕ) : 20*V p < degree p := by dsimp [degree,generators]; omega

theorem Q_pos (p : ℕ) : 0 < Q p := by dsimp [Q]; exact pow_pos (by have := degree_ge p; omega) _

theorem H_pos (p : ℕ) : 0 < H p := by dsimp [H]; exact pow_pos (by have := degree_ge p; omega) _

theorem colors_pos (p : ℕ) : 0 < colors p := by dsimp [colors]; omega

theorem colors_large (p : ℕ) : 2*degree p*Q p*H p < colors p := by dsimp [colors]; omega

theorem bump_loss {p : ℕ} (hp : 1 ≤ p) :
    (L p : ℝ)/(K p : ℝ)*(2*(p : ℝ)*(R p : ℝ)+1) ≤ (L p : ℝ)/4 := by
  have hp' : 1 ≤ (p : ℝ) := by exact_mod_cast hp
  have hR : 0 ≤ (R p : ℝ) := Nat.cast_nonneg _
  have hpR : 0 ≤ (p : ℝ)*(R p : ℝ) := mul_nonneg (by positivity) hR
  have hK : 0 < (K p : ℝ) := by exact_mod_cast K_pos hp
  have hKn : (K p : ℝ) = 10*(p : ℝ)*((R p : ℝ)+1) := by simp [K]
  have hnum : 4*(2*(p : ℝ)*(R p : ℝ)+1) ≤ (K p : ℝ) := by rw [hKn]; nlinarith
  have hL : 0 ≤ (L p : ℝ) := Nat.cast_nonneg _
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ hK).mpr
  nlinarith [mul_le_mul_of_nonneg_left hnum hL]

end DiscreteFree.BlockParameters

end

end OAI
