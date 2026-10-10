import OAI.NumberTheory.CubicMoment.Estimates.TripleIndexCount

namespace OAI

/-! A triple with a small bilinear ratio has only logarithmic spread in
its three smooth norm indices. This is the counting input for flat
exceptional boxes. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def tripleNormScale (k : Fin 3 → ℕ) (i : Fin 3) : ℝ := (4/3:ℝ)^(k i)/2

lemma tripleNormScale_pos (k : Fin 3 → ℕ) (i : Fin 3) : 0 < tripleNormScale k i := by
  unfold tripleNormScale
  positivity

lemma tripleNormScale_prod_le (k : Fin 3 → ℕ) {B : ℝ}
    (hB : ∀ i, tripleNormScale k i ≤ B) (i : Fin 3) :
    (∏ j, tripleNormScale k j) ≤ tripleNormScale k i*B^2 := by
  rw [←Finset.mul_prod_erase _ (tripleNormScale k) (Finset.mem_univ i)]
  apply mul_le_mul_of_nonneg_left _ (tripleNormScale_pos k i).le
  calc
    _ ≤ ∏ _j ∈ Finset.univ.erase i, B := Finset.prod_le_prod₀
      (fun j _ => (tripleNormScale_pos k j).le) (fun j _ => hB j)
    _ = B^2 := by simp

lemma tripleNormScale_ratio_bound (k : Fin 3 → ℕ) {B L : ℝ} (G : ℕ)
    (hL : 0 ≤ L) (hB : ∀ i, tripleNormScale k i ≤ B)
    (hflat : B^3 ≤ (∏ i, tripleNormScale k i)*L^G) (i j : Fin 3) :
    tripleNormScale k i ≤ tripleNormScale k j*L^G := by
  have hBp : 0 < B := (tripleNormScale_pos k 0).trans_le (hB 0)
  apply (hB i).trans
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hBp)).mp
  calc
    B^2*B = B^3 := by ring
    _ ≤ (∏ i, tripleNormScale k i)*L^G := hflat
    _ ≤ (tripleNormScale k j*B^2)*L^G :=
      mul_le_mul_of_nonneg_right (tripleNormScale_prod_le k hB j) (pow_nonneg hL G)
    _ = _ := by ring

theorem tripleNormScale_index_spread (k : Fin 3 → ℕ) {B L : ℝ} (G : ℕ)
    (hL : 1 ≤ L) (hB : ∀ i, tripleNormScale k i ≤ B)
    (hflat : B^3 ≤ (∏ i, tripleNormScale k i)*L^G) (i j : Fin 3) :
    k i ≤ k j+⌈(G:ℝ)*Real.log L/Real.log (4/3:ℝ)⌉₊ := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hr : 0 < Real.log (4/3:ℝ) := Real.log_pos (by norm_num)
  have he (a : Fin 3) : Real.log (tripleNormScale k a) =
      (k a:ℝ)*Real.log (4/3:ℝ)-Real.log 2 := by
    rw [tripleNormScale,Real.log_div (pow_pos (by norm_num : (0:ℝ) < 4/3) _).ne'
      (by norm_num),Real.log_pow]
  have hratio := Real.log_le_log (tripleNormScale_pos k i)
    (tripleNormScale_ratio_bound k G hLp.le hB hflat i j)
  rw [Real.log_mul (tripleNormScale_pos k j).ne' (pow_pos hLp G).ne',
    he i,he j,Real.log_pow] at hratio
  have hceil := Nat.le_ceil ((G:ℝ)*Real.log L/Real.log (4/3:ℝ))
  have hc : (k i:ℝ) ≤ (k j:ℝ)+
      (⌈(G:ℝ)*Real.log L/Real.log (4/3:ℝ)⌉₊:ℝ) := by
    have hh := (div_le_iff₀ hr).mp hceil
    nlinarith
  exact_mod_cast hc

end CubicFirstMoment

end

end OAI
