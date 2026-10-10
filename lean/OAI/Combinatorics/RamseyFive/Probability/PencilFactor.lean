import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreScalars

lemma pencil_factor {q : ℝ} (hq : 1  ≤  q) :
    (q^2+q+1)^2  ≤  9*q^4 ∧ (q+1)^2  ≤  4*q^2 := by
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq
  have hq2 : q  ≤  q^2 := by nlinarith
  have hp : q^2+q+1  ≤  3*q^2 := by nlinarith
  have hs := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ q^2+q+1) hp 2
  have ht := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ q+1) (by linarith : q+1 ≤ 2*q) 2
  constructor <;> nlinarith

theorem pair_power_two_hundred {q n δ N a χ E : ℝ}
    (hq : 1 ≤ q) (hn : 0<n) (hδ : 0 ≤ δ) (hN : 0 ≤ N) (ha : 0<a) (ha2 : a ≤ 2)
    (hmass : δ*N ≤ q)
    (hgeom : E*a^2  ≤  (q^4/n^2*Real.exp χ/(a/2)^100)*(q^2+q+1)^2*a^2+
      2*δ^2*N^2*(q+1)^2) :
    E*a^200  ≤  9*2^200*(q^4/n)^2*Real.exp χ+8*q^4*a^198 := by
  obtain ⟨hpoly,htwo⟩ := pencil_factor hq
  have hm2 : δ^2*N^2 ≤ q^2 := by
    have := pow_le_pow_left₀ (mul_nonneg hδ hN) hmass 2
    nlinarith
  have hnoise : 2*δ^2*N^2*(q+1)^2  ≤  8*q^4 := by
    calc
      _ = 2*(δ^2*N^2)*(q+1)^2 := by ring
      _ ≤ 2*q^2*(4*q^2) := mul_le_mul
        (mul_le_mul_of_nonneg_left hm2 (by norm_num)) htwo
        (sq_nonneg (q+1)) (by positivity)
      _ = _ := by ring
  have hmain : (q^4/n^2*Real.exp χ/(a/2)^100)*(q^2+q+1)^2*a^2  ≤
      (q^4/n^2*Real.exp χ/(a/2)^100)*(9*q^4)*a^2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg a)
    exact mul_le_mul_of_nonneg_left hpoly (by positivity)
  have hh := mul_le_mul_of_nonneg_right (hgeom.trans (add_le_add hmain hnoise))
    (pow_nonneg ha.le 198)
  have he : ((q^4/n^2*Real.exp χ/(a/2)^100)*(9*q^4)*a^2)*a^198 =
      9*2^100*(q^4/n)^2*Real.exp χ*a^100 := by
    field_simp
  have hp : a^2*a^198=a^200 := by rw [←pow_add]
  rw [add_mul,mul_assoc E (a^2),hp,he] at hh
  apply hh.trans
  apply add_le_add_left
  calc
    _  ≤  9*2^100*(q^4/n)^2*Real.exp χ*2^100 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le ha2 100) (by positivity)
    _ = 9*2^200*(q^4/n)^2*Real.exp χ := by ring

theorem degree_power_two_hundred {q m a D : ℝ} (hq : 1 ≤ q)
    (hm : 0 ≤ m) (hm2 : m ≤ 2) (ha : 0 ≤ a)
    (hgeom : D*a^2 ≤ 2*m*(q^2+q+1)*a+2*m^2*(q+1)) :
    D*a^200  ≤  12*q^2*a^199+16*q*a^198 := by
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq
  have hq2 : q ≤ q^2 := by nlinarith
  have hpoly : q^2+q+1 ≤ 3*q^2 := by nlinarith
  have hm4 : m^2 ≤ 4 := by nlinarith
  have hfirst : 2*m*(q^2+q+1)*a ≤ 12*q^2*a := by
    apply mul_le_mul_of_nonneg_right _ ha
    calc
      _  ≤  4*(3*q^2) := mul_le_mul (by linarith) hpoly (by positivity) (by norm_num)
      _ = _ := by ring
  have hsecond : 2*m^2*(q+1) ≤ 16*q := by
    calc
      _  ≤  8*(2*q) := mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
      _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_right (hgeom.trans (add_le_add hfirst hsecond)) (pow_nonneg ha 198)
  have heL : D*a^2*a^198=D*a^200 := by ring
  have heR : (12*q^2*a+16*q)*a^198=12*q^2*a^199+16*q*a^198 := by ring
  rwa [heL,heR] at hh

end SharpRamseyFive.ScoreScalars

end OAI
