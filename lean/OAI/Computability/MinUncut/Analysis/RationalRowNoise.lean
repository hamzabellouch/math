import Mathlib
import OAI.Computability.MinUncut.Estimates.Convolution

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.RowNoise
attribute [local instance] Classical.propDecidable
variable {R W : Type*} [Fintype R] [Fintype W] [DecidableEq W]

def rationalRowDensity (a : ℚ) (b c : W) : ℚ :=
  (1-a)*(if c=b then (Fintype.card W:ℚ) else 0)+a

def rationalDensity (a : ℚ) (B C : R → W) : ℚ :=
  ∏ r, rationalRowDensity a (B r) (C r)

lemma rationalRowDensity_cast (a : ℚ) (b c : W) :
    (rationalRowDensity a b c:ℝ)=rowDensity a b c := by
  by_cases h : c=b <;> simp [rationalRowDensity,rowDensity,h]

lemma rationalDensity_cast (a : ℚ) (B C : R → W) :
    (rationalDensity a B C:ℝ)=density a B C := by
  simp only [rationalDensity,density,Rat.cast_prod,rationalRowDensity_cast]

lemma rationalDensity_nonneg {a : ℚ} (ha : 0≤a) (ha1 : a≤1) (B C : R → W) :
    0≤rationalDensity a B C := by
  apply Finset.prod_nonneg
  intro r _
  unfold rationalRowDensity
  split_ifs <;> positivity

variable [Nonempty W]
lemma rationalRowDensity_mean (a : ℚ) (b : W) : (𝔼 c, rationalRowDensity a b c)=1 := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [rationalRowDensity,Finset.sum_add_distrib,← Finset.mul_sum,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hn : (Fintype.card W:ℚ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
  ring

lemma rational_expect_prod [DecidableEq R] {A : R → Type*} [∀ r, Fintype (A r)]
    (f : ∀ r, A r → ℚ) : (𝔼 x : ∀ r, A r, ∏ r, f r (x r))=∏ r, 𝔼 a, f r a := by
  simp only [Fintype.expect_eq_sum_div_card,Fintype.card_pi]
  rw [← Fintype.prod_sum,Nat.cast_prod,Finset.prod_div_distrib]

lemma rationalDensity_mean [DecidableEq R] (a : ℚ) (B : R → W) :
    (𝔼 C, rationalDensity a B C)=1 := by
  unfold rationalDensity
  rw [rational_expect_prod]
  simp only [rationalRowDensity_mean,Finset.prod_const_one]
end MinUncut.RowNoise

end
end

end OAI
