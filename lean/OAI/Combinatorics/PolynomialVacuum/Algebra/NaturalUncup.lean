import OAI.Combinatorics.PolynomialVacuum.Algebra.NaturalCup
import OAI.Combinatorics.PolynomialVacuum.Algebra.HomogeneousCupUnslide

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

theorem skipTwo_uncup_left (i : ℕ) (s : ℕ → Spin) (ab : Pair) :
    skipTwo (i+1) (replacePair s i (i+1) ab)=
      Function.update (skipTwo i s) i ab.1 := by
  funext k
  simp only [skipTwo,replacePair,Function.update_apply]
  split_ifs <;> congr 1 <;> omega

theorem skipTwo_uncup_right (i : ℕ) (s : ℕ → Spin) (ab : Pair) :
    skipTwo i (replacePair s (i+1) (i+1+1) ab)=
      Function.update (skipTwo i s) i ab.2 := by
  funext k
  simp only [skipTwo,replacePair,Function.update_apply]
  split_ifs <;> congr 1 <;> omega

theorem siteR_cup_unslide (i : ℕ) (x y : ℂ) :
    exchangeDenominator (T*x) y • (siteR i y x*cupLinear (i+1)) =
      exchangeDenominator y x • (siteR (i+1) (T*x) y*cupLinear i) := by
  ext W s
  simp only [siteR,pairLinear,cupLinear,Module.End.mul_apply,LinearMap.coe_mk,
    AddHom.coe_mk,pairAction,LinearMap.smul_apply,Pi.smul_apply,smul_eq_mul]
  simp only [replacePair_right,
    replacePair_other s (by omega : i+1+1≠i) (by omega : i+1+1≠i+1),
    replacePair_other s (by omega : i≠i+1) (by omega : i≠i+1+1),
    replacePair_left s (by omega : i+1≠i+1+1),
    skipTwo_uncup_left,skipTwo_uncup_right,Fintype.sum_prod_type,Finset.mul_sum]
  let w : Spin → ℂ := fun h => W (Function.update (skipTwo i s) i h)
  change (∑ a : Spin, ∑ b : Spin, exchangeDenominator (T*x) y *
    (exchangeNumerator y x (s i,s (i+1)) (a,b)*(cup (b,s (i+1+1))*w a))) =
    (∑ a : Spin, ∑ b : Spin, exchangeDenominator y x *
    (exchangeNumerator (T*x) y (s (i+1),s (i+1+1)) (a,b)*(cup (s i,a)*w b)))
  calc
    _ = ∑ h : Spin, homogeneousUncupLeft x y (s i) (s (i+1)) (s (i+1+1)) h*w h := by
      simp only [homogeneousUncupLeft,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _; ring
    _ = ∑ h : Spin, homogeneousUncupRight x y (s i) (s (i+1)) (s (i+1+1)) h*w h := by
      simp only [homogeneous_cup_unslide]
    _ = _ := by
      simp only [homogeneousUncupRight,Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _; ring

end PolynomialVacuumAlgebra

end OAI
