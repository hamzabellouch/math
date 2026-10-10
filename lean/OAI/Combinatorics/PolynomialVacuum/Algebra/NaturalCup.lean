import OAI.Combinatorics.PolynomialVacuum.Algebra.BraidTrain
import OAI.Combinatorics.PolynomialVacuum.Algebra.HomogeneousCupSlide

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

def skipTwo {α : Type*} (i : ℕ) (s : ℕ → α) : ℕ → α :=
  fun j => s (if j < i then j else j+2)

def skipOne {α : Type*} (i : ℕ) (s : ℕ → α) : ℕ → α :=
  fun j => s (if j < i then j else j+1)

noncomputable def cupLinear (i : ℕ) : Module.End ℂ (SpinTensor ℕ ℂ) where
  toFun W s := cup (s i,s (i+1))*W (skipTwo i s)
  map_add' W V := by ext s; simp [mul_add]
  map_smul' c W := by ext s; simp [mul_left_comm]

theorem skipTwo_before {i j : ℕ} (h : j+1 < i) (s : ℕ → Spin) (ab : Pair) :
    skipTwo i (replacePair s j (j+1) ab)=replacePair (skipTwo i s) j (j+1) ab := by
  funext k
  simp only [skipTwo,replacePair,Function.update_apply]
  split_ifs <;> congr 1 <;> omega

theorem skipTwo_after {i j : ℕ} (h : i+2 ≤ j) (s : ℕ → Spin) (ab : Pair) :
    skipTwo i (replacePair s j (j+1) ab)=replacePair (skipTwo i s) (j-2) (j-1) ab := by
  funext k
  simp only [skipTwo,replacePair,Function.update_apply]
  split_ifs <;> congr 1 <;> omega

theorem skipTwo_sliding (i : ℕ) (s : ℕ → Spin) (ab cd : Pair) :
    skipTwo i (replacePair (replacePair s i (i+1) ab) (i+1) (i+1+1) cd)=
      Function.update (skipTwo i s) i cd.2 := by
  funext k
  simp only [skipTwo,replacePair,Function.update_apply]
  split_ifs <;> congr 1 <;> omega

theorem skipTwo_slide_end (i : ℕ) (s : ℕ → Spin) :
    Function.update (skipTwo i s) i (s i)=skipTwo (i+1) s := by
  funext k
  simp only [skipTwo,Function.update_apply]
  split_ifs <;> congr 1 <;> omega

theorem siteR_cup_before {i j : ℕ} (h : j+1 < i) (x y : ℂ) :
    siteR j x y*cupLinear i=cupLinear i*siteR j x y := by
  ext W s
  simp only [siteR,pairLinear,cupLinear,Module.End.mul_apply,LinearMap.coe_mk,
    AddHom.coe_mk,pairAction]
  simp only [replacePair_other s (by omega : i≠j) (by omega : i≠j+1),
    replacePair_other s (by omega : i+1≠j) (by omega : i+1≠j+1),
    skipTwo_before h,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab _
  have hs1 : skipTwo i s j=s j := by simp [skipTwo,show j < i by omega]
  have hs2 : skipTwo i s (j+1)=s (j+1) := by simp [skipTwo,h]
  rw [hs1,hs2]
  ring

theorem siteR_cup_after {i j : ℕ} (h : i+2 ≤ j) (x y : ℂ) :
    siteR j x y*cupLinear i=cupLinear i*siteR (j-2) x y := by
  ext W s
  simp only [siteR,pairLinear,cupLinear,Module.End.mul_apply,LinearMap.coe_mk,
    AddHom.coe_mk,pairAction]
  simp only [replacePair_other s (by omega : i≠j) (by omega : i≠j+1),
    replacePair_other s (by omega : i+1≠j) (by omega : i+1≠j+1),
    skipTwo_after h,Finset.mul_sum]
  have hp : j-2+1=j-1 := by omega
  rw [hp]
  apply Finset.sum_congr rfl
  intro ab _
  have hs1 : skipTwo i s (j-2)=s j := by simp [skipTwo,show ¬j-2 < i by omega,show j-2+2=j by omega]
  have hs2 : skipTwo i s (j-1)=s (j+1) := by simp [skipTwo,show ¬j-1 < i by omega,show j-1+2=j+1 by omega]
  rw [hs1,hs2]
  ring

theorem siteR_cup_slide (i : ℕ) (x y : ℂ) :
    siteR i x y*siteR (i+1) (T*x) y*cupLinear i =
      (exchangeDenominator x y*exchangeDenominator (T*x) y) • cupLinear (i+1) := by
  ext W s
  simp only [siteR,pairLinear,cupLinear,Module.End.mul_apply,LinearMap.coe_mk,
    AddHom.coe_mk,pairAction,LinearMap.smul_apply]
  simp only [replacePair_right,
    replacePair_other s (by omega : i+1+1≠i) (by omega : i+1+1≠i+1)]
  have hl (ab cd : Pair) : replacePair (replacePair s i (i+1) ab) (i+1) (i+1+1) cd i=ab.1 := by
    rw [replacePair_other _ (by omega) (by omega),replacePair_left _ (by omega)]
  simp only [hl,skipTwo_sliding,Finset.mul_sum,Fintype.sum_prod_type]
  have hr (ab cd : Pair) : replacePair (replacePair s i (i+1) ab) (i+1) (i+1+1) cd (i+1)=cd.1 :=
    replacePair_left _ (by omega) _
  
  simp only [hr]
  let w : Spin → ℂ := fun h => W (Function.update (skipTwo i s) i h)
  have hh : (∑ a : Spin, ∑ b : Spin, ∑ c : Spin, ∑ h : Spin,
      exchangeNumerator x y (s i,s (i+1)) (a,b)*
      (exchangeNumerator (T*x) y (b,s (i+1+1)) (c,h)*(cup (a,c)*w h))) =
      ∑ h : Spin, homogeneousCupLeft x y (s i) (s (i+1)) (s (i+1+1)) h*w h := by
    simp only [homogeneousCupLeft,Finset.sum_mul]
    symm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro b _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro h _; ring
  change (∑ a : Spin, ∑ b : Spin, ∑ c : Spin, ∑ h : Spin,
    exchangeNumerator x y (s i,s (i+1)) (a,b)*
    (exchangeNumerator (T*x) y (b,s (i+1+1)) (c,h)*(cup (a,c)*w h))) = _
  rw [hh]
  simp only [homogeneous_cup_slide,homogeneousCupRight,ite_mul,
    mul_ite,zero_mul,mul_zero]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  simp only [w,skipTwo_slide_end,Pi.smul_apply,smul_eq_mul]
  ring

end PolynomialVacuumAlgebra

end OAI
