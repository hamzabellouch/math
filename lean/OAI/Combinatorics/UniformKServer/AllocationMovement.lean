import Mathlib
import OAI.Combinatorics.UniformKServer.AllocationOutputs

namespace OAI

                                         
section

/-! Companion §05, the exact non-wholesale hole identities and movement
bounds. The coefficient of the parent variation is exactly one. -/
namespace UniformKServer.AllocationOutputs
noncomputable section
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem sum_difference_le (a b : ι → ℝ) : |(∑ i, b i)-(∑ i, a i)| ≤ variation a b := by
  rw [←sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

omit [DecidableEq ι] in
theorem excess_difference (a b : ι → ℝ) (p q : ℝ) :
    |excess b q-excess a p| ≤ variation a b+|q-p| := by
  calc
    _ ≤ |((∑ i, b i)-q)-((∑ i, a i)-p)| := abs_max_sub_max_le_abs _ _ _
    _ = |((∑ i, b i)-(∑ i, a i))-(q-p)| := by congr 1; ring
    _ ≤ |(∑ i, b i)-(∑ i, a i)|+|q-p| := abs_sub _ _
    _ ≤ _ := add_le_add (sum_difference_le a b) le_rfl

omit [DecidableEq ι] in
theorem outputs_from_holes (a b x y : ι → ℝ) :
    variation (fun i => a i-x i) (fun i => b i-y i) ≤ variation a b+variation x y := by
  rw [variation,variation,variation,←sum_add_distrib]
  apply sum_le_sum
  intro i _
  convert abs_sub (b i-a i) (y i-x i) using 1
  congr 1
  ring

omit [DecidableEq ι] in
theorem scalar_vector_movement (a b : ι → ℝ) (p q : ℝ)
    (hq : 0 ≤ q) (ha : ∀ i, 0 ≤ a i) :
    variation (fun i => p*a i) (fun i => q*b i) ≤
      q*variation a b+|q-p| *(∑ i, a i) := by
  rw [variation,variation,mul_sum,mul_sum,←sum_add_distrib]
  apply sum_le_sum
  intro i _
  calc
    _ = |q*(b i-a i)+(q-p)*a i| := by congr 1; ring
    _ ≤ |q*(b i-a i)|+|(q-p)*a i| := abs_add_le _ _
    _ = _ := by rw [abs_mul,abs_mul,abs_of_nonneg hq,abs_of_nonneg (ha i)]

omit [DecidableEq ι] in
theorem rule_one_movement (d₀ d₁ α₀ α₁ : ι → ℝ) (q₀ q₁ : ℝ)
    (hα : ∀ i, 0 ≤ α₀ i) (hsum : (∑ i, α₀ i)=1) :
    variation (ruleOne d₀ α₀ q₀) (ruleOne d₁ α₁ q₁) ≤
      |q₁-q₀|+2*variation d₀ d₁+excess d₁ q₁*variation α₀ α₁ := by
  have hm := outputs_from_holes d₀ d₁ (fun i => excess d₀ q₀*α₀ i)
    (fun i => excess d₁ q₁*α₁ i)
  have hh := scalar_vector_movement α₀ α₁ (excess d₀ q₀) (excess d₁ q₁)
    (excess_nonneg _ _) hα
  rw [hsum,mul_one] at hh
  have he := excess_difference d₀ d₁ q₀ q₁
  change variation (ruleOne d₀ α₀ q₀) (ruleOne d₁ α₁ q₁) ≤ _ at hm
  linarith

def sideTotal (a : ι → ℝ) (o : ι) : ℝ := ∑ i ∈ univ.erase o, a i

def sideVariation (a b : ι → ℝ) (o : ι) : ℝ := ∑ i ∈ univ.erase o, |b i-a i|

def holesTwo (R : ℝ) (ω : ι → ℝ) (o i : ι) : ℝ :=
  if i=o then max (R-sideTotal ω o) 0 else ω i

theorem side_total_difference (a b : ι → ℝ) (o : ι) :
    |sideTotal b o-sideTotal a o| ≤ sideVariation a b o := by
  rw [sideTotal,sideTotal,←sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

theorem side_variation_le (a b : ι → ℝ) (o : ι) :
    sideVariation a b o ≤ variation a b :=
  sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun i _ _ => abs_nonneg (b i-a i))

theorem holes_two_movement (a b : ι → ℝ) (p q : ℝ) (o : ι) :
    variation (holesTwo p a o) (holesTwo q b o) ≤ |q-p|+2*sideVariation a b o := by
  rw [variation,←sum_erase_add _ _ (mem_univ o)]
  have hs : (∑ i ∈ univ.erase o, |holesTwo q b o i-holesTwo p a o i|) =
      sideVariation a b o := by
    apply sum_congr rfl
    intro i hi
    simp only [holesTwo,ite_eq_right (ne_of_mem_erase hi)]
  rw [hs]
  simp only [holesTwo,ite_true]
  have hm := abs_max_sub_max_le_abs (q-sideTotal b o) (p-sideTotal a o) 0
  have he : (q-sideTotal b o)-(p-sideTotal a o) = (q-p)-(sideTotal b o-sideTotal a o) := by ring
  rw [he] at hm
  have ht := (abs_sub (q-p) (sideTotal b o-sideTotal a o)).trans
    (add_le_add le_rfl (side_total_difference a b o))
  linarith

theorem rule_two_holes (d w : ι → ℝ) (q D : ℝ) (o i : ι)
    (hw : 0 ≤ sideTotal (fun j => D*w j) o) :
    d i-ruleTwo d w q D o i = holesTwo (excess d q) (fun j => D*w j) o i := by
  by_cases hi : i=o
  · subst i
    simp only [ruleTwo,holesTwo,ite_true]
    have he : (∑ i, d i)-q-sideTotal (fun j => D*w j) o =
        d o-(q-∑ j ∈ univ.erase o, (d j-D*w j)) := by
      rw [←sum_erase_add _ _ (mem_univ o),sum_sub_distrib]
      unfold sideTotal
      ring
    have hm : d o-min (d o) (q-∑ j ∈ univ.erase o, (d j-D*w j)) =
        max (d o-(q-∑ j ∈ univ.erase o, (d j-D*w j))) 0 := by
      rcases le_total (d o) (q-∑ j ∈ univ.erase o, (d j-D*w j)) with h|h
      · rw [min_eq_left h,max_eq_right (sub_nonpos.mpr h),sub_self]
      · rw [min_eq_right h,max_eq_left (sub_nonneg.mpr h)]
    rw [hm,←he]
    unfold excess
    by_cases hh : 0 ≤ (∑ i, d i)-q
    · rw [max_eq_left hh]
    · have hz : (∑ i, d i)-q ≤ 0 := le_of_not_ge hh
      rw [max_eq_right hz,max_eq_right (by linarith),max_eq_right (by linarith)]
  · simp only [ruleTwo,holesTwo,ite_eq_right hi]
    ring

theorem rule_two_movement (d₀ d₁ w₀ w₁ : ι → ℝ) (q₀ q₁ D₀ D₁ : ℝ) (o : ι)
    (hD₀ : 0 ≤ D₀) (hD₁ : 0 ≤ D₁) (hw₀ : ∀ i, 0 ≤ w₀ i) (hw₁ : ∀ i, 0 ≤ w₁ i) :
    variation (ruleTwo d₀ w₀ q₀ D₀ o) (ruleTwo d₁ w₁ q₁ D₁ o) ≤
      |q₁-q₀|+2*variation d₀ d₁+2*D₁*variation w₀ w₁+2*|D₁-D₀| *(∑ i, w₀ i) := by
  have hω₀ : 0 ≤ sideTotal (fun i => D₀*w₀ i) o :=
    sum_nonneg (fun i _ => mul_nonneg hD₀ (hw₀ i))
  have hω₁ : 0 ≤ sideTotal (fun i => D₁*w₁ i) o :=
    sum_nonneg (fun i _ => mul_nonneg hD₁ (hw₁ i))
  have he₀ : ruleTwo d₀ w₀ q₀ D₀ o = fun i => d₀ i-holesTwo (excess d₀ q₀) (fun j => D₀*w₀ j) o i := by
    funext i
    linarith [rule_two_holes d₀ w₀ q₀ D₀ o i hω₀]
  have he₁ : ruleTwo d₁ w₁ q₁ D₁ o = fun i => d₁ i-holesTwo (excess d₁ q₁) (fun j => D₁*w₁ j) o i := by
    funext i
    linarith [rule_two_holes d₁ w₁ q₁ D₁ o i hω₁]
  rw [he₀,he₁]
  have hm := outputs_from_holes d₀ d₁ (holesTwo (excess d₀ q₀) (fun j => D₀*w₀ j) o)
    (holesTwo (excess d₁ q₁) (fun j => D₁*w₁ j) o)
  have hh := holes_two_movement (fun j => D₀*w₀ j) (fun j => D₁*w₁ j) (excess d₀ q₀) (excess d₁ q₁) o
  have hs := side_variation_le (fun j => D₀*w₀ j) (fun j => D₁*w₁ j) o
  have hv := scalar_vector_movement w₀ w₁ D₀ D₁ hD₁ hw₀
  have he := excess_difference d₀ d₁ q₀ q₁
  nlinarith

end
end UniformKServer.AllocationOutputs

end

end OAI
