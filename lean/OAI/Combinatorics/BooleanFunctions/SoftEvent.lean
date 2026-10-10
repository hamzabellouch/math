import OAI.Combinatorics.BooleanFunctions.FiniteMoments
import OAI.Combinatorics.BooleanFunctions.MomentTransfer

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace SoftEvent
attribute [local instance] Classical.propDecidable
open FiniteMoments MomentTransfer
variable {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α]

omit [Nonempty α] in
theorem average_div_const (f : α → ℝ) (c : ℝ) :
    average (fun a => f a/c) = average f/c := by
  simp only [div_eq_mul_inv,average_mul_const]

def rawMoments (T : α → ℝ) (w : ι → α → ℝ) (k : Fin 3) (i : ι) : ℝ :=
  average (fun a => w i a*(T a)^(k:ℕ))

omit [Nonempty α] in
theorem weighted_shifted_sq (w : ι → α → ℝ) (hw : ∀ i, average (w i) ≠ 0)
    (T : ι → α → ℝ) (c : ℝ) :
    average (fun x : ι → α => (∏ i, w i (x i))*(c+∑ i, T i (x i))^2) =
      (∏ i, average (w i)) * ((c+∑ i, average (fun a => w i a*T i a)/average (w i))^2 +
        ∑ i, (average (fun a => w i a*(T i a)^2)/average (w i) -
          (average (fun a => w i a*T i a)/average (w i))^2)) := by
  let r := fun i a => w i a/average (w i)
  have hr (i : ι) : average (r i) = 1 := average_normalized_weight _ (hw i)
  have he : (fun x : ι → α => (∏ i, w i (x i))*(c+∑ i, T i (x i))^2) =
      fun x => (∏ i, average (w i))*((∏ i, r i (x i))*(c+∑ i, T i (x i))^2) := by
    funext x
    dsimp [r]
    rw [Finset.prod_div_distrib]
    field_simp [Finset.prod_ne_zero_iff.mpr (fun i _ => hw i)]
  rw [he,average_const_mul]
  have hm (i : ι) : average (fun a => r i a*T i a) =
      average (fun a => w i a*T i a)/average (w i) := by
    simp only [r,div_mul_eq_mul_div,average_div_const]
  have hh := normalized_product_shifted_sq r hr T _ hm c
  simp only [r,div_mul_eq_mul_div,average_div_const] at hh
  exact congrArg ((∏ i, average (w i)) * ·) hh

omit [Nonempty α] in
theorem weighted_deficit (w : ι → α → ℝ) (hw : ∀ i, average (w i) ≠ 0)
    (T : α → ℝ) (c : ℝ) :
    average (fun x : ι → α => (∏ i, w i (x i))*(1-(c+∑ i, T (x i))^2)) =
      (∏ i, (rawMoments T w) 0 i) *
        (1-(c+∑ i, means (rawMoments T w) i)^2-∑ i, vars (rawMoments T w) i) := by
  simp only [mul_sub,mul_one,average_sub]
  rw [average_pi_prod w,weighted_shifted_sq w hw (fun _ => T) c]
  simp only [rawMoments,means,vars,Fin.val_zero,Fin.val_one,show ((2 : Fin 3):ℕ) = 2 from rfl,pow_zero,pow_one,mul_one]
  ring

theorem prod_set_one (f : ι → ℝ) (i : ι) :
    (∏ j, if j = i then 1 else f j) = ∏ j ∈ Finset.univ.erase i, f j := by
  rw [← Finset.prod_erase_mul Finset.univ (fun j => if j = i then 1 else f j) (Finset.mem_univ i)]
  simp only [ite_true,mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [ite_eq_right (Finset.mem_erase.mp hj).1]

theorem sum_set_zero (f : ι → ℝ) (i : ι) :
    (∑ j, if j = i then 0 else f j) = ∑ j ∈ Finset.univ.erase i, f j := by
  rw [← Finset.sum_erase_add Finset.univ (fun j => if j = i then 0 else f j) (Finset.mem_univ i)]
  simp only [ite_true,add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [ite_eq_right (Finset.mem_erase.mp hj).1]

def without (w : ι → α → ℝ) (i j : ι) (a : α) : ℝ := if j = i then 1 else w j a

theorem weighted_deficit_without (w : ι → α → ℝ) (hw : ∀ i, average (w i) ≠ 0)
    (T : α → ℝ) (h0 : average T = 0) (h1 : average (fun a => (T a)^2) = 1)
    (c : ℝ) (i : ι) :
    average (fun x : ι → α => (∏ j ∈ Finset.univ.erase i, w j (x j))*(1-(c+∑ j, T (x j))^2)) =
      -((∏ j, rawMoments T w 0 j)/rawMoments T w 0 i) *
        ((c+∑ j, means (rawMoments T w) j-means (rawMoments T w) i)^2+
          ∑ j ∈ Finset.univ.erase i, vars (rawMoments T w) j) := by
  let l := rawMoments T w
  have hb (j) : rawMoments T (without w i) 0 j = if j = i then 1 else l 0 j := by
    by_cases hj : j = i <;> simp [rawMoments,without,hj,average_const,l]
  have hm (j) : means (rawMoments T (without w i)) j = if j = i then 0 else means l j := by
    by_cases hj : j = i <;> simp [means,rawMoments,without,hj,average_const,h0,l]
  have hv (j) : vars (rawMoments T (without w i)) j = if j = i then 1 else vars l j := by
    by_cases hj : j = i
    · simp [vars,hm,rawMoments,without,hj,average_const,h1]
    · simp [vars,hm,rawMoments,without,hj,l]
  have hwb (j) : average (without w i j) ≠ 0 := by
    change average (fun a => if j = i then 1 else w j a) ≠ 0
    by_cases hj : j = i <;> simp [hj,average_const,hw]
  have he : (fun x : ι → α => (∏ j ∈ Finset.univ.erase i, w j (x j))*(1-(c+∑ j, T (x j))^2)) =
      fun x => (∏ j, without w i j (x j))*(1-(c+∑ j, T (x j))^2) := by
    funext x
    change _ = (∏ j, if j = i then 1 else w j (x j))*(1-(c+∑ j, T (x j))^2)
    rw [prod_set_one]
  rw [he,weighted_deficit (without w i) hwb T c]
  simp_rw [hb,hm,hv]
  rw [prod_set_one,sum_set_zero]
  have hp : (∏ j ∈ Finset.univ.erase i, l 0 j) = (∏ j, l 0 j)/l 0 i := by
    apply (eq_div_iff (by simpa [l,rawMoments] using hw i)).mpr
    exact Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  have hs := Finset.sum_erase_add Finset.univ (fun j => means l j) (Finset.mem_univ i)
  have hvs : (∑ j, if j = i then (1:ℝ) else vars l j) = 1+∑ j ∈ Finset.univ.erase i, vars l j := by
    rw [← Finset.sum_erase_add Finset.univ (fun j => if j = i then (1:ℝ) else vars l j)
      (Finset.mem_univ i)]
    simp only [ite_true]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp only [ite_eq_right (Finset.mem_erase.mp hj).1]
  rw [hp,hvs,show (∑ j ∈ Finset.univ.erase i, means l j) = (∑ j, means l j)-means l i by linarith]
  change _ = -((∏ j, l 0 j)/l 0 i)*((c+∑ j, means l j-means l i)^2+
    ∑ j ∈ Finset.univ.erase i, vars l j)
  ring

def softWeight (s w : ι → α → ℝ) (x : α × (ι → α)) : ℝ :=
  (∑ i, s i x.1 * ∏ j ∈ Finset.univ.erase i, w j (x.2 j)) - ∏ j, w j (x.2 j)

def deficit (T : α → ℝ) (b : ℝ) (a : α × (ι → α) → ℝ) : ℝ :=
  average (fun x => a x*(1-(T x.1+∑ j, T (x.2 j)-b)^2))

omit [Nonempty α] in
theorem quadratic_average (T w : α → ℝ) (a v : ℝ) :
    average (fun x => w x*((1+T x-a)^2+v)) = average (fun x => w x*(T x)^2) +
      2*(1-a)*average (fun x => w x*T x) + ((1-a)^2+v)*average w := by
  have he : (fun x => w x*((1+T x-a)^2+v)) = fun x =>
      w x*(T x)^2+2*(1-a)*(w x*T x)+((1-a)^2+v)*w x := by funext x; ring
  rw [he,average_add,average_add,average_const_mul,average_const_mul]

theorem soft_deficit_eq_gain (s w : ι → α → ℝ) (hw : ∀ i, average (w i) ≠ 0)
    (T : α → ℝ) (h0 : average T = 0) (h1 : average (fun a => (T a)^2) = 1) :
    deficit T ((∑ i, means (rawMoments T w) i)-1) (softWeight s w) =
      gain (rawMoments T w) (rawMoments T s) := by
  let l := rawMoments T w
  let b := (∑ i, means l i)-1
  let P := ∏ i, l 0 i
  let v := ∑ i, vars l i
  have hshift (u : α) (z : ι → α) : T u+∑ i, T (z i)-b = T u-b+∑ i, T (z i) := by ring
  have hex (u : α) (i : ι) :
      average (fun z : ι → α => (∏ j ∈ Finset.univ.erase i, w j (z j))*
        (1-(T u-b+∑ j, T (z j))^2)) = -(P/l 0 i)*
          ((1+T u-means l i)^2+∑ j ∈ Finset.univ.erase i, vars l j) := by
    rw [weighted_deficit_without w hw T h0 h1 (T u-b) i]
    change -(P/l 0 i)*_ = _
    congr 2
    dsimp [b]
    ring
  have hall (u : α) :
      average (fun z : ι → α => (∏ j, w j (z j))*(1-(T u-b+∑ j, T (z j))^2)) =
        P*(1-(1+T u)^2-v) := by
    rw [weighted_deficit w hw T (T u-b)]
    change P*(1-(T u-b+∑ i, means l i)^2-v) = _
    dsimp [b]
    ring
  have ha : average (fun u => P*(1-(1+T u)^2-v)) = -P*(1+v) := by
    have he : (fun u => P*(1-(1+T u)^2-v)) = fun u =>
        -P*(T u)^2-2*P*T u-P*v := by funext u; ring
    rw [he,average_sub,average_sub,average_const_mul,average_const_mul,average_const,h0,h1]
    ring
  have hi (i : ι) : average (fun u => s i u*(-(P/l 0 i)*
      ((1+T u-means l i)^2+∑ j ∈ Finset.univ.erase i, vars l j))) =
      -P*((rawMoments T s 2 i+2*(1-means l i)*rawMoments T s 1 i+
        ((1-means l i)^2+∑ j ∈ Finset.univ.erase i, vars l j)*rawMoments T s 0 i)/l 0 i) := by
    have he : (fun u => s i u*(-(P/l 0 i)*
        ((1+T u-means l i)^2+∑ j ∈ Finset.univ.erase i, vars l j))) = fun u =>
        -(P/l 0 i)*(s i u*((1+T u-means l i)^2+∑ j ∈ Finset.univ.erase i, vars l j)) := by
      funext u; ring
    rw [he,average_const_mul,quadratic_average]
    simp only [rawMoments,Fin.val_zero,Fin.val_one,show ((2:Fin 3):ℕ)=2 from rfl,pow_zero,pow_one,mul_one]
    ring
  change deficit T b (softWeight s w) = _
  rw [deficit,average_prod]
  simp only [softWeight,sub_mul,Finset.sum_mul]
  simp_rw [hshift,mul_assoc]
  simp only [average_sub,average_sum,average_const_mul]
  simp_rw [hex,hall]
  rw [ha]
  simp_rw [hi]
  rw [← Finset.mul_sum]
  change -P*(_)-(-P*(1+v)) = P*(1+v-_)
  ring

end SoftEvent
end SquareRootDegree

end

end OAI
