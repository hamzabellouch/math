import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.NonroundMass

namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Finset
abbrev Vec := Ix → ℝ
abbrev Mat := Matrix Ix Ix ℝ

def proj (x : Vec) (i j : Ix) : ℝ := (if i = j then 1 else 0) - x i * x j

def dproj (x : Vec) (k i j : Ix) : ℝ :=
  -(if k = i then 1 else 0) * x j - x i * (if k = j then 1 else 0)

def tangentTrace (x : Vec) (H : Mat) : ℝ := ∑ i, ∑ j, proj x i j * H i j

def hessTF (x : Vec) (H : Mat) (i j : Ix) : ℝ :=
  (∑ a, ∑ b, proj x i a * H a b * proj x b j) - tangentTrace x H / 2 * proj x i j

def dTangentTrace (x : Vec) (H : Mat) (K : Ix → Mat) (k : Ix) : ℝ :=
  ∑ i, ∑ j, (dproj x k i j * H i j + proj x i j * K k i j)

def dHessTF (x : Vec) (H : Mat) (K : Ix → Mat) (k i j : Ix) : ℝ :=
  (∑ a, ∑ b, (dproj x k i a * H a b * proj x b j +
    proj x i a * K k a b * proj x b j + proj x i a * H a b * dproj x k b j)) -
      dTangentTrace x H K k / 2 * proj x i j - tangentTrace x H / 2 * dproj x k i j

def divHessTF (x : Vec) (H : Mat) (K : Ix → Mat) (j : Ix) : ℝ :=
  ∑ k, ∑ i, ∑ l, proj x k i * proj x j l * dHessTF x H K k i l

def roundLap (x : Vec) (g : Vec) (H : Mat) : ℝ :=
  tangentTrace x H - 2 * (∑ i, x i * g i)

def dRoundLap (x : Vec) (g : Vec) (H : Mat) (K : Ix → Mat) (k : Ix) : ℝ :=
  dTangentTrace x H K k - 2 * (g k + ∑ i, x i * H k i)

lemma proj_symm (x : Vec) (i j : Ix) : proj x i j = proj x j i := by
  simp only [proj, eq_comm, mul_comm]

lemma proj_normal {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (i : Ix) :
    ∑ j, proj x i j * x j = 0 := by
  simp only [proj, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq univ i (fun j => x j), ite_eq_left (mem_univ i)]
  simp_rw [mul_assoc, ← pow_two]
  rw [← Finset.mul_sum, hx]
  ring

lemma proj_idempotent {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (i j : Ix) :
    ∑ k, proj x i k * proj x k j = proj x i j := by
  simp only [proj, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' univ j (fun k => (if i = k then 1 else 0) - x i * x k),
    ite_eq_left (mem_univ j)]
  have hn := proj_normal hx i
  simp only [proj] at hn
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  simp only [hn, zero_mul, sub_zero]

lemma proj_trace {x : Vec} (hx : ∑ i, x i ^ 2 = 1) : ∑ i, proj x i i = 2 := by
  simp only [proj, ← pow_two, Finset.sum_sub_distrib]
  rw [hx]
  norm_num

lemma projected_dproj {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (j k b : Ix) :
    ∑ l, proj x j l * dproj x k b l = -x b * proj x j k := by
  have he (l : Ix) : proj x j l * dproj x k b l =
      -(if k = b then 1 else 0) * (proj x j l * x l) -
        x b * (if k = l then proj x j l else 0) := by
    simp only [dproj]
    split_ifs <;> ring
  simp_rw [he, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [proj_normal hx, Finset.sum_ite_eq univ k, ite_eq_left (mem_univ k)]
  ring

lemma contracted_dproj {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (a : Ix) :
    ∑ k, ∑ i, proj x k i * dproj x k i a = -2 * x a := by
  have he (k i : Ix) : proj x k i * dproj x k i a =
      -(if k = i then proj x k i else 0) * x a -
        (if k = a then 1 else 0) * (proj x k i * x i) := by
    simp only [dproj]
    split_ifs <;> ring
  simp only [he, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    Finset.sum_neg_distrib, Finset.sum_ite_eq, mem_univ, ite_true, proj_normal hx,
    mul_zero, sub_zero]
  rw [proj_trace hx]

lemma sum3_rotate (f : Ix → Ix → Ix → ℝ) :
    (∑ i, ∑ a, ∑ b, f i a b) = ∑ a, ∑ b, ∑ i, f i a b := by
  simpa only [Fintype.sum_prod_type] using
    (Finset.sum_comm (s := (univ : Finset Ix)) (t := (univ : Finset (Ix × Ix)))
      (f := fun i ab => f i ab.1 ab.2))

lemma sum4_comm (f : Ix → Ix → Ix → Ix → ℝ) :
    (∑ k, ∑ i, ∑ a, ∑ b, f k i a b) = ∑ a, ∑ b, ∑ k, ∑ i, f k i a b := by
  simpa only [Fintype.sum_prod_type] using
    (Finset.sum_comm (s := (univ : Finset (Ix × Ix))) (t := (univ : Finset (Ix × Ix)))
      (f := fun ki ab => f ki.1 ki.2 ab.1 ab.2))

lemma contraction_left_dproj {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (B : Ix → Ix → ℝ) :
    (∑ k, ∑ i, proj x k i * (∑ a, ∑ b, dproj x k i a * B a b)) =
      ∑ a, ∑ b, (-2 * x a) * B a b := by
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [sum4_comm]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  simp only [← Finset.sum_mul, contracted_dproj hx]

lemma contraction_left_proj {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (B : Ix → Ix → Ix → ℝ) :
    (∑ k, ∑ i, proj x k i * (∑ a, ∑ b, proj x i a * B k a b)) =
      ∑ k, ∑ a, ∑ b, proj x k a * B k a b := by
  apply sum_congr rfl
  intro k hk
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [sum3_rotate]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  rw [← Finset.sum_mul, proj_idempotent hx]

lemma contraction_trace_term {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (v : Vec) (j : Ix) :
    (∑ k, ∑ i, proj x k i * (v k * proj x i j)) = ∑ k, v k * proj x k j := by
  apply sum_congr rfl
  intro k hk
  simp_rw [mul_left_comm (proj x k _) (v k), ← Finset.mul_sum]
  rw [proj_idempotent hx]

lemma contraction_right_dproj {x : Vec} (_hx : ∑ i, x i ^ 2 = 1) (H : Mat) (j : Ix) :
    (∑ k, ∑ a, ∑ b, proj x k a * (H a b * dproj x k b j)) =
      -tangentTrace x H * x j - ∑ a, ∑ b, proj x j a * H a b * x b := by
  have he (k a b : Ix) : proj x k a * (H a b * dproj x k b j) =
      -(if k = b then proj x k a * H a b else 0) * x j -
        (if k = j then proj x k a * H a b * x b else 0) := by
    simp only [dproj]
    split_ifs <;> ring
  simp_rw [he]
  rw [sum3_rotate]
  simp only [sum_sub_distrib, ← sum_mul, sum_neg_distrib, sum_ite_eq', mem_univ, ite_true]
  simp_rw [proj_symm x _ _]
  simp only [← Finset.sum_neg_distrib, tangentTrace]

lemma sum3_last (f : Ix → Ix → Ix → ℝ) :
    (∑ i, ∑ a, ∑ b, f i a b) = ∑ b, ∑ i, ∑ a, f i a b := by
  simpa only [Fintype.sum_prod_type] using
    (Finset.sum_comm (s := (univ : Finset (Ix × Ix))) (t := (univ : Finset Ix))
      (f := fun ia b => f ia.1 ia.2 b))

def normalH (x : Vec) (H : Mat) (j : Ix) : ℝ := ∑ a, ∑ b, proj x j a * H a b * x b
def projectedK (x : Vec) (K : Ix → Mat) (j : Ix) : ℝ :=
  ∑ k, proj x j k * (∑ a, ∑ b, proj x a b * K k a b)
def projectedTraceDeriv (x : Vec) (H : Mat) (K : Ix → Mat) (j : Ix) : ℝ :=
  ∑ k, proj x j k * dTangentTrace x H K k

def rawContract (x : Vec) (D : Ix → Ix → Ix → ℝ) (j : Ix) : ℝ :=
  ∑ k, ∑ i, proj x k i * D k i j

lemma rawContract_add (x : Vec) (D E : Ix → Ix → Ix → ℝ) (j : Ix) :
    rawContract x (D + E) j = rawContract x D j + rawContract x E j := by
  simp only [rawContract, Pi.add_apply, mul_add, sum_add_distrib]

lemma rawContract_sub (x : Vec) (D E : Ix → Ix → Ix → ℝ) (j : Ix) :
    rawContract x (D - E) j = rawContract x D j - rawContract x E j := by
  simp only [rawContract, Pi.sub_apply, mul_sub, sum_sub_distrib]

lemma rawContract_smul (x : Vec) (D : Ix → Ix → Ix → ℝ) (c : ℝ) (j : Ix) :
    rawContract x (c • D) j = c * rawContract x D j := by
  simp only [rawContract, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, Finset.mul_sum]

lemma first_contribution {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (H : Mat)
    (hH : ∀ i j, H i j = H j i) (j : Ix) :
    rawContract x (fun k i j => ∑ a, ∑ b, dproj x k i a * (H a b * proj x b j)) j =
      -2 * normalH x H j := by
  rw [rawContract, contraction_left_dproj hx]
  unfold normalH
  rw [sum_comm]
  simp only [Finset.mul_sum]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  rw [hH b a, proj_symm x a j]
  ring

lemma second_contribution {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (K : Ix → Mat)
    (hK : ∀ k a b, K k a b = K b k a) (j : Ix) :
    rawContract x (fun k i j => ∑ a, ∑ b, proj x i a * (K k a b * proj x b j)) j =
      projectedK x K j := by
  rw [rawContract, contraction_left_proj hx, sum3_last]
  unfold projectedK
  apply sum_congr rfl
  intro b hb
  simp only [Finset.mul_sum]
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro a ha
  rw [hK k a b, proj_symm x b j]
  ring

lemma third_contribution {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (H : Mat) (j : Ix) :
    rawContract x (fun k i j => ∑ a, ∑ b, proj x i a * (H a b * dproj x k b j)) j =
      -tangentTrace x H * x j - normalH x H j := by
  rw [rawContract, contraction_left_proj hx, contraction_right_dproj hx]
  rfl

lemma trace_contribution {x : Vec} (hx : ∑ i, x i ^ 2 = 1)
    (H : Mat) (K : Ix → Mat) (j : Ix) :
    rawContract x (fun k i j => dTangentTrace x H K k / 2 * proj x i j) j =
      projectedTraceDeriv x H K j / 2 := by
  rw [rawContract, contraction_trace_term hx]
  unfold projectedTraceDeriv
  rw [Finset.sum_div]
  apply sum_congr rfl
  intro k hk
  rw [proj_symm x k j]
  ring

lemma rawContract_tfHessian {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (H : Mat) (K : Ix → Mat)
    (hH : ∀ i j, H i j = H j i) (hK : ∀ k a b, K k a b = K b k a) (j : Ix) :
    rawContract x (dHessTF x H K) j =
      -3 * normalH x H j + projectedK x K j - projectedTraceDeriv x H K j / 2 := by
  have he : dHessTF x H K =
      ((fun k i j => ∑ a, ∑ b, dproj x k i a * (H a b * proj x b j)) +
      (fun k i j => ∑ a, ∑ b, proj x i a * (K k a b * proj x b j)) +
      (fun k i j => ∑ a, ∑ b, proj x i a * (H a b * dproj x k b j))) -
      (fun k i j => dTangentTrace x H K k / 2 * proj x i j) -
      (tangentTrace x H / 2) • dproj x := by
    funext k i j
    simp only [dHessTF, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      sum_add_distrib, mul_assoc]
  rw [he, rawContract_sub, rawContract_sub, rawContract_add, rawContract_add,
    first_contribution hx H hH, second_contribution hx K hK, third_contribution hx H,
    trace_contribution hx, rawContract_smul]
  change _ - tangentTrace x H / 2 * (∑ k, ∑ i, proj x k i * dproj x k i j) = _
  rw [contracted_dproj hx]
  ring

lemma dTangentTrace_formula (x : Vec) (H : Mat) (K : Ix → Mat)
    (hH : ∀ i j, H i j = H j i) (k : Ix) :
    dTangentTrace x H K k = (∑ a, ∑ b, proj x a b * K k a b) -
      2 * (∑ b, H k b * x b) := by
  have he (i j : Ix) : dproj x k i j * H i j =
      -(if k = i then H i j * x j else 0) -
        (if k = j then H i j * x i else 0) := by
    simp only [dproj]
    split_ifs <;> ring
  simp only [dTangentTrace, he, sum_add_distrib, sum_sub_distrib,
    sum_neg_distrib]
  have h1 : (∑ i, ∑ j, if k = i then H i j * x j else 0) = ∑ b, H k b * x b := by
    rw [sum_comm]
    simp only [sum_ite_eq, mem_univ, ite_true]
  have h2 : (∑ i, ∑ j, if k = j then H i j * x i else 0) = ∑ b, H k b * x b := by
    simp only [sum_ite_eq, mem_univ, ite_true]
    simp_rw [hH _ k]
  rw [h1, h2]
  ring

lemma projectedTraceDeriv_formula (x : Vec) (H : Mat) (K : Ix → Mat)
    (hH : ∀ i j, H i j = H j i) (j : Ix) :
    projectedTraceDeriv x H K j = projectedK x K j - 2 * normalH x H j := by
  simp only [projectedTraceDeriv, dTangentTrace_formula x H K hH, mul_sub,
    sum_sub_distrib, projectedK, normalH, Finset.mul_sum]
  congr 1
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro b hb
  ring

lemma rawContract_tfHessian_simplified {x : Vec} (hx : ∑ i, x i ^ 2 = 1)
    (H : Mat) (K : Ix → Mat) (hH : ∀ i j, H i j = H j i)
    (hK : ∀ k a b, K k a b = K b k a) (j : Ix) :
    rawContract x (dHessTF x H K) j = projectedK x K j / 2 - 2 * normalH x H j := by
  rw [rawContract_tfHessian hx H K hH hK, projectedTraceDeriv_formula x H K hH]
  ring

lemma projected_twice {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (v : Vec) (j : Ix) :
    (∑ l, proj x j l * (∑ k, proj x l k * v k)) = ∑ k, proj x j k * v k := by
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  rw [← Finset.sum_mul, proj_idempotent hx]

lemma divHessTF_eq {x : Vec} (hx : ∑ i, x i ^ 2 = 1)
    (g : Vec) (H : Mat) (K : Ix → Mat) (hH : ∀ i j, H i j = H j i)
    (hK : ∀ k a b, K k a b = K b k a) (j : Ix) :
    divHessTF x H K j = ∑ k, proj x j k * (g k + dRoundLap x g H K k / 2) := by
  have hc : divHessTF x H K j = ∑ l, proj x j l * rawContract x (dHessTF x H K) l := by
    simp only [divHessTF, rawContract, Finset.mul_sum]
    rw [sum3_last]
    apply sum_congr rfl
    intro l hl
    apply sum_congr rfl
    intro k hk
    apply sum_congr rfl
    intro i hi
    ring
  rw [hc]
  simp_rw [rawContract_tfHessian_simplified hx H K hH hK]
  have hkp : (∑ l, proj x j l * projectedK x K l) = projectedK x K j :=
    projected_twice hx _ j
  have hhp : (∑ l, proj x j l * normalH x H l) = normalH x H j := by
    simp only [normalH, ← Finset.mul_sum, mul_assoc]
    exact projected_twice hx _ j
  have hproj : (∑ l, proj x j l * (projectedK x K l / 2 - 2 * normalH x H l)) =
      projectedK x K j / 2 - 2 * normalH x H j := by
    simp only [mul_sub, ← mul_div_assoc, sum_sub_distrib, ← sum_div,
      mul_left_comm (proj x j _) 2, ← Finset.mul_sum, hkp, hhp]
  rw [hproj]
  simp only [dRoundLap, dTangentTrace_formula x H K hH, projectedK, normalH]
  rw [sum_div, Finset.mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro k hk
  simp only [← Finset.mul_sum, mul_assoc]
  have hm : (∑ i, x i * H k i) = ∑ i, H k i * x i := by simp_rw [mul_comm (x _)]
  rw [hm]
  ring

lemma hessTF_symm (x : Vec) (H : Mat) (hH : ∀ i j, H i j = H j i) (i j : Ix) :
    hessTF x H i j = hessTF x H j i := by
  unfold hessTF
  rw [proj_symm x i j]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  rw [proj_symm x i b, proj_symm x a j, hH b a]
  ring

lemma hessTF_normal_left {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (H : Mat) (j : Ix) :
    ∑ i, x i * hessTF x H i j = 0 := by
  simp only [hessTF, mul_sub, Finset.mul_sum, sum_sub_distrib]
  have he (i a b : Ix) : x i * (proj x i a * H a b * proj x b j) =
      (proj x a i * x i) * (H a b * proj x b j) := by rw [proj_symm x i a]; ring
  simp_rw [he]
  rw [sum3_rotate]
  simp only [← Finset.sum_mul, proj_normal hx, zero_mul, sum_const_zero]
  have ht (i : Ix) : x i * (tangentTrace x H / 2 * proj x i j) =
      tangentTrace x H / 2 * (proj x j i * x i) := by rw [proj_symm x i j]; ring
  simp_rw [ht, ← Finset.mul_sum, proj_normal hx]
  ring

lemma hessTF_projected_left {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (H : Mat) (i j : Ix) :
    ∑ k, proj x i k * hessTF x H k j = hessTF x H i j := by
  have he (k : Ix) : proj x i k * hessTF x H k j =
      (if i = k then hessTF x H k j else 0) - x i * (x k * hessTF x H k j) := by
    simp only [proj]
    split_ifs <;> ring
  simp only [he, sum_sub_distrib, sum_ite_eq, mem_univ, ite_true, ← Finset.mul_sum,
    hessTF_normal_left hx, mul_zero, sub_zero]

lemma hessTF_trace_zero {x : Vec} (hx : ∑ i, x i ^ 2 = 1) (H : Mat) :
    ∑ i, hessTF x H i i = 0 := by
  simp only [hessTF, sum_sub_distrib, ← Finset.mul_sum, proj_trace hx]
  have he (i a b : Ix) : proj x i a * H a b * proj x b i =
      (proj x b i * proj x i a) * H a b := by ring
  simp_rw [he]
  rw [sum3_rotate]
  simp only [← Finset.sum_mul, proj_idempotent hx]
  simp_rw [proj_symm x _ _]
  change tangentTrace x H - tangentTrace x H / 2 * 2 = 0
  ring

end
end CKSInducedSphere

end

end OAI
