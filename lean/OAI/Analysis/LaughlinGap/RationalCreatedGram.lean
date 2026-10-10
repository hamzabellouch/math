import Mathlib
import OAI.Analysis.LaughlinGap.ExteriorTermExpansion

namespace OAI

/-! Rational Created Gram. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators

lemma wordSign_ne_zero_nodup {n : ℕ} (js : List (Fin n)) (h : wordSign js ≠ 0) : js.Nodup := by
  induction js with
  | nil => simp
  | cons j js ih =>
    by_cases hj : j ∈ js
    · exact False.elim (h (by simp [wordSign,hj]))
    · exact List.nodup_cons.mpr ⟨hj,ih (by intro he; apply h; simp [wordSign,hj,he])⟩

end LaughlinGap.Occupation

namespace LaughlinGap.RealOccupation
open scoped BigOperators InnerProduct
open Spin

noncomputable def rootSetWeight {n : ℕ} (A : Finset (Fin n)) : ℝ :=
  ∏ a ∈ A, rootFactorial a.val

def setFactorial {n : ℕ} (A : Finset (Fin n)) : ℚ := ∏ a ∈ A, (a.val.factorial : ℚ)

lemma rootSetWeight_sq {n : ℕ} (A : Finset (Fin n)) :
    rootSetWeight A^2 = (setFactorial A:ℝ) := by
  simp [rootSetWeight,setFactorial,← Finset.prod_pow]

lemma rootSetWeight_ne_zero {n : ℕ} (A : Finset (Fin n)) : rootSetWeight A ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun a _ => rootFactorial_ne_zero a.val

def fourColumn {D : ℕ} (hD : D ≤ 23) (r : ℕ) (A : Finset (Fin 25)) : ℚ :=
  ∑ a : FourTerm D, if (fourTermLabels hD a).toFinset=A then
    fourTermCoefficient D r a * Occupation.wordSign (fourTermLabels hD a) else 0

def fourKeys {D : ℕ} (hD : D ≤ 23) : Finset (Finset (Fin 25)) :=
  (Finset.univ.filter (fun a : FourTerm D => (fourTermLabels hD a).Nodup)).image
    (fun a => (fourTermLabels hD a).toFinset)

lemma fourColumn_support {D : ℕ} (hD : D ≤ 23) (r : ℕ) (A : Finset (Fin 25))
    (h : A ∉ fourKeys hD) : fourColumn hD r A = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  by_cases he : (fourTermLabels hD a).toFinset=A
  · have hz : Occupation.wordSign (fourTermLabels hD a)=0 := by
      by_contra hz
      apply h
      exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,Occupation.wordSign_ne_zero_nodup _ hz⟩,he⟩
    simp [he,hz]
  · simp [he]

lemma four_term_denominator {D : ℕ} (hD : D ≤ 23) (r : ℕ) (a : FourTerm D) :
    copyNormalization D r * (fourTermCoefficient D r a : ℝ) *
        (Occupation.wordSign (fourTermLabels hD a):ℝ) /
      (rootFactorial (fourTermX a)*rootFactorial (fourTermY a)*
        rootFactorial (fourTermJ a)*rootFactorial (fourTermK a)) =
      copyNormalization D r *
        (fourTermCoefficient D r a * Occupation.wordSign (fourTermLabels hD a):ℚ) /
          rootSetWeight (fourTermLabels hD a).toFinset := by
  by_cases hs : Occupation.wordSign (fourTermLabels hD a)=0
  · simp [hs]
  · have hn := Occupation.wordSign_ne_zero_nodup _ hs
    rw [rootSetWeight,List.prod_toFinset _ hn]
    simp only [fourTermLabels,List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one,
      Rat.cast_mul]
    ring

lemma four_created_column {D : ℕ} (hD : D ≤ 23) (r : FourCopy D) (A : Finset (Fin 25)) :
    ((fourLocalHighestStar hD r).adjoint (Occupation.vacuum 25)) A =
      ((copyNormalization D r.val.val * (fourColumn hD r.val.val A:ℝ) / rootSetWeight A : ℝ):ℂ) := by
  rw [fourLocalHighestStar_terms]
  simp only [fourColumn,Rat.cast_sum]
  rw [Finset.mul_sum,Finset.sum_div]
  simp only [map_sum,map_smulₛₗ,LinearMap.sum_apply,LinearMap.smul_apply,
    Occupation.word_adjoint_vacuum,smul_smul,WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_smul,Pi.smul_apply,PiLp.single_apply,
    smul_eq_mul,map_mul,Complex.conj_ofReal,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases he : (fourTermLabels hD a).toFinset=A
  · simp only [he,← Complex.ofReal_ratCast,← Complex.ofReal_mul]
    rw [four_pair_normalization]
    have hd := four_term_denominator hD r.val.val a
    rw [he] at hd
    push_cast
    norm_cast
    convert hd using 1
    ring
  · have hne : A ≠ (fourTermLabels hD a).toFinset := Ne.symm he
    simp only [ite_eq_right he,ite_eq_right hne,Rat.cast_zero,mul_zero,zero_div,Complex.ofReal_zero]

def rationalCreatedGram {D : ℕ} (hD : D ≤ 23) : Matrix (FourCopy D) (FourCopy D) ℚ :=
  fun u v => ∑ A ∈ fourKeys hD, fourColumn hD u.val.val A * fourColumn hD v.val.val A / setFactorial A

lemma createdGram_rational {D : ℕ} (hD : D ≤ 23) (u v : FourCopy D) :
    Occupation.createdGram (fourLocalHighestStar hD) u v =
      ((copyNormalization D u.val.val * (rationalCreatedGram hD u v:ℝ) *
        copyNormalization D v.val.val : ℝ):ℂ) := by
  unfold Occupation.createdGram
  simp only [PiLp.inner_apply,RCLike.inner_apply,
    four_created_column,Complex.conj_ofReal]
  have he : (∑ A : Finset (Fin 25),
      (copyNormalization D u.val.val * (fourColumn hD u.val.val A:ℝ) / rootSetWeight A)*
      (copyNormalization D v.val.val * (fourColumn hD v.val.val A:ℝ) / rootSetWeight A)) =
      ∑ A ∈ fourKeys hD,
      (copyNormalization D u.val.val * (fourColumn hD u.val.val A:ℝ) / rootSetWeight A)*
      (copyNormalization D v.val.val * (fourColumn hD v.val.val A:ℝ) / rootSetWeight A) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro A ha hnot
    simp [fourColumn_support hD u.val.val A hnot]
  simp only [← Complex.ofReal_mul,← Complex.ofReal_sum]
  simp only [mul_comm (copyNormalization D v.val.val * _ / _)
    (copyNormalization D u.val.val * _ / _)]
  rw [he]
  congr 1
  simp only [rationalCreatedGram,Rat.cast_sum,Rat.cast_div,Rat.cast_mul,
    Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro A ha
  rw [← rootSetWeight_sq]
  ring

end LaughlinGap.RealOccupation

end

end OAI
