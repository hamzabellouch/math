import OAI.Analysis.TriangularHilbert.WeightedCubic

namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι]

def hsSquare (R : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖R i j‖^2

def hsCube (R : Matrix ι ι ℂ) : ℝ := hsSquare R * Real.sqrt (hsSquare R)

lemma hsSquare_nonneg (R : Matrix ι ι ℂ) : 0 ≤ hsSquare R :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma hsSquare_star (R : Matrix ι ι ℂ) : hsSquare Rᴴ = hsSquare R := by
  unfold hsSquare
  simp only [Matrix.conjTranspose_apply,norm_star]
  rw [Finset.sum_comm]

lemma hsSquare_rowStar_sum [DecidableEq ι] (A : Three → Matrix ι ι ℂ) (v : Three) :
    hsSquare (rowStar A v) = ∑ w, hsSquare (triangleBlocks A v w) := by
  unfold hsSquare
  simp only [Fintype.sum_prod_type,rowStar_apply]
  have he (a : Three) : (∑ i, ∑ b : Three, ∑ j, ‖if a = v then triangleBlocks A a b i j else 0‖^2) =
      if a = v then (∑ b : Three, ∑ i, ∑ j, ‖triangleBlocks A a b i j‖^2) else 0 := by
    split_ifs with ha
    · exact Finset.sum_comm
    · simp
  simp_rw [he]
  simp

lemma hsSquare_zero : hsSquare (0 : Matrix ι ι ℂ) = 0 := by simp [hsSquare]

lemma hsSquare_rowStar [DecidableEq ι] (A : Three → Matrix ι ι ℂ) (v : Three) :
    hsSquare (rowStar A v) = hsSquare (A v) + hsSquare (A (v+2)) := by
  rw [hsSquare_rowStar_sum,Fin.sum_univ_three]
  fin_cases v <;> simp [triangleBlocks,hsSquare_zero,hsSquare_star]
  ac_rfl

lemma cubic_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a+b)*Real.sqrt (a+b) ≤ Real.sqrt 2*(a*Real.sqrt a+b*Real.sqrt b) := by
  have hh := TriangularHilbert.weighted_cubic (Finset.univ : Finset (Fin 2))
    ![Real.sqrt a,Real.sqrt b] (fun _ => 1)
    (by intro i _; fin_cases i <;> simp [Real.sqrt_nonneg]) (by simp)
  have he (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x)^3 = x*Real.sqrt x := by
    rw [pow_succ,Real.sq_sqrt hx]
  simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,
    Real.sq_sqrt ha,Real.sq_sqrt hb,he a ha,he b hb,mul_one,one_mul,one_add_one_eq_two,mul_comm] using hh

lemma energy_star_le_hsCube [DecidableEq ι] (A : Three → Matrix ι ι ℂ) (v : Three) :
    energy (starGram A v) ≤ Real.sqrt 2*(hsCube (A v)+hsCube (A (v+2))) := by
  have hh := energy_gram_le_HS (rowStar A v)
  change energy (starGram A v) ≤ hsSquare (rowStar A v)*Real.sqrt (hsSquare (rowStar A v)) at hh
  rw [hsSquare_rowStar] at hh
  exact hh.trans (cubic_add_le (hsSquare_nonneg _) (hsSquare_nonneg _))

lemma hsSquare_weightedArray (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) :
    hsSquare (weightedArray A g v) = ∑ i, ∑ j, ‖A v i j‖^2 * (g v i*g (v+1) j) := by
  unfold hsSquare weightedArray
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,
    Real.sq_sqrt (hg v i),Real.sq_sqrt (hg (v+1) j)]
  ring

lemma hsCube_weightedArray_le (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ v, (∑ i, g v i) ≤ M) (v : Three) :
    hsCube (weightedArray A g v) ≤ M * ∑ i, ∑ j, ‖A v i j‖^3 * (g v i*g (v+1) j) := by
  have hh := TriangularHilbert.weighted_cubic (Finset.univ : Finset (ι×ι))
    (fun a => ‖A v a.1 a.2‖) (fun a => g v a.1*g (v+1) a.2)
    (fun _ _ => norm_nonneg _) (fun a _ => mul_nonneg (hg _ _) (hg _ _))
  simp only [Fintype.sum_prod_type] at hh
  have hw : (∑ i, ∑ j, g v i*g (v+1) j) ≤ M^2 := by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul,pow_two]
    exact mul_le_mul (hm v) (hm (v+1)) (Finset.sum_nonneg (fun j _ => hg _ j)) hM
  have hs : Real.sqrt (∑ i, ∑ j, g v i*g (v+1) j) ≤ M := by
    simpa only [Real.sqrt_sq hM] using Real.sqrt_le_sqrt hw
  unfold hsCube
  rw [hsSquare_weightedArray A g hg]
  exact hh.trans (by
    rw [mul_comm M]
    exact mul_le_mul_of_nonneg_left hs (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun j _ => mul_nonneg (pow_nonneg (norm_nonneg _) _) (mul_nonneg (hg _ _) (hg _ _))))))
end
end TriangularHilbert.MatrixEnergy
end

end OAI
