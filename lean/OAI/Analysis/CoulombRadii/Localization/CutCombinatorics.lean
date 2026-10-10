import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.Add
import OAI.Analysis.CoulombRadii.FormDomain.CubeGradient

namespace OAI

noncomputable section

section
open scoped BigOperators Classical
namespace Coulomb

lemma sum_product_labels {I L : Type*} [Fintype I] [Fintype L] [DecidableEq I]
    (f : I → L → ℝ) : (∑ p : I → L, ∏ i, f i (p i)) = ∏ i, ∑ l, f i l := by
  simpa only [Fintype.piFinset_univ] using
    (Finset.prod_univ_sum (fun _ : I => (Finset.univ : Finset L)) f).symm

lemma product_partition_square {I L : Type*} [Fintype I] [Fintype L] [DecidableEq I]
    (f : I → L → ℝ) (hf : ∀ i, ∑ l, f i l ^ 2 = 1) :
    ∑ p : I → L, (∏ i, f i (p i))^2 = 1 := by
  simp_rw [←Finset.prod_pow]
  rw [sum_product_labels (fun i l => f i l ^ 2)]
  simp only [hf,Finset.prod_const_one]

lemma sum_slot_product {I L : Type*} [Fintype I] [Fintype L] [DecidableEq I]
    (f : I → L → ℝ) (g : L → ℝ) (i : I)
    (hf : ∀ j, ∑ l, f j l = 1) :
    (∑ p : I → L, g (p i) * ∏ j ∈ Finset.univ.erase i, f j (p j)) = ∑ l, g l := by
  let w : I → L → ℝ := fun j l => if j=i then g l else f j l
  have hp (p : I → L) : g (p i) * ∏ j ∈ Finset.univ.erase i, f j (p j) = ∏ j, w j (p j) := by
    rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [w,ite_eq_left rfl]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    exact (ite_eq_right (Finset.ne_of_mem_erase hj)).symm
  simp_rw [hp]
  rw [sum_product_labels w]
  rw [Finset.prod_eq_single i]
  · simp [w]
  · intro j hj hji
    simp only [w,ite_eq_right hji,hf]
  · simp

lemma sum_slot_product_square {I L : Type*} [Fintype I] [Fintype L] [DecidableEq I]
    (f : I → L → ℝ) (g : L → ℝ) (i : I)
    (hf : ∀ j, ∑ l, f j l ^ 2 = 1) :
    (∑ p : I → L, (g (p i) * ∏ j ∈ Finset.univ.erase i, f j (p j))^2) = ∑ l, g l ^ 2 := by
  simp_rw [mul_pow,←Finset.prod_pow]
  exact sum_slot_product (fun i l => f i l ^ 2) (fun l => g l ^ 2) i hf

lemma abs_partition_le_one {L : Type*} [Fintype L] (f : L → ℝ)
    (hf : ∑ l, f l ^ 2 = 1) (l : L) : |f l| ≤ 1 := by
  have h := Finset.single_le_sum (fun j _ => sq_nonneg (f j)) (Finset.mem_univ l)
  rw [hf] at h
  nlinarith [sq_abs (f l),abs_nonneg (f l)]

lemma abs_prod_le_one {I : Type*} (s : Finset I) (f : I → ℝ)
    (h : ∀ i ∈ s, |f i| ≤ 1) : |∏ i ∈ s, f i| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) h
end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def tensorCut {n : ℕ} {L : Type*} (χ : L → Space → ℝ) (p : Fin n → L) (x : Configuration n) : ℝ :=
  ∏ i, χ (p i) (position x i)

lemma tensorCut_contDiff {n : ℕ} {L : Type*} (χ : L → Space → ℝ)
    (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l)) (p : Fin n → L) :
    ContDiff ℝ (⊤ : ℕ∞) (tensorCut χ p) := by
  unfold tensorCut
  apply contDiff_prod
  intro i hi
  exact (hχ (p i)).comp (positionCLM i).contDiff

lemma tensorCut_fderiv {n : ℕ} {L : Type*} (χ : L → Space → ℝ)
    (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l)) (p : Fin n → L)
    (x : Configuration n) (i : Fin n) (b : Fin 3) :
    fderiv ℝ (tensorCut χ p) x (EuclideanSpace.single (i,b) 1) =
      fderiv ℝ (χ (p i)) (position x i) (EuclideanSpace.single b 1) *
        ∏ j ∈ Finset.univ.erase i, χ (p j) (position x j) := by
  have hd (j : Fin n) : DifferentiableAt ℝ (fun y : Configuration n => χ (p j) (position y j)) x := by
    exact ((hχ (p j)).differentiable (by simp) (positionCLM j x)).comp x
      (positionCLM j).differentiableAt
  have he (j : Fin n) : fderiv ℝ (fun y : Configuration n => χ (p j) (position y j)) x =
      (fderiv ℝ (χ (p j)) (position x j)).comp (positionCLM j) := by
    exact (((hχ (p j)).differentiable (by simp) (position x j)).hasFDerivAt.comp x
      (positionCLM j).hasFDerivAt).fderiv
  unfold tensorCut
  rw [fderiv_finsetProd (fun j _ => hd j),sum_apply]
  simp only [smul_apply,smul_eq_mul,he,ContinuousLinearMap.comp_apply,positionCLM_single]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    ring
  · intro j hj hji
    simp only [ite_eq_right hji,map_zero,mul_zero]
  · simp

lemma tensorCut_partition {n : ℕ} {L : Type*} [Fintype L]
    (χ : L → Space → ℝ) (hp : ∀ z, ∑ l, χ l z ^ 2 = 1) (x : Configuration n) :
    ∑ p : Fin n → L, tensorCut χ p x ^ 2 = 1 :=
  product_partition_square (fun i l => χ l (position x i)) (fun i => hp (position x i))

lemma tensorCut_abs_le_one {n : ℕ} {L : Type*} [Fintype L]
    (χ : L → Space → ℝ) (hp : ∀ z, ∑ l, χ l z ^ 2 = 1) (p : Fin n → L) (x : Configuration n) :
    |tensorCut χ p x| ≤ 1 :=
  abs_prod_le_one _ _ (fun i _ => abs_partition_le_one (fun l => χ l (position x i)) (hp _) _)

lemma tensorCut_partial_bound {n : ℕ} {L : Type*} [Fintype L]
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z ^ 2 = 1) {D : ℝ} (hD : 0 ≤ D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin n → L) (a : Fin n × Fin 3) (x : Configuration n) :
    |fderiv ℝ (tensorCut χ p) x (EuclideanSpace.single a 1)| ≤ D := by
  rcases a with ⟨i,b⟩
  rw [tensorCut_fderiv χ hχ,abs_mul]
  calc
    _ ≤ D*1 := mul_le_mul (hd _ _ _) (abs_prod_le_one _ _
      (fun j _ => abs_partition_le_one (fun l => χ l (position x j)) (hp _) _)) (abs_nonneg _) hD
    _ = D := mul_one D

lemma tensorCut_gradient_square_sum {n : ℕ} {L : Type*} [Fintype L]
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z ^ 2 = 1) (x : Configuration n) (i : Fin n) (b : Fin 3) :
    (∑ p : Fin n → L, (fderiv ℝ (tensorCut χ p) x (EuclideanSpace.single (i,b) 1))^2) =
      ∑ l, (fderiv ℝ (χ l) (position x i) (EuclideanSpace.single b 1))^2 := by
  simp_rw [tensorCut_fderiv χ hχ]
  exact sum_slot_product_square (fun j l => χ l (position x j))
    (fun l => fderiv ℝ (χ l) (position x i) (EuclideanSpace.single b 1)) i (fun j => hp _)

def H1Vector.labelCut {n : ℕ} {L : Type*} [Fintype L] (ψ : H1Vector n)
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z ^ 2 = 1) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin n → L) : H1Vector n :=
  ψ.smoothMul (tensorCut χ p) (tensorCut_contDiff χ hχ p) 1 D
    (tensorCut_abs_le_one χ hp p) (tensorCut_partial_bound χ hχ hp hD hd p)

lemma mass_labelCut {n : ℕ} {L : Type*} [Fintype L] (ψ : H1Vector n)
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z ^ 2 = 1) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D) :
    ∑ p : Fin n → L, mass (ψ.labelCut χ hχ hp D hD hd p) = mass ψ :=
  mass_smooth_partition ψ _ (tensorCut_contDiff χ hχ) 1 D (tensorCut_abs_le_one χ hp)
    (tensorCut_partial_bound χ hχ hp hD hd) (tensorCut_partition χ hp)

lemma form_labelCut {J n : ℕ} {L : Type*} [Fintype L] (S : Nuclei J) (ψ : H1Vector n)
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z ^ 2 = 1) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D) :
    (∑ p : Fin n → L, form S (ψ.labelCut χ hχ hp D hD hd p)) =
      form S ψ+(1/2:ℝ)*∑ s, ∑ a : Fin n × Fin 3, ∫ x,
        (∑ l, (fderiv ℝ (χ l) (position x a.1) (EuclideanSpace.single a.2 1))^2)*‖ψ.value s x‖^2 := by
  unfold H1Vector.labelCut
  rw [form_smooth_partition S ψ _ _ _ _ _ _ (tensorCut_partition χ hp)]
  simp_rw [tensorCut_gradient_square_sum χ hχ hp]

end Coulomb

end

end OAI
