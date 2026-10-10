import Mathlib
import OAI.Probability.SKRatio.Calculus.RowControl
import OAI.Probability.SKRatio.Variational.CompactField

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open Scalar Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def quadratic (A : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j*p i*p j

def weightedForm (A : Matrix (Fin n) (Fin n) ℝ) (G : FieldWeight × FieldWeight → ℝ)
    (x : Fin n → FieldWeight) (p : Fin n → ℝ) : ℝ :=
  quadratic (fun i j => A i j*G (x i,x j)) p

def diagonalForm (A : Matrix (Fin n) (Fin n) ℝ) (G : FieldWeight × FieldWeight → ℝ)
    (x : Fin n → FieldWeight) (p : Fin n → ℝ) : ℝ :=
  ∑ i, (∑ j, A i j*G (x i,x j))*p i^2

def varianceKernel (p : FieldWeight × FieldWeight) : ℝ := compactV p.2
def meanVarianceKernel (p : FieldWeight × FieldWeight) : ℝ :=
  (1-(p.2:ℝ))*compactV p.2

lemma continuous_varianceKernel : Continuous varianceKernel :=
  continuous_compactV.comp continuous_snd
lemma continuous_meanVarianceKernel : Continuous meanVarianceKernel := by
  unfold meanVarianceKernel
  exact (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
    (continuous_compactV.comp continuous_snd)

def compactForm (J : Interaction n) (x : Fin n → FieldWeight) (p : Fin n → ℝ) : ℝ :=
  weightedForm J varianceKernel x p +
  2*weightedForm (fun i j => J i j^2) meanVarianceKernel x p +
  diagonalForm (fun i j => J i j^2) compactF x p +
  weightedForm (fun i j => J i j^2) compactK x p

lemma quadratic_add (A B : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ) :
    quadratic (A+B) p = quadratic A p+quadratic B p := by
  simp only [quadratic,Matrix.add_apply,add_mul,Finset.sum_add_distrib]
lemma quadratic_sub (A B : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ) :
    quadratic (A-B) p = quadratic A p-quadratic B p := by
  simp only [quadratic,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]
lemma quadratic_const_mul (a : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ) :
    quadratic (a • A) p = a*quadratic A p := by
  simp only [quadratic,Matrix.smul_apply,smul_eq_mul,mul_assoc,←Finset.mul_sum]

lemma quadratic_inner (A : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ) :
    quadratic A p = inner ℝ (WithLp.toLp 2 p)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A (WithLp.toLp 2 p)) := by
  rw [Matrix.inner_toEuclideanCLM]
  simp only [quadratic,dotProduct,Matrix.mulVec,Finset.mul_sum]
  congr 1
  ext i
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma quadratic_abs_le (A : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ) :
    |quadratic A p| ≤ euclideanOpNorm A*(∑ i, p i^2) := by
  rw [quadratic_inner]
  let P : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 p
  have hb := (abs_real_inner_le_norm P (Matrix.toEuclideanCLM (𝕜 := ℝ) A P)).trans
    (mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (𝕜 := ℝ) A).le_opNorm P) (norm_nonneg P))
  calc
    _ ≤ ‖P‖*(‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖*‖P‖) := hb
    _ = euclideanOpNorm A*(∑ i, p i^2) := by
      rw [show ‖P‖*(‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖*‖P‖) =
        euclideanOpNorm A*‖P‖^2 by unfold euclideanOpNorm; ring]
      rw [EuclideanSpace.real_norm_sq_eq]

lemma weightedForm_sub (A B : Matrix (Fin n) (Fin n) ℝ)
    (G : FieldWeight × FieldWeight → ℝ) (x : Fin n → FieldWeight) (p : Fin n → ℝ) :
    weightedForm A G x p-weightedForm B G x p = weightedForm (A-B) G x p := by
  simp only [weightedForm,quadratic,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]

lemma diagonalForm_sub (A B : Matrix (Fin n) (Fin n) ℝ)
    (G : FieldWeight × FieldWeight → ℝ) (x : Fin n → FieldWeight) (p : Fin n → ℝ) :
    diagonalForm A G x p-diagonalForm B G x p = diagonalForm (A-B) G x p := by
  simp only [diagonalForm,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]

lemma diagonalForm_abs_le (A : Matrix (Fin n) (Fin n) ℝ)
    (G : FieldWeight × FieldWeight → ℝ) (x : Fin n → FieldWeight) (p : Fin n → ℝ)
    {C : ℝ} (hC : ∀ i, |∑ j, A i j*G (x i,x j)| ≤ C) :
    |diagonalForm A G x p| ≤ C*∑ i, p i^2 := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i, C*p i^2 := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul,abs_of_nonneg (sq_nonneg (p i))]
      exact mul_le_mul_of_nonneg_right (hC i) (sq_nonneg _))
    _ = _ := (Finset.mul_sum ..).symm

lemma sum_offdiag_eq_full {F : Fin n → Fin n → ℝ} (hF : ∀ i, F i i=0) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, F i j) = ∑ i, ∑ j, F i j := by
  apply Finset.sum_congr rfl
  intro i _
  simpa only [hF i,add_zero] using Finset.sum_erase_add Finset.univ (F i) (Finset.mem_univ i)

lemma gradient_pair_expansion (J : Interaction n) (hJ : ∀ i j, J i j=J j i)
    (hdiag : ∀ i, J i i=0) (H p : Fin n → ℝ) :
    pairSum (fun i j => J i j^2*(v (H j)*p i+v (H i)*p j)^2/(w (H i)+w (H j))) =
      diagonalForm (fun i j => J i j^2) compactF (fun i => compactWeight (H i)) p +
      weightedForm (fun i j => J i j^2) compactK (fun i => compactWeight (H i)) p := by
  have hd : ∀ i, J i i^2*(v (H i)^2/(w (H i)+w (H i)))*p i^2=0 := by simp [hdiag]
  have hk : ∀ i, J i i^2*kernel (H i) (H i)*p i*p i=0 := by simp [hdiag]
  simp only [diagonalForm,weightedForm,quadratic,compactF_weight,compactK_weight,Finset.sum_mul]
  rw [←sum_offdiag_eq_full hd,←sum_offdiag_eq_full hk,sum_offdiag_pairs,sum_offdiag_pairs,←pairSum_add]
  unfold pairSum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only []
  rw [hJ j i]
  dsimp [kernel]
  rw [add_comm (w (H j)) (w (H i))]
  ring

theorem gradientForm_eq_compactForm (J : Interaction n) (hJ : ∀ i j, J i j=J j i)
    (hdiag : ∀ i, J i i=0) (p : Fin n → ℝ) :
    gradientForm J p = compactForm J (fun i => compactWeight (∑ j, J i j)) p := by
  have hm (i : Fin n) : mean J (plusSpin n) i = m (∑ j, J i j) := by
    simp [mean,field,plusSpin,spin,m]
  have hv (i : Fin n) : conditionalVariance J (plusSpin n) i = v (∑ j, J i j) := by
    simp only [conditionalVariance,hm,v]
  have hw (i : Fin n) : gradientWeight J (plusSpin n) i = w (∑ j, J i j) := by
    simp [gradientWeight,plusSpin,spin,hm,w]
  simp only [gradientForm,hm,hv,hw,gradient_pair_expansion J hJ hdiag,
    compactForm,weightedForm,quadratic,varianceKernel,meanVarianceKernel,
    compactV_weight,compactWeight_coe]
  have h₁ : (∑ i, ∑ j ∈ Finset.univ.erase i, J i j*p i*v (∑ k, J j k)*p j) =
      ∑ i, ∑ j, J i j*v (∑ k, J j k)*p i*p j := by
    rw [sum_offdiag_eq_full (by intro i; simp [hdiag])]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h₂ : (∑ i, ∑ j ∈ Finset.univ.erase i, J i j^2*p i*m (∑ k, J j k)*v (∑ k, J j k)*p j) =
      ∑ i, ∑ j, J i j^2*((1-w (∑ k, J j k))*v (∑ k, J j k))*p i*p j := by
    rw [sum_offdiag_eq_full (by intro i; simp [hdiag])]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [w]
    ring
  rw [h₁,h₂]
  ring

end SKRatio.Planted

end
end

end OAI
