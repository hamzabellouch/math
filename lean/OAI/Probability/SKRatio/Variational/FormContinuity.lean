import Mathlib
import OAI.Probability.SKRatio.Matrices.CompactMatrixMasks
import OAI.Probability.SKRatio.Variational.FormAlgebra

namespace OAI

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open Scalar Calculus MatrixNet
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma weightedForm_field_sub (A : Matrix (Fin n) (Fin n) ℝ)
    (G : FieldWeight × FieldWeight → ℝ) (x y : Fin n → FieldWeight) (p : Fin n → ℝ) :
    weightedForm A G x p-weightedForm A G y p =
      quadratic (fun i j => A i j*(G (x i,x j)-G (y i,y j))) p := by
  simp only [weightedForm,quadratic,mul_sub,sub_mul,Finset.sum_sub_distrib]

lemma weightedForm_field_bound (A : Matrix (Fin n) (Fin n) ℝ)
    (G : FieldWeight × FieldWeight → ℝ) (x y : Fin n → FieldWeight) (p : Fin n → ℝ)
    {a C : ℝ} (ha : 0≤a) (hC : 0≤C)
    (hr : ∀ i, ∑ j, |A i j| ≤ C) (hc : ∀ j, ∑ i, |A i j| ≤ C)
    (he : ∀ i j, |G (x i,x j)-G (y i,y j)| ≤ a) :
    |weightedForm A G x p-weightedForm A G y p| ≤ a*C*∑ i, p i^2 := by
  rw [weightedForm_field_sub]
  exact (quadratic_abs_le _ p).trans (mul_le_mul_of_nonneg_right
    (kernel_error_norm_le A _ _ ha hC hr hc he) (Finset.sum_nonneg (fun i _ => sq_nonneg (p i))))

lemma diagonalForm_field_bound (A : Matrix (Fin n) (Fin n) ℝ)
    (G : FieldWeight × FieldWeight → ℝ) (x y : Fin n → FieldWeight) (p : Fin n → ℝ)
    {a C : ℝ} (ha : 0≤a)
    (hr : ∀ i, ∑ j, |A i j| ≤ C)
    (he : ∀ i j, |G (x i,x j)-G (y i,y j)| ≤ a) :
    |diagonalForm A G x p-diagonalForm A G y p| ≤ a*C*∑ i, p i^2 := by
  have hid : diagonalForm A G x p-diagonalForm A G y p =
      ∑ i, (∑ j, A i j*(G (x i,x j)-G (y i,y j)))*p i^2 := by
    simp only [diagonalForm,mul_sub,sub_mul,Finset.sum_sub_distrib]
  have hb (i : Fin n) : |∑ j, A i j*(G (x i,x j)-G (y i,y j))| ≤ a*C := by
    calc
      _ ≤ ∑ j, |A i j*(G (x i,x j)-G (y i,y j))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, a*|A i j| := Finset.sum_le_sum (fun j _ => by
        rw [abs_mul,mul_comm]
        exact mul_le_mul_of_nonneg_right (he i j) (abs_nonneg _))
      _ = a*(∑ j, |A i j|) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hr i) ha
  rw [hid]
  calc
    _ ≤ ∑ i, |(∑ j, A i j*(G (x i,x j)-G (y i,y j)))*p i^2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (a*C)*p i^2 := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul,abs_of_nonneg (sq_nonneg (p i))]
      exact mul_le_mul_of_nonneg_right (hb i) (sq_nonneg _))
    _ = _ := (Finset.mul_sum ..).symm

lemma weightedForm_variance_eq (J : Interaction n) (x : Fin n → FieldWeight) (p : Fin n → ℝ) :
    weightedForm J varianceKernel x p = quadratic ((Matrix.of J)*
      Matrix.diagonal (fun i => compactV (x i))) p := by
  simp only [weightedForm,quadratic,varianceKernel,Matrix.mul_diagonal,Matrix.of_apply]

lemma weightedForm_variance_field_bound (J : Interaction n) (x y : Fin n → FieldWeight)
    (p : Fin n → ℝ) {a : ℝ} (ha : 0≤a)
    (he : ∀ i, |compactV (x i)-compactV (y i)| ≤ a) :
    |weightedForm J varianceKernel x p-weightedForm J varianceKernel y p| ≤
      a*euclideanOpNorm J*∑ i, p i^2 := by
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => compactV (x i)-compactV (y i))
  have heq : (Matrix.of J)*Matrix.diagonal (fun i => compactV (x i)) -
      (Matrix.of J)*Matrix.diagonal (fun i => compactV (y i)) = (Matrix.of J)*D := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.sub_apply,Matrix.mul_diagonal,Matrix.of_apply,D]
    ring
  rw [weightedForm_variance_eq,weightedForm_variance_eq,←quadratic_sub,heq]
  have hnD : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) D‖ ≤ a :=
    matrix_diagonal_opNorm_le _ a ha he
  have hn : euclideanOpNorm ((Matrix.of J)*D) ≤ a*euclideanOpNorm J := by
    unfold euclideanOpNorm
    rw [map_mul,mul_comm a]
    apply (norm_mul_le _ _).trans
    exact mul_le_mul_of_nonneg_left hnD (norm_nonneg _)
  exact (quadratic_abs_le _ p).trans (mul_le_mul_of_nonneg_right hn
    (Finset.sum_nonneg (fun i _ => sq_nonneg (p i))))

lemma compactForm_field_bound (J : Interaction n) (hJ : ∀ i j, J i j=J j i)
    (x y : Fin n → FieldWeight) (p : Fin n → ℝ) {a C : ℝ} (ha : 0≤a) (hC : 0≤C)
    (hr : ∀ i, ∑ j, J i j^2 ≤ C)
    (hv : ∀ i, |compactV (x i)-compactV (y i)| ≤ a)
    (hm : ∀ i j, |meanVarianceKernel (x i,x j)-meanVarianceKernel (y i,y j)| ≤ a)
    (hf : ∀ i j, |compactF (x i,x j)-compactF (y i,y j)| ≤ a)
    (hk : ∀ i j, |compactK (x i,x j)-compactK (y i,y j)| ≤ a) :
    |compactForm J x p-compactForm J y p| ≤ a*(euclideanOpNorm J+4*C)*(∑ i, p i^2) := by
  have hr' (i : Fin n) : ∑ j, |J i j^2| ≤ C := by simpa only [abs_pow,sq_abs] using hr i
  have hc' (j : Fin n) : ∑ i, |J i j^2| ≤ C := by simpa only [hJ,abs_pow,sq_abs] using hr j
  let L := weightedForm J varianceKernel x p-weightedForm J varianceKernel y p
  let M := weightedForm (fun i j => J i j^2) meanVarianceKernel x p-weightedForm (fun i j => J i j^2) meanVarianceKernel y p
  let D := diagonalForm (fun i j => J i j^2) compactF x p-diagonalForm (fun i j => J i j^2) compactF y p
  let K := weightedForm (fun i j => J i j^2) compactK x p-weightedForm (fun i j => J i j^2) compactK y p
  have hid : compactForm J x p-compactForm J y p=L+2*M+D+K := by dsimp [compactForm,L,M,D,K]; ring
  have hL : |L| ≤ a*euclideanOpNorm J*(∑ i, p i^2) := weightedForm_variance_field_bound J x y p ha hv
  have hM : |M| ≤ a*C*(∑ i, p i^2) := weightedForm_field_bound _ _ x y p ha hC hr' hc' hm
  have hD : |D| ≤ a*C*(∑ i, p i^2) := diagonalForm_field_bound _ _ x y p ha hr' hf
  have hK : |K| ≤ a*C*(∑ i, p i^2) := weightedForm_field_bound _ _ x y p ha hC hr' hc' hk
  rw [hid]
  have ht := (abs_add_le (L+2*M+D) K).trans
    (add_le_add ((abs_add_le (L+2*M) D).trans (add_le_add (abs_add_le L (2*M)) le_rfl)) le_rfl)
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at ht
  nlinarith only [ht,hL,hM,hD,hK]

lemma form_kernels_uniform {a : ℝ} (ha : 0<a) :
    ∃ δ : ℝ, 0<δ ∧ ∀ x y x' y' : FieldWeight,
      dist x x'<δ → dist y y'<δ →
      |compactV y-compactV y'|≤a ∧
      |meanVarianceKernel (x,y)-meanVarianceKernel (x',y')|≤a ∧
      |compactF (x,y)-compactF (x',y')|≤a ∧
      |compactK (x,y)-compactK (x',y')|≤a := by
  let G : FieldWeight × FieldWeight → Fin 4 → ℝ := fun p =>
    ![varianceKernel p,meanVarianceKernel p,compactF p,compactK p]
  have hG : Continuous G := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_varianceKernel
    · exact continuous_meanVarianceKernel
    · exact continuous_compactF
    · exact continuous_compactK
  obtain ⟨δ,hδ,hcont⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hG) a ha
  refine ⟨δ,hδ,?_⟩
  intro x y x' y' hx hy
  have hh := (dist_pi_lt_iff ha).mp (hcont (a := (x,y)) (b := (x',y'))
    (by simpa only [Prod.dist_eq,max_lt_iff] using And.intro hx hy))
  exact ⟨(hh 0).le,(hh 1).le,(hh 2).le,(hh 3).le⟩

lemma compactForm_uniform_field_change {C K u : ℝ} (hC : 0≤C) (hK : 0≤K) (hu : 0<u) :
    ∃ δ : ℝ, 0<δ ∧ ∀ {n : ℕ} (J : Interaction n), (∀ i j, J i j=J j i) →
      euclideanOpNorm J≤K → (∀ i, ∑ j, J i j^2≤C) →
      ∀ H H' p : Fin n → ℝ, (∀ i, |H i-H' i|≤δ) →
      |compactForm J (fun i => compactWeight (H i)) p-
        compactForm J (fun i => compactWeight (H' i)) p| ≤ u*(∑ i, p i^2) := by
  let a := u/(K+4*C+1)
  have ha : 0<a := by dsimp [a]; positivity
  obtain ⟨δ,hδ,hcont⟩ := form_kernels_uniform ha
  refine ⟨δ/2,by positivity,?_⟩
  intro n J hJ hnorm hr H H' p hnear
  have hd (i : Fin n) : dist (compactWeight (H i)) (compactWeight (H' i))<δ := by
    have hb := compactWeight_lipschitz.dist_le_mul (H i) (H' i)
    simp only [NNReal.coe_one,one_mul,Real.dist_eq] at hb
    exact lt_of_le_of_lt (hb.trans (hnear i)) (by linarith)
  have hb := compactForm_field_bound J hJ _ _ p ha.le hC hr
    (fun i => (hcont _ _ _ _ (hd i) (hd i)).1)
    (fun i j => (hcont _ _ _ _ (hd i) (hd j)).2.1)
    (fun i j => (hcont _ _ _ _ (hd i) (hd j)).2.2.1)
    (fun i j => (hcont _ _ _ _ (hd i) (hd j)).2.2.2)
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hden : 0<K+4*C+1 := by positivity
  have hid : a*(K+4*C+1)=u := div_mul_cancel₀ _ hden.ne'
  nlinarith only [hid,mul_nonneg ha.le (sub_nonneg.mpr hnorm),ha.le]

end SKRatio.Planted

end

end OAI
