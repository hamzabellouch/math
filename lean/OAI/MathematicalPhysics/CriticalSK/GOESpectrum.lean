import OAI.MathematicalPhysics.CriticalSK.GaussianMatrices
import OAI.MathematicalPhysics.CriticalSK.Resolvent

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open scoped BigOperators
open Matrix Polynomial
open scoped BigOperators Topology
open Filter
namespace CriticalSK

open scoped InnerProductSpace

lemma symmetric_eigenvalue_norm_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A B : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (hB : B.toLinearMap.IsSymmetric)
    {n : ℕ} (hn : finrank ℝ E = n) (i : Fin n) :
    |hA.eigenvalues hn i - hB.eigenvalues hn i| ≤ ‖A-B‖ := by
  refine eigenvalue_form_comparison hA hB hn (S := Set.univ) (Φ := fun _ => ‖A-B‖)
    (by intro a ha b hb hab; dsimp; linarith) (by intro a ha b hb hab; dsimp; linarith)
    (fun _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _) ?_ i
  intro x hx
  calc
    _ = |inner ℝ x ((A-B) x)| := by rw [_root_.sub_apply,inner_sub_right]; rfl
    _ ≤ ‖x‖*‖(A-B) x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖*(‖A-B‖*‖x‖) := mul_le_mul_of_nonneg_left ((A-B).le_opNorm x) (norm_nonneg _)
    _ = _ := by rw [hx]; ring

def gaussianMatrixCLM {n : ℕ} (A : GaussianMatrix (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (Matrix.toLpLin 2 2 (fun i j => A i j)).toContinuousLinearMap

def gaussianMatrixToCLM (n : ℕ) : GaussianMatrix (Fin n) →ₗ[ℝ]
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) where
  toFun := gaussianMatrixCLM
  map_add' A B := by
    ext x i
    change (∑ j, (A i j+B i j)*x j) = (∑ j, A i j*x j)+(∑ j, B i j*x j)
    simp only [add_mul,Finset.sum_add_distrib]
  map_smul' r A := by
    ext x i
    change (∑ j, (r*A i j)*x j) = r*(∑ j, A i j*x j)
    simp only [mul_assoc,Finset.mul_sum]

lemma finite_real_linear_continuous {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup F] [NormedSpace ℝ F] (T : D →ₗ[ℝ] F) : Continuous T :=
  T.continuous_of_finiteDimensional

lemma gaussianMatrixCLM_continuous (n : ℕ) : Continuous (gaussianMatrixCLM (n := n)) := by
  change Continuous (gaussianMatrixToCLM n)
  exact finite_real_linear_continuous (gaussianMatrixToCLM n)

lemma gaussianMatrixCLM_symmetric {n : ℕ} (A : GaussianMatrix (Fin n))
    (hA : ∀ i j, A i j = A j i) : (gaussianMatrixCLM A).toLinearMap.IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  ext i j
  exact hA j i

lemma symmetrize_half_entry {n : ℕ} (A : GaussianMatrix (Fin n)) (i j : Fin n) :
    symmetrizeGaussianMatrix (1/2:ℝ) A i j = (A i j + A j i)/2 := by
  change (1/2:ℝ)*(A i j+A j i) = _
  ring

lemma symmetrize_half_symmetric {n : ℕ} (A : GaussianMatrix (Fin n)) :
    ∀ i j, symmetrizeGaussianMatrix (1/2:ℝ) A i j = symmetrizeGaussianMatrix (1/2:ℝ) A j i := by
  intro i j
  rw [symmetrize_half_entry,symmetrize_half_entry,add_comm]

lemma symmetrize_half_eq {n : ℕ} (A : GaussianMatrix (Fin n)) (hA : ∀ i j, A i j = A j i) :
    symmetrizeGaussianMatrix (1/2:ℝ) A = A := by
  ext i j
  rw [symmetrize_half_entry,hA j i]
  ring

def matrixOrderedEigenvalues {n : ℕ} (A : GaussianMatrix (Fin n)) : Fin n → ℝ :=
  (gaussianMatrixCLM_symmetric _ (symmetrize_half_symmetric A)).eigenvalues (by simp : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n)

lemma matrixOrderedEigenvalues_eq {n : ℕ} (A : GaussianMatrix (Fin n))
    (hA : ∀ i j, A i j = A j i) :
    matrixOrderedEigenvalues A = (gaussianMatrixCLM_symmetric A hA).eigenvalues (by simp : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) := by
  unfold matrixOrderedEigenvalues
  congr 2
  exact congrArg gaussianMatrixCLM (symmetrize_half_eq A hA)

lemma matrixOrderedEigenvalues_continuous {n : ℕ} (i : Fin n) :
    Continuous (fun A : GaussianMatrix (Fin n) => matrixOrderedEigenvalues A i) := by
  let F := fun A : GaussianMatrix (Fin n) => gaussianMatrixCLM (symmetrizeGaussianMatrix (1/2:ℝ) A)
  have hc : Continuous F := (gaussianMatrixCLM_continuous n).comp (symmetrizeGaussianMatrix_continuous _)
  rw [continuous_iff_continuousAt]
  intro A
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ,hδ,h⟩ := Metric.continuousAt_iff.mp hc.continuousAt ε hε
  refine ⟨δ,hδ,fun B hB => ?_⟩
  have hh := symmetric_eigenvalue_norm_bound (F B) (F A)
    (gaussianMatrixCLM_symmetric _ (symmetrize_half_symmetric B))
    (gaussianMatrixCLM_symmetric _ (symmetrize_half_symmetric A)) (by simp : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) i
  exact (show dist (matrixOrderedEigenvalues B i) (matrixOrderedEigenvalues A i) ≤ dist (F B) (F A) by
    simpa only [dist_eq_norm,Real.norm_eq_abs,matrixOrderedEigenvalues] using hh).trans_lt (h hB)

lemma orthoMatrix_transpose {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (orthoMatrix U).transpose = orthoMatrix U.symm := by
  ext i j
  have hh := U.inner_map_eq_flip (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j)
  simpa only [EuclideanSpace.inner_basisFun_real,EuclideanSpace.basisFun_inner,
    orthoMatrix,Matrix.transpose_apply] using hh

lemma orthoMatrix_toLpLin {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Matrix.toLpLin 2 2 (orthoMatrix U) = U.toLinearEquiv.toLinearMap := by
  ext x i
  change (∑ j, U (EuclideanSpace.basisFun (Fin n) ℝ j) i * x j) = U x i
  rw [euclidean_isometry_apply_eq_sum]
  apply Finset.sum_congr rfl
  intros
  ring

lemma gaussianMatrixCLM_conjugate {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (A : GaussianMatrix (Fin n)) :
    (gaussianMatrixCLM (conjugateGaussianMatrix U A)).toLinearMap =
      U.toLinearEquiv.conj (gaussianMatrixCLM A).toLinearMap := by
  change Matrix.toLpLin 2 2 (matrixOfGaussian (conjugateGaussianMatrix U A)) = _
  rw [matrixOfGaussian_conjugate,Matrix.toLpLin_mul_same,Matrix.toLpLin_mul_same,
    orthoMatrix_transpose,orthoMatrix_toLpLin,orthoMatrix_toLpLin]
  rfl

lemma matrixOrderedEigenvalues_conjugate {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (A : GaussianMatrix (Fin n)) (hA : ∀ i j, A i j = A j i) :
    matrixOrderedEigenvalues (conjugateGaussianMatrix U A) = matrixOrderedEigenvalues A := by
  rw [matrixOrderedEigenvalues_eq _ (conjugate_symmetric U A hA),matrixOrderedEigenvalues_eq _ hA]
  apply (LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff _ _ _ _).mpr
  rw [gaussianMatrixCLM_conjugate,LinearEquiv.charpoly_conj]

lemma matrixOrderedEigenvalues_triReduce {n : ℕ}
    (A : GaussianMatrix (Fin n)) (hA : ∀ i j, A i j = A j i) :
    matrixOrderedEigenvalues (triReduce n A) = matrixOrderedEigenvalues A := by
  rw [triReduce_conjugate n A hA]
  exact matrixOrderedEigenvalues_conjugate _ _ hA

lemma matrixOrderedEigenvalues_sample (n : ℕ) (ω : TriSample n) :
    matrixOrderedEigenvalues (WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => triSampleMatrix n ω i j))) =
      sampleEigenvalues n ω := by
  have hA : ∀ i j, triSampleMatrix n ω i j = triSampleMatrix n ω j i := by
    intro i j
    have hh := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => M i j) (triSampleMatrix_hermitian n ω)
    simpa only [Matrix.conjTranspose_apply,star_trivial] using hh.symm
  rw [matrixOrderedEigenvalues_eq _ hA]
  rfl

def triEntriesLaw (n : ℕ) (s : ℝ) : Measure (Fin n → ℝ × ℝ) :=
  Measure.pi fun i => (gaussianReal 0 (4*s^2).toNNReal).prod (columnNormLaw (n-i.val-1) s)

instance triEntriesLaw_probability (n : ℕ) (s : ℝ) : IsProbabilityMeasure (triEntriesLaw n s) := by
  unfold triEntriesLaw; infer_instance

def triEntriesMatrix : (n : ℕ) → (Fin n → ℝ × ℝ) → GaussianMatrix (Fin n)
  | 0, _ => 0
  | n+1, p => assembleTri n ((p 0).1, (p 0).2, triEntriesMatrix n (fun i => p i.succ))

lemma triEntriesMatrix_measurable (n : ℕ) : Measurable (triEntriesMatrix n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (assembleTri_measurable n).comp
      (((measurable_pi_apply (0 : Fin (n+1))).fst).prodMk
        (((measurable_pi_apply (0 : Fin (n+1))).snd).prodMk
          (ih.comp (Measurable.of_eval (fun i => measurable_pi_apply i.succ)))))

lemma triEntriesLaw_split (n : ℕ) (s : ℝ) :
    MeasurePreserving (fun p : Fin (n+1) → ℝ × ℝ => (p 0, fun i : Fin n => p i.succ))
      (triEntriesLaw (n+1) s)
      (((gaussianReal 0 (4*s^2).toNNReal).prod (columnNormLaw n s)).prod (triEntriesLaw n s)) := by
  convert measurePreserving_piFinSuccAbove
    (fun i : Fin (n+1) => (gaussianReal 0 (4*s^2).toNNReal).prod (columnNormLaw (n+1-i.val-1) s)) 0 using 1
  · rfl
  · rfl
  · simp only [Fin.val_zero,Nat.sub_zero,Nat.add_sub_cancel_right,triEntriesLaw,
      Fin.succAbove_zero,Fin.val_succ,Nat.add_sub_add_right]

lemma probability_eq_on_subsingleton {Ω : Type*} [MeasurableSpace Ω] [Subsingleton Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : μ=ν := by
  apply Measure.ext
  intro t _
  by_cases ht : t.Nonempty
  · obtain ⟨x,hx⟩ := ht
    have he : t=Set.univ := Set.eq_univ_of_forall (fun y => by simpa only [Subsingleton.elim y x] using hx)
    simp only [he,measure_univ]
  · simp only [Set.not_nonempty_iff_eq_empty.mp ht,measure_empty]

lemma triEntriesMatrix_preserving (n : ℕ) (s : ℝ) :
    MeasurePreserving (triEntriesMatrix n) (triEntriesLaw n s) (triMatrixLaw n s) := by
  induction n with
  | zero =>
    refine ⟨triEntriesMatrix_measurable 0,?_⟩
    exact probability_eq_on_subsingleton _ _
  | succ n ih =>
    have hp := (MeasurePreserving.id ((gaussianReal 0 (4*s^2).toNNReal).prod (columnNormLaw n s))).prod ih
    have ha := measurePreserving_prodAssoc (gaussianReal 0 (4*s^2).toNNReal)
      (columnNormLaw n s) (triMatrixLaw n s)
    have hb : MeasurePreserving (assembleTri n)
        ((gaussianReal 0 (4*s^2).toNNReal).prod ((columnNormLaw n s).prod (triMatrixLaw n s)))
        (triMatrixLaw (n+1) s) := ⟨assembleTri_measurable n,rfl⟩
    exact hb.comp (ha.comp (hp.comp (triEntriesLaw_split n s)))

lemma triEntriesMatrix_apply (n : ℕ) (p : Fin n → ℝ × ℝ) (i j : Fin n) :
    triEntriesMatrix n p i j =
      (if i=j then (p i).1 else 0)+(if i.val+1=j.val then (p i).2 else 0)+
        (if j.val+1=i.val then (p j).2 else 0) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => simp [triEntriesMatrix,assembleTri,borderMatrix_zero_zero]
      | succ j =>
        rw [triEntriesMatrix,assembleTri,borderMatrix_zero_succ]
        have he : (1=j.val+1) ↔ (j.val=0) := by omega
        have hn : ¬(j.val+1+1=0) := by omega
        simp only [Ne.symm (Fin.succ_ne_zero j),Fin.val_zero,Fin.val_succ,hn,ite_false,
          zero_add,add_zero,he]
        change (p 0).2*(if j.val=0 then 1 else 0) = _
        split_ifs <;> simp only [mul_one,mul_zero]
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        rw [triEntriesMatrix,assembleTri,borderMatrix_succ_zero]
        have he : (1=i.val+1) ↔ (i.val=0) := by omega
        have hn : ¬(i.val+1+1=0) := by omega
        simp only [Fin.succ_ne_zero i,Fin.val_zero,Fin.val_succ,hn,ite_false,
          zero_add,add_zero,he]
        change (p 0).2*(if i.val=0 then 1 else 0) = _
        split_ifs <;> simp only [mul_one,mul_zero]
      | succ j =>
        simpa only [triEntriesMatrix,assembleTri,borderMatrix_succ_succ,Fin.succ_inj,
          Fin.val_succ,Nat.add_right_cancel_iff] using ih (fun k => p k.succ) i j

def goeScale (n : ℕ) : ℝ := (Real.sqrt (2*(n+1:ℝ)))⁻¹

lemma goeScale_square (n : ℕ) : 2*(goeScale n)^2 = (n+1:ℝ)⁻¹ := by
  have hn : (0:ℝ) < n+1 := by positivity
  unfold goeScale
  rw [inv_pow,Real.sq_sqrt (by positivity)]
  field_simp

lemma goeScale_diagonal (n : ℕ) : 4*(goeScale n)^2 = 2/(n+1:ℝ) := by
  have := goeScale_square n
  rw [div_eq_mul_inv]
  nlinarith

lemma gaussian_div_sqrt_preserving (n : ℕ) :
    MeasurePreserving (fun x : ℝ => x/Real.sqrt (n+1:ℝ)) (gaussianReal 0 1)
      (gaussianReal 0 (2*(goeScale n)^2).toNNReal) := by
  refine ⟨by fun_prop,?_⟩
  rw [gaussianReal_map_div_const,zero_div,goeScale_square]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_mk,Real.coe_toNNReal _ (by positivity : 0 ≤ (n+1:ℝ)⁻¹)]
  rw [Real.sq_sqrt (by positivity),one_div]

lemma chi_eq_norm (m : ℕ) (x : Fin m → ℝ) :
    chi m x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [chi,chiSquare,Real.norm_eq_abs,sq_abs]

lemma columnNormLaw_scale (n m : ℕ) :
    columnNormLaw m (goeScale n) =
      (standardGaussianProduct m).map (fun x => chi m x/Real.sqrt (n+1:ℝ)) := by
  have hp := measurePreserving_pi (fun _ : Fin m => gaussianReal 0 1)
    (fun _ : Fin m => gaussianReal 0 (2*(goeScale n)^2).toNNReal)
    (fun _ => gaussian_div_sqrt_preserving n)
  have hh := (columnNorm_preserving m (goeScale n)).comp hp
  have he : (fun x : Fin m → ℝ => ‖(WithLp.toLp 2 (fun i => x i/Real.sqrt (n+1:ℝ)) : EuclideanSpace ℝ (Fin m))‖) =
      (fun x => chi m x/Real.sqrt (n+1:ℝ)) := by
    funext x
    have hv : (WithLp.toLp 2 (fun i => x i/Real.sqrt (n+1:ℝ)) : EuclideanSpace ℝ (Fin m)) =
        (Real.sqrt (n+1:ℝ))⁻¹ • WithLp.toLp 2 x := by ext i; simp [div_eq_mul_inv,mul_comm]
    rw [hv,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),← chi_eq_norm]
    ring
  have hmap := hh.map_eq
  change (standardGaussianProduct m).map (fun x : Fin m → ℝ =>
    ‖(WithLp.toLp 2 (fun i => x i/Real.sqrt (n+1:ℝ)) : EuclideanSpace ℝ (Fin m))‖) = _ at hmap
  rw [he] at hmap
  exact hmap.symm

lemma columnNormLaw_zero (s : ℝ) : columnNormLaw 0 s = Measure.dirac 0 := by
  unfold columnNormLaw
  have he : (fun v : Fin 0 → ℝ => ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 0))‖) = fun _ => (0:ℝ) := by
    funext v
    rw [show (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 0)) = 0 from Subsingleton.elim _ _,norm_zero]
  rw [he,Measure.map_const,measure_univ,one_smul]

lemma measurePreserving_independent {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)] (μ : Measure Ω) (ν : ∀ i, Measure (β i))
    (f : ∀ i, Ω → β i) (hf : ∀ i, MeasurePreserving (f i) μ (ν i)) (hi : iIndepFun f μ) :
    MeasurePreserving (fun ω i => f i ω) μ (Measure.pi ν) := by
  refine ⟨Measurable.of_eval (fun i => (hf i).measurable),?_⟩
  rw [hi.map_fun_eq_pi_map (fun i => (hf i).aemeasurable)]
  congr 1
  funext i
  exact (hf i).map_eq

lemma diagonalMarginal_scale (n i : ℕ) :
    diagonalMarginal n i = gaussianReal 0 (4*(goeScale n)^2).toNNReal := by
  rw [goeScale_diagonal]
  unfold diagonalMarginal
  congr 1
  apply NNReal.coe_injective
  rw [Real.coe_toNNReal _ (by positivity : 0 ≤ 2/(n+1:ℝ))]
  rfl

lemma diagonalFinite_preserving (n : ℕ) :
    MeasurePreserving (fun a : ℕ → ℝ => fun i : Fin (n+1) => a i.val)
      (diagonalLaw n) (Measure.pi fun _ => gaussianReal 0 (4*(goeScale n)^2).toNNReal) := by
  have hi : iIndepFun (fun i : ℕ => fun a : ℕ → ℝ => a i) (diagonalLaw n) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  exact measurePreserving_independent _ _ _
    (fun i => by simpa only [diagonalLaw,diagonalMarginal_scale] using measurePreserving_eval_infinitePi (diagonalMarginal n) i.val)
    (hi.precomp Fin.val_injective)

def finiteChiEntry (n i : ℕ) (x : Fin (chiRowDim n i) → ℝ) : ℝ :=
  if i<n then chi (chiRowDim n i) x/Real.sqrt (n+1:ℝ) else 0

lemma finiteChiEntry_measurable (n i : ℕ) : Measurable (finiteChiEntry n i) := by
  unfold finiteChiEntry
  split_ifs
  · exact (chi_measurable _).div_const _
  · exact measurable_const

lemma finiteChiEntry_preserving (n i : ℕ) :
    MeasurePreserving (finiteChiEntry n i) (standardGaussianProduct (chiRowDim n i))
      (columnNormLaw (n-i) (goeScale n)) := by
  refine ⟨finiteChiEntry_measurable n i,?_⟩
  change Measure.map (fun x => if i<n then chi (chiRowDim n i) x / Real.sqrt (n+1:ℝ) else 0) _ = _
  by_cases hi : i<n
  · have hd : chiRowDim n i = n-i := by unfold chiRowDim; omega
    simp only [ite_eq_left hi]
    rw [hd, columnNormLaw_scale]
  · have hd : n-i=0 := by omega
    simp only [ite_eq_right hi,hd,columnNormLaw_zero,Measure.map_const,
      measure_univ,one_smul]

lemma chiFinite_preserving (n : ℕ) :
    MeasurePreserving (fun a : ChiRows n => fun i : Fin (n+1) => finiteChiEntry n i.val (a i.val))
      (chiRowLaw n) (Measure.pi fun i => columnNormLaw (n-i.val) (goeScale n)) := by
  have hi : iIndepFun (fun i : ℕ => fun a : ChiRows n => finiteChiEntry n i (a i)) (chiRowLaw n) :=
    iIndepFun_infinitePi (fun i => finiteChiEntry_measurable n i)
  exact measurePreserving_independent _ _ _
    (fun i => (finiteChiEntry_preserving n i.val).comp
      (measurePreserving_eval_infinitePi (fun i => standardGaussianProduct (chiRowDim n i)) i.val))
    (hi.precomp Fin.val_injective)

def sampleEntries (n : ℕ) (ω : TriSample n) (i : Fin (n+1)) : ℝ × ℝ :=
  (ω.1 i.val, finiteChiEntry n i.val (ω.2 i.val))

lemma sampleEntries_preserving (n : ℕ) :
    MeasurePreserving (sampleEntries n) (triLaw n) (triEntriesLaw (n+1) (goeScale n)) := by
  have hp := (diagonalFinite_preserving n).prod (chiFinite_preserving n)
  have he := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin (n+1))
    (fun _ => gaussianReal 0 (4*(goeScale n)^2).toNNReal)
    (fun i => columnNormLaw (n-i.val) (goeScale n))).symm
  convert he.comp hp using 1
  · rfl
  · rfl
  · unfold triEntriesLaw
    congr 1
    funext i
    congr 2
    omega

lemma sampleEntriesMatrix_apply (n : ℕ) (ω : TriSample n) (i j : Fin (n+1)) :
    triEntriesMatrix (n+1) (sampleEntries n ω) i j = triSampleMatrix n ω i j := by
  rw [triEntriesMatrix_apply]
  simp only [sampleEntries,triSampleMatrix,finiteChiEntry]
  congr 1
  · congr 1
    split_ifs with he hi
    · rfl
    · omega
    · rfl
  · split_ifs with he hi
    · rfl
    · omega
    · rfl

lemma sampleMatrix_preserving (n : ℕ) :
    MeasurePreserving (fun ω : TriSample n => WithLp.toLp 2
      (fun i => WithLp.toLp 2 (fun j => triSampleMatrix n ω i j)))
      (triLaw n) (triMatrixLaw (n+1) (goeScale n)) := by
  have hh := (triEntriesMatrix_preserving (n+1) (goeScale n)).comp (sampleEntries_preserving n)
  convert hh using 1
  funext ω
  ext i j
  exact (sampleEntriesMatrix_apply n ω i j).symm

lemma matrixOrderedEigenvalues_measurable (n : ℕ) :
    Measurable (matrixOrderedEigenvalues (n := n)) :=
  Measurable.of_eval (fun i => (matrixOrderedEigenvalues_continuous i).measurable)

lemma goe_sample_eigenvalues_law (n : ℕ) :
    (goeLaw (Fin (n+1)) (goeScale n)).map matrixOrderedEigenvalues =
      (triLaw n).map (sampleEigenvalues n) := by
  have hT : (triMatrixLaw (n+1) (goeScale n)).map matrixOrderedEigenvalues =
      (goeLaw (Fin (n+1)) (goeScale n)).map matrixOrderedEigenvalues := by
    rw [← (triReduce_preserving (n+1) (goeScale n)).map_eq,
      Measure.map_map (matrixOrderedEigenvalues_measurable _) (triReduce_measurable _)]
    apply Measure.map_congr
    filter_upwards [goe_symmetric_ae (ι := Fin (n+1)) (goeScale n)] with A hA
    exact matrixOrderedEigenvalues_triReduce A hA
  rw [← hT,← (sampleMatrix_preserving n).map_eq,
    Measure.map_map (matrixOrderedEigenvalues_measurable _) (sampleMatrix_preserving n).measurable]
  congr 1
  funext ω
  exact matrixOrderedEigenvalues_sample n ω

def spectralGood (n : ℕ) (h s : ℝ) : Set (Fin (n+1) → ℝ) :=
  {lam | ∀ i, |lam i-(2-orderedJacobiGaps n i)| ≤
    edgeError (formA n h) (formB n) (formC n) s (orderedJacobiGaps n i)}

lemma spectralGood_measurable (n : ℕ) (h s : ℝ) : MeasurableSet (spectralGood n h s) := by
  simp only [spectralGood,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le ((measurable_pi_apply i).sub_const _).abs measurable_const

lemma sampleEigenvalues_measurable (n : ℕ) : Measurable (sampleEigenvalues n) := by
  have hc := (matrixOrderedEigenvalues_measurable (n+1)).comp (sampleMatrix_preserving n).measurable
  simpa only [Function.comp_def,matrixOrderedEigenvalues_sample] using hc

lemma goe_spectral_bad_probability (n : ℕ) {h s : ℝ} (hh : 0 ≤ h) (hs : 0 < s)
    (hscale : scaleEnergy (Nat.clog 8 (n+1)) 0 ≤ s)
    (hsmall : formA n h*(3/8:ℝ)*s^(-5/8:ℝ)+formC n ≤ 1) :
    (goeLaw (Fin (n+1)) (goeScale n)).real
      (matrixOrderedEigenvalues ⁻¹' (spectralGood n h s)ᶜ) ≤ 32*Real.exp (-h^2) := by
  have he := congrArg (fun μ : Measure (Fin (n+1) → ℝ) => μ.real (spectralGood n h s)ᶜ)
    (goe_sample_eigenvalues_law n)
  simp only [Measure.real,Measure.map_apply (matrixOrderedEigenvalues_measurable _)
    (spectralGood_measurable n h s).compl,Measure.map_apply (sampleEigenvalues_measurable n)
    (spectralGood_measurable n h s).compl] at he
  rw [show (goeLaw (Fin (n+1)) (goeScale n)).real
    (matrixOrderedEigenvalues ⁻¹' (spectralGood n h s)ᶜ) =
      (triLaw n).real (sampleEigenvalues n ⁻¹' (spectralGood n h s)ᶜ) from he]
  apply (measureReal_mono ?_).trans (triBad_probability n h)
  intro ω hω
  by_contra hn
  exact hω (triSample_eigenvalue_good n hh hs hscale hsmall hn)

end CriticalSK

end

end OAI
