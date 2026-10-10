import OAI.Analysis.KadisonSimilarity.Tracial.FullColumnTheorem
import OAI.Analysis.KadisonSimilarity.Representation.IsometricTransfer
import OAI.Analysis.KadisonSimilarity.Representation.OrthogonalColumns
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

namespace OAI

/-! The properly infinite commutator estimate. Internal orthogonal isometries
supply the row, and Dickson supplies its actual commutator error bounds. -/

noncomputable section
namespace KadisonSimilarity

open scoped CStarAlgebra

section NativeMatrixNorm

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem norm_cstarMatrix_conjTranspose_le {m n : Type*} [Fintype m] [Fintype n]
    (M : CStarMatrix m n A) : ‖M.conjTranspose‖ ≤ ‖M‖ := by
  apply CStarMatrix.norm_le_of_forall_inner_le (C := ‖M‖₊)
  intro v w
  have hi := CStarMatrix.inner_toCLM_conjTranspose_right (M := M) (v := w) (w := v)
  have hn := congrArg norm hi
  calc
    _ = ‖inner A (CStarMatrix.toCLM M w) v‖ := hn
    _ ≤ ‖CStarMatrix.toCLM M w‖ * ‖v‖ := CStarModule.norm_inner_le _
    _ ≤ (‖M‖ * ‖w‖) * ‖v‖ := mul_le_mul_of_nonneg_right
      ((CStarMatrix.toCLM M).le_opNorm w) (norm_nonneg v)
    _ = (‖M‖₊ : ℝ) * ‖v‖ * ‖w‖ := by simp only [coe_nnnorm]; ring

/-- Rectangular conjugate transpose preserves the native C-star matrix norm. -/
theorem norm_cstarMatrix_conjTranspose {m n : Type*} [Fintype m] [Fintype n]
    (M : CStarMatrix m n A) : ‖M.conjTranspose‖ = ‖M‖ := by
  apply le_antisymm (norm_cstarMatrix_conjTranspose_le M)
  have hMM : M.conjTranspose.conjTranspose = M := by
    ext i j
    simp [CStarMatrix.conjTranspose_apply]
  simpa only [hMM] using norm_cstarMatrix_conjTranspose_le M.conjTranspose

/-- The adjoint column of orthogonal internal isometries is contractive in
the native C-star matrix norm. -/
theorem norm_cstar_isometry_adjoint_column_le_one {n : ℕ} (v : Fin n → A)
    (hv : ∀ i j, star (v i) * v j = if i = j then 1 else 0) :
    ‖CStarMatrix.ofMatrix (fun i (_ : Fin 1) => star (v i))‖ ≤ 1 := by
  let W : CStarMatrix (Fin n) (Fin 1) A := CStarMatrix.ofMatrix (fun i _ => star (v i))
  change ‖CStarMatrix.toCLM W‖ ≤ 1
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have hterm (i j : Fin n) :
      x i * star (v i) * (v j * star (x j)) =
        if i = j then x i * star (x j) else 0 := by
    calc
      _ = x i * (star (v i) * v j) * star (x j) := by noncomm_ring
      _ = _ := by rw [hv]; split_ifs <;> simp
  have hi : inner A (CStarMatrix.toCLM W x) (CStarMatrix.toCLM W x) = inner A x x := by
    have hout : CStarMatrix.toCLM W x =
        (WithCStarModule.equiv A (Fin 1 → A)).symm
          (fun _ => ∑ i : Fin n, x i * star (v i)) :=
      CStarMatrix.toCLM_apply_eq_sum
    rw [hout]
    change (∑ _ : Fin 1, (∑ i : Fin n, x i * star (v i)) *
      star (∑ j : Fin n, x j * star (v j))) = ∑ i : Fin n, x i * star (x i)
    simp only [Finset.univ_unique, Finset.sum_singleton, star_sum, star_mul, star_star,
      Finset.mul_sum, Finset.sum_mul]
    simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hn : ‖CStarMatrix.toCLM W x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [CStarModule.norm_sq_eq A, CStarModule.norm_sq_eq A, hi]
  have heq : ‖CStarMatrix.toCLM W x‖ = ‖x‖ := by
    nlinarith [norm_nonneg (CStarMatrix.toCLM W x), norm_nonneg x]
  simpa only [one_mul] using heq.le

/-- The row of internal orthogonal isometries has native matrix norm at most one. -/
theorem norm_cstar_isometry_row_le_one {n : ℕ} (v : Fin n → A)
    (hv : ∀ i j, star (v i) * v j = if i = j then 1 else 0) :
    ‖CStarMatrix.ofMatrix (fun (_ : Fin 1) i => v i)‖ ≤ 1 := by
  rw [← norm_cstarMatrix_conjTranspose]
  exact norm_cstar_isometry_adjoint_column_le_one v hv

end NativeMatrixNorm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A von Neumann algebra is closed in the operator norm. -/
instance vonNeumannAlgebra_isClosed (P : VonNeumannAlgebra H) :
    IsClosed (P : Set (H →L[ℂ] H)) := by
  change IsClosed P.carrier
  rw [← P.centralizer_centralizer']
  exact Set.isClosed_centralizer _

instance vonNeumannAlgebra_smulMemClass :
    SMulMemClass (VonNeumannAlgebra H) ℂ (H →L[ℂ] H) where
  smul_mem {s} c {_x} hx := s.toStarSubalgebra.smul_mem hx c

/-- The actual row of a finite family of internal isometries. -/
def internalIsometryRow (P : VonNeumannAlgebra H) {n : ℕ} (v : Fin n → P) :
    HilbertCopies H n →L[ℂ] H := sumColumns (fun i => (v i : H →L[ℂ] H))

theorem internal_isometry_relation (P : VonNeumannAlgebra H) {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then 1 else 0) (i j : Fin n) :
    (v i : H →L[ℂ] H).adjoint.comp (v j : H →L[ℂ] H) =
      if i = j then ContinuousLinearMap.id ℂ H else 0 := by
  have h := congrArg (fun a : P => (a : H →L[ℂ] H)) (hv i j)
  split_ifs at h ⊢ <;> exact h

theorem internalIsometryRow_adjoint_self (P : VonNeumannAlgebra H) {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then 1 else 0) :
    (internalIsometryRow P v).adjoint.comp (internalIsometryRow P v) =
      ContinuousLinearMap.id ℂ (HilbertCopies H n) := by
  ext x i
  change (sumColumns (fun i => (v i : H →L[ℂ] H))).adjoint
    (sumColumns (fun i => (v i : H →L[ℂ] H)) x) i = x i
  rw [sumColumns_adjoint_apply, sumColumns_apply, map_sum]
  have ht (j : Fin n) : (v i : H →L[ℂ] H).adjoint ((v j : H →L[ℂ] H) (x j)) =
      if i = j then x j else 0 := by
    have h := congrArg (fun T : H →L[ℂ] H => T (x j)) (internal_isometry_relation P v hv i j)
    split_ifs with hij
    · simpa only [hij, ↓reduceIte, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using h
    · simpa only [hij, ↓reduceIte, ContinuousLinearMap.comp_apply, zero_apply] using h
  simp only [ht, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

def vonNeumannRepresentation (P : VonNeumannAlgebra H) : P →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  P.toStarSubalgebra.subtype

def vonNeumannInnerDerivation (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) :
    P →L[ℂ] (H →L[ℂ] H) :=
  cornerCommutator (vonNeumannRepresentation P) (vonNeumannRepresentation P) Y

@[simp] theorem vonNeumannInnerDerivation_apply (P : VonNeumannAlgebra H)
    (Y : H →L[ℂ] H) (a : P) : vonNeumannInnerDerivation P Y a = commutator Y (a : H →L[ℂ] H) := rfl

theorem norm_vonNeumannInnerDerivation (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) :
    ‖vonNeumannInnerDerivation P Y‖ = scalarCommutatorNorm P Y := by
  unfold scalarCommutatorNorm
  congr 1

/-- Dickson's row estimate gives the actual error of the internal isometry row. -/
theorem internalIsometryRow_error (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H)
    (dickson : DicksonTwoBound (A := P) (RectangularSum H H))
    {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then 1 else 0) :
    ‖Y.comp (internalIsometryRow P v) - (internalIsometryRow P v).comp (amplify Y n)‖ ≤
      (4 * Real.sqrt 2) * scalarCommutatorNorm P Y := by
  let δ := vonNeumannInnerDerivation P Y
  let W : Matrix (Fin 1) (Fin n) P := fun _ i => v i
  have hδ := (rectangularDerivation_row_column (vonNeumannRepresentation P)
    (vonNeumannRepresentation P) δ
    (cornerCommutator_leibniz (vonNeumannRepresentation P) (vonNeumannRepresentation P) Y)
    dickson).1 n W
  have heq (x : HilbertCopies H n) :
      (rectangularMatrixOperator (W.map δ) x) 0 =
        (Y.comp (internalIsometryRow P v) - (internalIsometryRow P v).comp (amplify Y n)) x := by
    rw [rectangularMatrixOperator_apply, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply]
    simp only [internalIsometryRow, sumColumns_apply, amplify_apply]
    change (∑ i, (Y ((v i : H →L[ℂ] H) (x i)) - (v i : H →L[ℂ] H) (Y (x i)))) =
      Y (∑ i, (v i : H →L[ℂ] H) (x i)) - ∑ i, (v i : H →L[ℂ] H) (Y (x i))
    rw [map_sum, Finset.sum_sub_distrib]
  have hnorm :
      ‖Y.comp (internalIsometryRow P v) - (internalIsometryRow P v).comp (amplify Y n)‖ ≤
        ‖rectangularMatrixOperator (W.map δ)‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (rectangularMatrixOperator (W.map δ)))
    intro x
    rw [← heq]
    exact (PiLp.norm_apply_le _ 0).trans ((rectangularMatrixOperator (W.map δ)).le_opNorm x)
  calc
    _ ≤ ((4 * Real.sqrt 2) * ‖δ‖) * ‖CStarMatrix.ofMatrix W‖ := hnorm.trans hδ
    _ ≤ ((4 * Real.sqrt 2) * ‖δ‖) * 1 := mul_le_mul_of_nonneg_left
      (norm_cstar_isometry_row_le_one v hv) (by positivity)
    _ = _ := by rw [mul_one, norm_vonNeumannInnerDerivation]

/-- Dickson's column estimate gives the adjoint-row error independently of
whether the operator being commuted is selfadjoint. -/
theorem internalIsometryRow_adjoint_error (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H)
    (dickson : DicksonTwoBound (A := P) (RectangularSum H H))
    {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then 1 else 0) :
    ‖(amplify Y n).comp (internalIsometryRow P v).adjoint -
        (internalIsometryRow P v).adjoint.comp Y‖ ≤
      (4 * Real.sqrt 2) * scalarCommutatorNorm P Y := by
  let δ := vonNeumannInnerDerivation P Y
  let W : Matrix (Fin n) (Fin 1) P := fun i _ => star (v i)
  have hδ := (rectangularDerivation_row_column (vonNeumannRepresentation P)
    (vonNeumannRepresentation P) δ
    (cornerCommutator_leibniz (vonNeumannRepresentation P) (vonNeumannRepresentation P) Y)
    dickson).2 n W
  have heq (x : H) :
      rectangularMatrixOperator (W.map δ) (PiLp.single 2 0 x) =
        ((amplify Y n).comp (internalIsometryRow P v).adjoint -
          (internalIsometryRow P v).adjoint.comp Y) x := by
    ext i
    have hzero : (default : Fin 1) = 0 := Subsingleton.elim _ _
    simp only [rectangularMatrixOperator_apply, PiLp.single_apply, Finset.univ_unique,
      Finset.sum_singleton, hzero, ↓reduceIte, sub_apply, ContinuousLinearMap.comp_apply]
    change (δ (star (v i))) x =
      Y ((internalIsometryRow P v).adjoint x i) -
        (internalIsometryRow P v).adjoint (Y x) i
    rw [show (internalIsometryRow P v).adjoint x i = (v i : H →L[ℂ] H).adjoint x
      from sumColumns_adjoint_apply _ _ _,
      show (internalIsometryRow P v).adjoint (Y x) i = (v i : H →L[ℂ] H).adjoint (Y x)
      from sumColumns_adjoint_apply _ _ _]
    rfl
  have hnorm :
      ‖(amplify Y n).comp (internalIsometryRow P v).adjoint -
        (internalIsometryRow P v).adjoint.comp Y‖ ≤ ‖rectangularMatrixOperator (W.map δ)‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (rectangularMatrixOperator (W.map δ)))
    intro x
    rw [← heq]
    simpa only [PiLp.norm_single] using
      (rectangularMatrixOperator (W.map δ)).le_opNorm (PiLp.single 2 0 x)
  calc
    _ ≤ ((4 * Real.sqrt 2) * ‖δ‖) * ‖CStarMatrix.ofMatrix W‖ := hnorm.trans hδ
    _ ≤ ((4 * Real.sqrt 2) * ‖δ‖) * 1 := mul_le_mul_of_nonneg_left
      (norm_cstar_isometry_adjoint_column_le_one v hv) (by positivity)
    _ = _ := by rw [mul_one, norm_vonNeumannInnerDerivation]

theorem internalIsometryRow_compression_mem (P : VonNeumannAlgebra H) {n : ℕ}
    (v : Fin n → P) (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) (hX : ∀ i j, X i j ∈ P) :
    (internalIsometryRow P v).comp
      ((matrixOperator X).comp (internalIsometryRow P v).adjoint) ∈ P := by
  have heq : (internalIsometryRow P v).comp
      ((matrixOperator X).comp (internalIsometryRow P v).adjoint) =
      ∑ i : Fin n, ∑ j : Fin n, (v i : H →L[ℂ] H) * X i j * star (v j : H →L[ℂ] H) := by
    ext x
    simp [internalIsometryRow, sumColumns_apply, matrixOperator_apply, map_sum,
      sumColumns_adjoint_apply, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint]
  rw [heq]
  apply P.sum_mem
  intro i _
  apply P.sum_mem
  intro j _
  exact P.mul_mem (P.mul_mem (v i).property (hX i j))
    (show star (v j : H →L[ℂ] H) ∈ P from star_mem (v j).property)

/-- Existence of finite families of orthogonal isometries. For a properly
infinite algebra this is supplied by its projection classification. -/
def HasInternalIsometryRows (P : VonNeumannAlgebra H) : Prop :=
  ∀ n : ℕ, ∃ v : Fin n → P, ∀ i j, star (v i) * v j = if i = j then 1 else 0

/-- The properly infinite estimate is derived from internal isometries and
the published row/column estimate, with no row-error hypotheses. -/
theorem properlyInfinite_commutatorEstimate (P : VonNeumannAlgebra H)
    (isometries : HasInternalIsometryRows P)
    (dickson : DicksonTwoBound (A := P) (RectangularSum H H)) :
    CommutatorEstimate P (1 + 2 * (4 * Real.sqrt 2)) := by
  intro Y n X hX
  obtain ⟨v, hv⟩ := isometries n
  apply norm_commutator_le_isometric_transfer Y (amplify Y n) (matrixOperator X)
    (internalIsometryRow P v) (internalIsometryRow_adjoint_self P v hv)
    (scalarCommutatorNorm_nonneg P Y) (by positivity)
  · exact norm_commutator_le_scalarCommutatorNorm P Y _ (internalIsometryRow_compression_mem P v X hX)
  · exact internalIsometryRow_error P Y dickson v hv
  · exact internalIsometryRow_adjoint_error P Y dickson v hv

end KadisonSimilarity

end

end OAI
