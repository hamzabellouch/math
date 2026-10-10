import OAI.Analysis.KadisonSimilarity.Tracial.CStarMatrixPadding
import OAI.Analysis.KadisonSimilarity.Tracial.MatrixTracialGNS
import Mathlib.Data.Matrix.Composition

namespace OAI

/-! # Flattening nested matrix and Hilbert-array coordinates -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

private theorem sum_fin_prod {M : Type*} [AddCommMonoid M] (p q : ℕ)
    (f : Fin (p * q) → M) :
    ∑ k : Fin (p * q), f k = ∑ i : Fin p, ∑ j : Fin q, f (finProdFinEquiv (i, j)) := by
  simpa only [Fintype.sum_prod_type] using
    (Fintype.sum_equiv (finProdFinEquiv : Fin p × Fin q ≃ Fin (p * q))
      (fun ij => f (finProdFinEquiv ij)) f (fun _ => rfl)).symm


section MatrixFlattening

variable {A : Type*} [CStarAlgebra A]

private theorem sum_cstarMatrix_apply {p q : ℕ}
    (f : Fin p → CStarMatrix (Fin q) (Fin q) A) (k l : Fin q) :
    (∑ s : Fin p, f s) k l = ∑ s : Fin p, f s k l := by
  have hs (s : Finset (Fin p)) : (∑ i ∈ s, f i) k l = ∑ i ∈ s, f i k l := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, CStarMatrix.add_apply, ih]
  exact hs Finset.univ

/-- First flatten block matrices to a product index. -/
def blockMatrixProductEquiv (p q : ℕ) :
    CStarMatrix (Fin p) (Fin p) (CStarMatrix (Fin q) (Fin q) A) ≃⋆ₐ[ℂ]
      CStarMatrix (Fin p × Fin q) (Fin p × Fin q) A where
  toFun X := CStarMatrix.ofMatrix fun i j => X i.1 j.1 i.2 j.2
  invFun X := CStarMatrix.ofMatrix fun i j =>
    CStarMatrix.ofMatrix fun k l => X (i, k) (j, l)
  left_inv X := by ext i j k l; rfl
  right_inv X := by ext i j; rfl
  map_add' X Y := by ext i j; rfl
  map_smul' c X := by ext i j; rfl
  map_star' X := by ext i j; rfl
  map_mul' X Y := by
    ext i j
    rcases i with ⟨i, k⟩
    rcases j with ⟨j, l⟩
    change (∑ s : Fin p, X i s * Y s j) k l =
      ∑ s : Fin p × Fin q, X i s.1 k s.2 * Y s.1 j s.2 l
    rw [sum_cstarMatrix_apply]
    simp only [CStarMatrix.mul_apply, Fintype.sum_prod_type]

@[simp] theorem blockMatrixProductEquiv_apply (p q : ℕ)
    (X : CStarMatrix (Fin p) (Fin p) (CStarMatrix (Fin q) (Fin q) A))
    (i j : Fin p) (k l : Fin q) :
    blockMatrixProductEquiv (A := A) p q X (i, k) (j, l) = X i j k l := rfl

/-- Flatten square blocks using the standard product enumeration. -/
def blockMatrixFlatten (p q : ℕ) :
    CStarMatrix (Fin p) (Fin p) (CStarMatrix (Fin q) (Fin q) A) ≃⋆ₐ[ℂ]
      CStarMatrix (Fin (p * q)) (Fin (p * q)) A :=
  (blockMatrixProductEquiv p q).trans (CStarMatrix.reindexₐ ℂ A finProdFinEquiv)

@[simp] theorem blockMatrixFlatten_apply (p q : ℕ)
    (X : CStarMatrix (Fin p) (Fin p) (CStarMatrix (Fin q) (Fin q) A))
    (i j : Fin p) (k l : Fin q) :
    blockMatrixFlatten (A := A) p q X (finProdFinEquiv (i, k))
      (finProdFinEquiv (j, l)) = X i j k l := by
  change blockMatrixProductEquiv p q X
    ((finProdFinEquiv : Fin p × Fin q ≃ Fin (p * q)).symm (finProdFinEquiv (i, k)))
    ((finProdFinEquiv : Fin p × Fin q ≃ Fin (p * q)).symm (finProdFinEquiv (j, l))) = _
  simp only [Equiv.symm_apply_apply, blockMatrixProductEquiv_apply]

variable [PartialOrder A] [StarOrderedRing A]

@[simp] theorem norm_blockMatrixFlatten (p q : ℕ)
    (X : CStarMatrix (Fin p) (Fin p) (CStarMatrix (Fin q) (Fin q) A)) :
    ‖blockMatrixFlatten p q X‖ = ‖X‖ :=
  NonUnitalStarAlgHom.norm_map (blockMatrixFlatten (A := A) p q).toNonUnitalStarAlgHom
    (blockMatrixFlatten p q).injective X

end MatrixFlattening

section EntrywiseEquivalence

variable {B C : Type*} [Semiring B] [Semiring C] [StarRing B] [StarRing C]
  [SMul ℂ B] [SMul ℂ C]

/-- An equivalence of coefficient algebras induces the entrywise matrix equivalence. -/
def entrywiseCStarMatrixEquiv (n : ℕ) (e : B ≃⋆ₐ[ℂ] C) :
    CStarMatrix (Fin n) (Fin n) B ≃⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) C where
  toFun X := X.map e
  invFun X := X.map e.symm
  left_inv X := by ext i j; simp
  right_inv X := by ext i j; simp
  map_add' X Y := by ext i j; simp
  map_smul' c X := by ext i j; simp
  map_star' X := by
    ext i j
    change e (star (X j i)) = star (e (X j i))
    exact map_star e _
  map_mul' X Y := by
    ext i j
    change e (∑ k : Fin n, X i k * Y k j) = ∑ k : Fin n, e (X i k) * e (Y k j)
    simp only [map_sum, map_mul]

@[simp] theorem entrywiseCStarMatrixEquiv_apply (n : ℕ) (e : B ≃⋆ₐ[ℂ] C)
    (X : CStarMatrix (Fin n) (Fin n) B) (i j : Fin n) :
    entrywiseCStarMatrixEquiv n e X i j = e (X i j) := rfl

end EntrywiseEquivalence

section TripleMatrices

variable {A : Type*} [CStarAlgebra A]

/-- Flatten three matrix indices, retaining the outer-to-inner order. -/
def tripleMatrixFlatten (p q t : ℕ) :
    CStarMatrix (Fin p) (Fin p)
      (CStarMatrix (Fin q) (Fin q) (CStarMatrix (Fin t) (Fin t) A)) ≃⋆ₐ[ℂ]
    CStarMatrix (Fin (p * (q * t))) (Fin (p * (q * t))) A :=
  (entrywiseCStarMatrixEquiv p (blockMatrixFlatten q t)).trans
    (blockMatrixFlatten p (q * t))

@[simp] theorem tripleMatrixFlatten_apply (p q t : ℕ)
    (X : CStarMatrix (Fin p) (Fin p)
      (CStarMatrix (Fin q) (Fin q) (CStarMatrix (Fin t) (Fin t) A)))
    (i j : Fin p) (k l : Fin q) (a b : Fin t) :
    tripleMatrixFlatten p q t X
      (finProdFinEquiv (i, finProdFinEquiv (k, a)))
      (finProdFinEquiv (j, finProdFinEquiv (l, b))) = X i j k l a b := by
  simp [tripleMatrixFlatten]

/-- The four-by-four dilation's flattened matrix has size `4 * n`. -/
def fourfoldMatrixFlatten (n : ℕ) :
    CStarMatrix (Fin 2) (Fin 2)
      (CStarMatrix (Fin 2) (Fin 2) (CStarMatrix (Fin n) (Fin n) A)) ≃⋆ₐ[ℂ]
    CStarMatrix (Fin (4 * n)) (Fin (4 * n)) A :=
  (tripleMatrixFlatten 2 2 n).trans
    (CStarMatrix.reindexₐ ℂ A (finCongr (by omega : 2 * (2 * n) = 4 * n)))

/-- The common enumeration of the three finite indices. -/
def fourfoldIndexEquiv (n : ℕ) : (Fin 2 × (Fin 2 × Fin n)) ≃ Fin (4 * n) :=
  ((Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans finProdFinEquiv).trans
    (finCongr (by omega : 2 * (2 * n) = 4 * n))

private theorem sum_fourfold {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : Fin (4 * n) → M) :
    ∑ a : Fin (4 * n), f a =
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin n, f (fourfoldIndexEquiv n (i, (j, k))) := by
  simpa only [Fintype.sum_prod_type] using
    (Fintype.sum_equiv (fourfoldIndexEquiv n)
      (fun ijk => f (fourfoldIndexEquiv n ijk)) f (fun _ => rfl)).symm

@[simp] theorem fourfoldMatrixFlatten_apply (n : ℕ)
    (X : CStarMatrix (Fin 2) (Fin 2)
      (CStarMatrix (Fin 2) (Fin 2) (CStarMatrix (Fin n) (Fin n) A)))
    (i j k l : Fin 2) (a b : Fin n) :
    fourfoldMatrixFlatten n X (fourfoldIndexEquiv n (i, (k, a)))
      (fourfoldIndexEquiv n (j, (l, b))) = X i j k l a b := by
  change tripleMatrixFlatten 2 2 n X
    ((finCongr (by omega : 2 * (2 * n) = 4 * n)).symm
      (finCongr (by omega : 2 * (2 * n) = 4 * n)
        (finProdFinEquiv (i, finProdFinEquiv (k, a)))))
    ((finCongr (by omega : 2 * (2 * n) = 4 * n)).symm
      (finCongr (by omega : 2 * (2 * n) = 4 * n)
        (finProdFinEquiv (j, finProdFinEquiv (l, b))))) = _
  simp only [Equiv.symm_apply_apply, tripleMatrixFlatten_apply]

end TripleMatrices

section MatrixTrace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Normalized diagonal traces agree under block flattening. -/
theorem normalizedMatrixTrace_blockMatrixFlatten (p q : ℕ) [NeZero p] [NeZero q]
    (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin p) (Fin p) (CStarMatrix (Fin q) (Fin q) A)) :
    normalizedMatrixTrace (normalizedMatrixTrace τ q) p X =
      normalizedMatrixTrace τ (p * q) (blockMatrixFlatten p q X) := by
  simp only [normalizedMatrixTrace_apply, Nat.cast_mul]
  rw [sum_fin_prod]
  simp only [blockMatrixFlatten_apply]
  let a : Fin p → ℂ := fun i => ∑ j : Fin q, τ (X i i j j)
  change (∑ i : Fin p, a i / (q : ℂ)) / (p : ℂ) =
    (∑ i : Fin p, a i) / ((p : ℂ) * (q : ℂ))
  rw [← Finset.sum_div, div_div, mul_comm (q : ℂ) (p : ℂ)]

theorem normalizedMatrixTrace_tripleMatrixFlatten (p q t : ℕ)
    [NeZero p] [NeZero q] [NeZero t] (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin p) (Fin p)
      (CStarMatrix (Fin q) (Fin q) (CStarMatrix (Fin t) (Fin t) A))) :
    normalizedMatrixTrace (normalizedMatrixTrace (normalizedMatrixTrace τ t) q) p X =
      normalizedMatrixTrace τ (p * (q * t)) (tripleMatrixFlatten p q t X) := by
  calc
    _ = normalizedMatrixTrace (normalizedMatrixTrace τ (q * t)) p
        (entrywiseCStarMatrixEquiv p (blockMatrixFlatten q t) X) := by
      simp only [normalizedMatrixTrace_apply, entrywiseCStarMatrixEquiv_apply]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact normalizedMatrixTrace_blockMatrixFlatten q t τ (X i i)
    _ = _ := normalizedMatrixTrace_blockMatrixFlatten p (q * t) τ _

theorem normalizedMatrixTrace_reindex {r m : ℕ} [NeZero r] [NeZero m]
    (τ : A →ₚ[ℂ] ℂ) (e : Fin r ≃ Fin m)
    (X : CStarMatrix (Fin r) (Fin r) A) :
    normalizedMatrixTrace τ m (CStarMatrix.reindexₐ ℂ A e X) =
      normalizedMatrixTrace τ r X := by
  have hcard : r = m := by simpa using Fintype.card_congr e
  simp only [normalizedMatrixTrace_apply]
  congr 1
  · exact (Fintype.sum_equiv e (fun i => τ (X i i))
      (fun j => τ ((CStarMatrix.reindexₐ ℂ A e X) j j)) (by
        intro i
        change τ (X i i) = τ (X (e.symm (e i)) (e.symm (e i)))
        rw [Equiv.symm_apply_apply])).symm
  · exact_mod_cast hcard.symm

/-- The normalized trace is unchanged by the complete fourfold flattening. -/
theorem normalizedMatrixTrace_fourfoldMatrixFlatten (n : ℕ) [NeZero n]
    (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin 2) (Fin 2)
      (CStarMatrix (Fin 2) (Fin 2) (CStarMatrix (Fin n) (Fin n) A))) :
    normalizedMatrixTrace τ (4 * n) (fourfoldMatrixFlatten n X) =
      normalizedMatrixTrace (normalizedMatrixTrace (normalizedMatrixTrace τ n) 2) 2 X := by
  rw [fourfoldMatrixFlatten, StarAlgEquiv.trans_apply, normalizedMatrixTrace_reindex]
  exact (normalizedMatrixTrace_tripleMatrixFlatten 2 2 n τ X).symm

theorem normalizedMatrixTrace_two_eq_linearMatrixTrace (τ : A →ₚ[ℂ] ℂ)
    (X : HochschildMatrixDilation.Mat A) :
    normalizedMatrixTrace τ 2 X = linearMatrixTrace τ.toLinearMap X := by
  simp only [normalizedMatrixTrace_apply, linearMatrixTrace_apply, Fin.sum_univ_two,
    Nat.cast_ofNat]
  rfl

/-- The actual flattened four-by-four contraction symmetry is centered for
the normalized trace on the ordinary matrix algebra. -/
theorem normalizedMatrixTrace_flattened_contractionSymmetry (n : ℕ) [NeZero n]
    (τ : A →ₚ[ℂ] ℂ) (X : CStarMatrix (Fin n) (Fin n) A) (hX : ‖X‖ ≤ 1) :
    normalizedMatrixTrace τ (4 * n)
      (fourfoldMatrixFlatten n (contractionSymmetryUnitary X hX)) = 0 := by
  rw [normalizedMatrixTrace_fourfoldMatrixFlatten, normalizedMatrixTrace_two_eq_linearMatrixTrace]
  have htwo : (normalizedMatrixTrace (normalizedMatrixTrace τ n) 2).toLinearMap =
      linearMatrixTrace (normalizedMatrixTrace τ n).toLinearMap := by
    ext Y
    exact normalizedMatrixTrace_two_eq_linearMatrixTrace _ Y
  rw [htwo]
  exact linearMatrixTrace_contractionSymmetryUnitary _ X hX

end MatrixTrace

section HilbertFlattening

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Flatten two finite Hilbert sums in the same order as block matrices. -/
def hilbertArrayFlatten (p q : ℕ) :
    HilbertCopies (HilbertCopies H q) p ≃ₗᵢ[ℂ] HilbertCopies H (p * q) :=
  (LinearIsometryEquiv.piLpCurry ℂ 2 (fun (_ : Fin p) (_ : Fin q) => H)).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ H
      ((Equiv.sigmaEquivProd (Fin p) (Fin q)).trans finProdFinEquiv))

@[simp] theorem hilbertArrayFlatten_apply (p q : ℕ)
    (x : HilbertCopies (HilbertCopies H q) p) (i : Fin p) (j : Fin q) :
    hilbertArrayFlatten p q x (finProdFinEquiv (i, j)) = x i j := by
  change x ((finProdFinEquiv : Fin p × Fin q ≃ Fin (p * q)).symm
      (finProdFinEquiv (i, j))).1
    ((finProdFinEquiv : Fin p × Fin q ≃ Fin (p * q)).symm
      (finProdFinEquiv (i, j))).2 = x i j
  rw [Equiv.symm_apply_apply]

/-- Repeated diagonal amplification is unchanged by flattening. -/
theorem hilbertArrayFlatten_amplify (p q : ℕ) (Y : H →L[ℂ] H)
    (x : HilbertCopies (HilbertCopies H q) p) :
    hilbertArrayFlatten p q (amplify (amplify Y q) p x) =
      amplify Y (p * q) (hilbertArrayFlatten p q x) := by
  ext k
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp

/-- Three nested finite Hilbert sums, in the same order as triple block matrices. -/
def hilbertTripleFlatten (p q t : ℕ) :
    HilbertCopies (HilbertCopies (HilbertCopies H t) q) p ≃ₗᵢ[ℂ]
      HilbertCopies H (p * (q * t)) :=
  (LinearIsometryEquiv.piLpCongrRight 2
    (fun _ : Fin p => hilbertArrayFlatten (H := H) q t)).trans
    (hilbertArrayFlatten (H := H) p (q * t))

@[simp] theorem hilbertTripleFlatten_apply (p q t : ℕ)
    (x : HilbertCopies (HilbertCopies (HilbertCopies H t) q) p)
    (i : Fin p) (j : Fin q) (a : Fin t) :
    hilbertTripleFlatten p q t x
      (finProdFinEquiv (i, finProdFinEquiv (j, a))) = x i j a := by
  simp [hilbertTripleFlatten]

/-- The Hilbert-space change of coordinates for the four-by-four dilation. -/
def hilbertFourfoldFlatten (n : ℕ) :
    HilbertCopies (HilbertCopies (HilbertCopies H n) 2) 2 ≃ₗᵢ[ℂ]
      HilbertCopies H (4 * n) :=
  (hilbertTripleFlatten 2 2 n).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ H
      (finCongr (by omega : 2 * (2 * n) = 4 * n)))

@[simp] theorem hilbertFourfoldFlatten_apply (n : ℕ)
    (x : HilbertCopies (HilbertCopies (HilbertCopies H n) 2) 2)
    (i j : Fin 2) (a : Fin n) :
    hilbertFourfoldFlatten n x (fourfoldIndexEquiv n (i, (j, a))) = x i j a := by
  simp [hilbertFourfoldFlatten, fourfoldIndexEquiv,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

theorem hilbertFourfoldFlatten_amplify (n : ℕ) (Y : H →L[ℂ] H)
    (x : HilbertCopies (HilbertCopies (HilbertCopies H n) 2) 2) :
    hilbertFourfoldFlatten n (amplify (amplify (amplify Y n) 2) 2 x) =
      amplify Y (4 * n) (hilbertFourfoldFlatten n x) := by
  ext k
  obtain ⟨⟨i, j, a⟩, rfl⟩ := (fourfoldIndexEquiv n).surjective k
  simp

end HilbertFlattening

section RepresentedFlattening

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Nested block multiplication and flattened matrix multiplication act
identically in the corresponding Hilbert coordinates. -/
theorem hilbertArrayFlatten_represented (p q : ℕ)
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (X : CStarMatrix (Fin p) (Fin p) (CStarMatrix (Fin q) (Fin q) A))
    (x : HilbertCopies (HilbertCopies H q) p) :
    hilbertArrayFlatten p q
      (matrixOperator (fun i j => representedMatrix σ (X i j)) x) =
    representedMatrix σ (blockMatrixFlatten p q X) (hilbertArrayFlatten p q x) := by
  ext k
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  rw [hilbertArrayFlatten_apply]
  let Z : Matrix (Fin p) (Fin p) (Matrix (Fin q) (Fin q) (H →L[ℂ] H)) :=
    fun a b c d => σ (X a b c d)
  let W : Matrix (Fin (p * q)) (Fin (p * q)) (H →L[ℂ] H) :=
    fun a b => σ (blockMatrixFlatten p q X a b)
  change (matrixOperator (fun a b => matrixOperator (Z a b)) x i) j =
    matrixOperator W (hilbertArrayFlatten p q x) (finProdFinEquiv (i, j))
  rw [matrixOperator_apply (fun a b => matrixOperator (Z a b)) x i,
    matrixOperator_apply W (hilbertArrayFlatten p q x) (finProdFinEquiv (i, j))]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, matrixOperator_apply]
  rw [sum_fin_prod p q]
  have hW (a b : Fin p) (c d : Fin q) :
      W (finProdFinEquiv (a, c)) (finProdFinEquiv (b, d)) = Z a b c d := by
    dsimp only [W, Z]
    rw [blockMatrixFlatten_apply]
  simp only [hW, hilbertArrayFlatten_apply]

variable [PartialOrder A] [StarOrderedRing A]

private theorem representedDoubleMatrix_nested_apply (n : ℕ)
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (X : HochschildMatrixDilation.Mat
      (HochschildMatrixDilation.Mat (CStarMatrix (Fin n) (Fin n) A)))
    (x : HilbertCopies (HilbertCopies (HilbertCopies H n) 2) 2)
    (i k : Fin 2) (a : Fin n) :
    representedDoubleMatrix (representedMatrixHom σ n) X x i k a =
      ∑ j : Fin 2, ∑ l : Fin 2, ∑ b : Fin n, σ (X i j k l a b) (x j l b) := by
  rw [representedDoubleMatrix_apply (representedMatrixHom σ n) X x i k]
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  exact matrixOperator_apply (fun c d => σ (X i j k l c d)) (x j l) a

/-- The nested action used by the dilation is precisely the ordinary
flattened matrix action under the explicit Hilbert-array isometry. -/
theorem hilbertFourfoldFlatten_representedDoubleMatrix (n : ℕ)
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (X : HochschildMatrixDilation.Mat
      (HochschildMatrixDilation.Mat (CStarMatrix (Fin n) (Fin n) A)))
    (x : HilbertCopies (HilbertCopies (HilbertCopies H n) 2) 2) :
    hilbertFourfoldFlatten n (representedDoubleMatrix (representedMatrixHom σ n) X x) =
      representedMatrix σ (fourfoldMatrixFlatten n X) (hilbertFourfoldFlatten n x) := by
  ext a
  obtain ⟨⟨i, k, b⟩, rfl⟩ := (fourfoldIndexEquiv n).surjective a
  rw [hilbertFourfoldFlatten_apply, representedDoubleMatrix_nested_apply]
  let W : Matrix (Fin (4 * n)) (Fin (4 * n)) (H →L[ℂ] H) :=
    fun c d => σ (fourfoldMatrixFlatten n X c d)
  change _ = matrixOperator W (hilbertFourfoldFlatten n x) (fourfoldIndexEquiv n (i, (k, b)))
  rw [matrixOperator_apply W (hilbertFourfoldFlatten n x) (fourfoldIndexEquiv n (i, (k, b))),
    sum_fourfold n]
  have hW (j l : Fin 2) (c : Fin n) :
      W (fourfoldIndexEquiv n (i, (k, b))) (fourfoldIndexEquiv n (j, (l, c))) =
        σ (X i j k l b c) := by
    dsimp only [W]
    rw [fourfoldMatrixFlatten_apply]
  simp only [hW, hilbertFourfoldFlatten_apply]

theorem hilbertFourfoldFlatten_commutator (n : ℕ)
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Y : H →L[ℂ] H)
    (X : HochschildMatrixDilation.Mat
      (HochschildMatrixDilation.Mat (CStarMatrix (Fin n) (Fin n) A)))
    (x : HilbertCopies (HilbertCopies (HilbertCopies H n) 2) 2) :
    hilbertFourfoldFlatten n
      (commutator (amplify (amplify (amplify Y n) 2) 2)
        (representedDoubleMatrix (representedMatrixHom σ n) X) x) =
      commutator (amplify Y (4 * n)) (representedMatrix σ (fourfoldMatrixFlatten n X))
        (hilbertFourfoldFlatten n x) := by
  simp only [commutator, sub_apply, mul_apply_eq_comp, map_sub,
    hilbertFourfoldFlatten_amplify, hilbertFourfoldFlatten_representedDoubleMatrix]

/-- The commutator norm is exactly preserved by the change of array coordinates. -/
theorem norm_fourfold_commutator (n : ℕ)
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Y : H →L[ℂ] H)
    (X : HochschildMatrixDilation.Mat
      (HochschildMatrixDilation.Mat (CStarMatrix (Fin n) (Fin n) A))) :
    ‖commutator (amplify Y (4 * n)) (representedMatrix σ (fourfoldMatrixFlatten n X))‖ =
      ‖commutator (amplify (amplify (amplify Y n) 2) 2)
        (representedDoubleMatrix (representedMatrixHom σ n) X)‖ := by
  let U := hilbertFourfoldFlatten (H := H) n
  let T := commutator (amplify (amplify (amplify Y n) 2) 2)
    (representedDoubleMatrix (representedMatrixHom σ n) X)
  have he : U.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (T.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap) =
      commutator (amplify Y (4 * n)) (representedMatrix σ (fourfoldMatrixFlatten n X)) := by
    apply ContinuousLinearMap.ext
    intro x
    change U (T (U.symm x)) = _
    rw [hilbertFourfoldFlatten_commutator, LinearIsometryEquiv.apply_symm_apply]
  calc
    _ = ‖U.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (T.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap)‖ :=
      congrArg norm he.symm
    _ = ‖T.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap‖ :=
      norm_isometricCoordinates_comp _ U
    _ = ‖T‖ := norm_comp_isometricCoordinates T U.symm

/-- The original matrix test is a norm-decreasing corner of the ordinary
`4 * n` centered symmetry test. -/
theorem norm_amplified_commutator_le_flattened_symmetry {n : ℕ} [NeZero n]
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Y : H →L[ℂ] H)
    (X : CStarMatrix (Fin n) (Fin n) A) (hX : ‖X‖ ≤ 1) :
    ‖commutator (amplify Y n) (representedMatrix σ X)‖ ≤
      ‖commutator (amplify Y (4 * n))
        (representedMatrix σ (fourfoldMatrixFlatten n (contractionSymmetryUnitary X hX)))‖ := by
  calc
    _ ≤ ‖commutator (amplify (amplify (amplify Y n) 2) 2)
        (representedDoubleMatrix (representedMatrixHom σ n)
          (contractionSymmetryUnitary X hX))‖ :=
      norm_amplified_commutator_le_centered_symmetry σ Y X hX
    _ = _ := (norm_fourfold_commutator n σ Y (contractionSymmetryUnitary X hX)).symm

end RepresentedFlattening

end KadisonSimilarity

end

end OAI
