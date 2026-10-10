import OAI.Analysis.KadisonSimilarity.Similarity.CompletelyBounded
import OAI.Analysis.KadisonSimilarity.Derivation.Derivations

namespace OAI

/-! # Rectangular derivations and the row/column estimate -/

noncomputable section
namespace KadisonSimilarity

variable {A F K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Finite rectangular operator matrices act between the two Hilbert sums. -/
def rectangularMatrixOperator {p q : ℕ}
    (X : Matrix (Fin p) (Fin q) (K →L[ℂ] F)) :
    HilbertCopies K q →L[ℂ] HilbertCopies F p :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin p => F)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      ∑ j : Fin q, (X i j).comp (PiLp.proj 2 (fun _ : Fin q => K) j))

@[simp] theorem rectangularMatrixOperator_apply {p q : ℕ}
    (X : Matrix (Fin p) (Fin q) (K →L[ℂ] F))
    (ξ : HilbertCopies K q) (i : Fin p) :
    rectangularMatrixOperator X ξ i = ∑ j : Fin q, X i j (ξ j) := by
  simp [rectangularMatrixOperator]

@[simp] theorem rectangularMatrixOperator_zero {p q : ℕ} :
    rectangularMatrixOperator (0 : Matrix (Fin p) (Fin q) (K →L[ℂ] F)) = 0 := by
  ext ξ i
  simp

theorem rectangularMatrixOperator_smul {p q : ℕ} (c : ℂ)
    (X : Matrix (Fin p) (Fin q) (K →L[ℂ] F)) :
    rectangularMatrixOperator (c • X) = c • rectangularMatrixOperator X := by
  ext ξ i
  simp [rectangularMatrixOperator, Finset.smul_sum]

/-- Coordinatewise amplification of a bounded operator between different spaces. -/
def mapCopies (T : K →L[ℂ] F) (n : ℕ) : HilbertCopies K n →L[ℂ] HilbertCopies F n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => F)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => T.comp (PiLp.proj 2 (fun _ : Fin n => K) i))

@[simp] theorem mapCopies_apply (T : K →L[ℂ] F) (n : ℕ)
    (ξ : HilbertCopies K n) (i : Fin n) : mapCopies T n ξ i = T (ξ i) := by
  simp [mapCopies]

theorem norm_mapCopies_le (T : K →L[ℂ] F) (n : ℕ) : ‖mapCopies T n‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro ξ
  have hs : ‖mapCopies T n ξ‖ ^ 2 ≤ (‖T‖ * ‖ξ‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      ∑ i : Fin n, ‖mapCopies T n ξ i‖ ^ 2 ≤
          ∑ i : Fin n, (‖T‖ * ‖ξ i‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [mapCopies_apply]
        exact pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm _) 2
      _ = ‖T‖ ^ 2 * (∑ i : Fin n, ‖ξ i‖ ^ 2) := by
        simp_rw [mul_pow]
        rw [Finset.mul_sum]
      _ = (‖T‖ * ‖ξ‖) ^ 2 := by rw [← PiLp.norm_sq_eq_of_L2]; ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg T) (norm_nonneg ξ))).mp hs

/-- The Hilbert direct sum used in the rectangular triangular representation. -/
abbrev RectangularSum (F K : Type*) := WithLp 2 (F × K)

def rectangularInl : F →L[ℂ] RectangularSum F K :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ F K).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ F K)

def rectangularInr : K →L[ℂ] RectangularSum F K :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ F K).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℂ F K)

@[simp] theorem rectangularInl_apply (x : F) :
    (rectangularInl (K := K) x).fst = x ∧ (rectangularInl (K := K) x).snd = 0 := by
  simp [rectangularInl]

@[simp] theorem rectangularInr_apply (x : K) :
    (rectangularInr (F := F) x).fst = 0 ∧ (rectangularInr (F := F) x).snd = x := by
  simp [rectangularInr]

theorem norm_rectangularInr_le_one : ‖rectangularInr (F := F) (K := K)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖WithLp.toLp 2 (0, x)‖ ≤ 1 * ‖x‖
  simp [WithLp.norm_toLp_snd]

theorem norm_rectangularFst_le_one : ‖WithLp.fstL 2 ℂ F K‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using WithLp.norm_fst_le F x

/-- Matrix amplification respects compression to the upper-right corner. -/
theorem rectangularMatrixOperator_corner {p q : ℕ}
    (X : Matrix (Fin p) (Fin q)
      (RectangularSum F K →L[ℂ] RectangularSum F K)) :
    rectangularMatrixOperator (fun i j => (WithLp.fstL 2 ℂ F K).comp
      ((X i j).comp rectangularInr)) =
      (mapCopies (WithLp.fstL 2 ℂ F K) p).comp
        ((rectangularMatrixOperator X).comp (mapCopies rectangularInr q)) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply PiLp.ext
  intro i
  calc
    _ = ∑ j : Fin q, ((WithLp.fstL 2 ℂ F K).comp
        ((X i j).comp rectangularInr)) (ξ j) :=
      rectangularMatrixOperator_apply (F := F) (K := K) _ ξ i
    _ = (WithLp.fstL 2 ℂ F K)
        (∑ j : Fin q, X i j (rectangularInr (ξ j))) := by
      simp only [ContinuousLinearMap.comp_apply, map_sum]
    _ = _ := by
      change _ = (mapCopies (WithLp.fstL 2 ℂ F K) p
        (rectangularMatrixOperator X (mapCopies rectangularInr q ξ))) i
      rw [mapCopies_apply, rectangularMatrixOperator_apply]
      congr 1

private theorem norm_compression_le
    {E₁ E₂ E₃ E₄ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    [NormedAddCommGroup E₃] [NormedSpace ℂ E₃]
    [NormedAddCommGroup E₄] [NormedSpace ℂ E₄]
    (L : E₃ →L[ℂ] E₄) (T : E₂ →L[ℂ] E₃) (R : E₁ →L[ℂ] E₂)
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) : ‖L.comp (T.comp R)‖ ≤ ‖T‖ := by
  calc
    ‖L.comp (T.comp R)‖ ≤ ‖L‖ * (‖T‖ * ‖R‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖T‖ * ‖R‖) :=
      mul_le_mul_of_nonneg_right hL (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ 1 * (‖T‖ * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR (norm_nonneg _)) zero_le_one
    _ = ‖T‖ := by ring

/-- Compression to the upper-right corner of every entry does not increase
 the norm of a rectangular operator matrix. -/
theorem norm_rectangularCorner_le {p q : ℕ}
    (X : Matrix (Fin p) (Fin q)
      (RectangularSum F K →L[ℂ] RectangularSum F K)) :
    ‖rectangularMatrixOperator (fun i j => (WithLp.fstL 2 ℂ F K).comp
      ((X i j).comp rectangularInr))‖ ≤ ‖rectangularMatrixOperator X‖ := by
  have hleft : ‖mapCopies (WithLp.fstL 2 ℂ F K) p‖ ≤ 1 :=
    (norm_mapCopies_le _ _).trans (norm_rectangularFst_le_one (F := F) (K := K))
  have hright : ‖mapCopies (rectangularInr (F := F) (K := K)) q‖ ≤ 1 :=
    (norm_mapCopies_le _ _).trans (norm_rectangularInr_le_one (F := F) (K := K))
  calc
    _ = ‖(mapCopies (WithLp.fstL 2 ℂ F K) p).comp
        ((rectangularMatrixOperator X).comp (mapCopies rectangularInr q))‖ :=
      congrArg norm (rectangularMatrixOperator_corner X)
    _ ≤ ‖rectangularMatrixOperator X‖ :=
      norm_compression_le _ _ _ hleft hright

/-- The diagonal plus one upper-right block. -/
def rectangularTriangular (ρ : F →L[ℂ] F) (δ : K →L[ℂ] F) (σ : K →L[ℂ] K) :
    RectangularSum F K →L[ℂ] RectangularSum F K :=
  rectangularInl.comp (ρ.comp (WithLp.fstL 2 ℂ F K)) +
    rectangularInl.comp (δ.comp (WithLp.sndL 2 ℂ F K)) +
    rectangularInr.comp (σ.comp (WithLp.sndL 2 ℂ F K))

@[simp] theorem rectangularTriangular_fst (ρ : F →L[ℂ] F) (δ : K →L[ℂ] F)
    (σ : K →L[ℂ] K) (x : RectangularSum F K) :
    (rectangularTriangular ρ δ σ x).fst = ρ x.fst + δ x.snd := by
  simp [rectangularTriangular, rectangularInl, rectangularInr]

@[simp] theorem rectangularTriangular_snd (ρ : F →L[ℂ] F) (δ : K →L[ℂ] F)
    (σ : K →L[ℂ] K) (x : RectangularSum F K) :
    (rectangularTriangular ρ δ σ x).snd = σ x.snd := by
  simp [rectangularTriangular, rectangularInl, rectangularInr]

/-- Contractive diagonal blocks give a contractive diagonal operator. -/
theorem norm_rectangularDiagonal_le (ρ : F →L[ℂ] F) (σ : K →L[ℂ] K)
    {c : ℝ} (hc : 0 ≤ c) (hρ : ‖ρ‖ ≤ c) (hσ : ‖σ‖ ≤ c) :
    ‖rectangularTriangular ρ 0 σ‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg x))).mp
  simp only [WithLp.prod_norm_sq_eq_of_L2, rectangularTriangular_fst,
    rectangularTriangular_snd, zero_apply, add_zero]
  have h₁ := (ρ.le_opNorm x.fst).trans
    (mul_le_mul_of_nonneg_right hρ (norm_nonneg x.fst))
  have h₂ := (σ.le_opNorm x.snd).trans
    (mul_le_mul_of_nonneg_right hσ (norm_nonneg x.snd))
  have h₁' := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
  have h₂' := pow_le_pow_left₀ (norm_nonneg _) h₂ 2
  calc
    ‖ρ x.fst‖ ^ 2 + ‖σ x.snd‖ ^ 2 ≤
        (c * ‖x.fst‖) ^ 2 + (c * ‖x.snd‖) ^ 2 := add_le_add h₁' h₂'
    _ = c ^ 2 * (‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2) := by ring
    _ = (c * ‖x‖) ^ 2 := by rw [← WithLp.prod_norm_sq_eq_of_L2 x]; ring

/-- The off-diagonal corner has the same norm bound as its sole block. -/
theorem norm_rectangularOffDiagonal_le (δ : K →L[ℂ] F) :
    ‖rectangularTriangular 0 δ 0‖ ≤ ‖δ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg δ)
  intro x
  have heq : rectangularTriangular 0 δ 0 x = WithLp.toLp 2 (δ x.snd, 0) := by
    apply (WithLp.equiv 2 (F × K)).injective
    apply Prod.ext <;> simp
  rw [heq, WithLp.norm_toLp_fst]
  exact (δ.le_opNorm x.snd).trans
    (mul_le_mul_of_nonneg_left (WithLp.norm_snd_le F x) (norm_nonneg δ))

/-- The pointwise triangular estimate used before applying Dickson. -/
theorem norm_rectangularTriangular_le (ρ : F →L[ℂ] F) (δ : K →L[ℂ] F)
    (σ : K →L[ℂ] K) {c : ℝ} (hc : 0 ≤ c) (hρ : ‖ρ‖ ≤ c) (hσ : ‖σ‖ ≤ c) :
    ‖rectangularTriangular ρ δ σ‖ ≤ c + ‖δ‖ := by
  have hsplit : rectangularTriangular ρ δ σ =
      rectangularTriangular ρ 0 σ + rectangularTriangular 0 δ 0 := by
    ext x
    apply (WithLp.equiv 2 (F × K)).injective
    apply Prod.ext <;> simp
  rw [hsplit]
  exact (norm_add_le (rectangularTriangular ρ 0 σ) (rectangularTriangular 0 δ 0)).trans
    (add_le_add (norm_rectangularDiagonal_le ρ σ hc hρ hσ)
      (norm_rectangularOffDiagonal_le δ))

variable [CompleteSpace F] [CompleteSpace K]

open scoped CStarAlgebra

/-- A rectangular derivation vanishes at the identity. -/
theorem rectangularDerivation_map_one (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b)) : δ 1 = 0 := by
  have h := hδ 1 1
  simp only [one_mul, map_one, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_id] at h
  have h' : δ 1 + 0 = δ 1 + δ 1 := by simpa using h
  exact (add_left_cancel h').symm

/-- The bounded unital triangular homomorphism of a rectangular derivation. -/
def rectangularRepresentation (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b)) :
    BoundedUnitalHom A (RectangularSum F K) := by
  let f : A →ₗ[ℂ] (RectangularSum F K →L[ℂ] RectangularSum F K) :=
    { toFun := fun a => rectangularTriangular (ρ a) (δ a) (σ a)
      map_add' := by
        intro a b
        ext x
        apply (WithLp.equiv 2 (F × K)).injective
        apply Prod.ext
        · simp; abel
        · simp
      map_smul' := by
        intro c a
        ext x
        apply (WithLp.equiv 2 (F × K)).injective
        apply Prod.ext <;> simp [smul_add] }
  have hone : f 1 = 1 := by
    ext x
    apply (WithLp.equiv 2 (F × K)).injective
    apply Prod.ext <;> simp [f, rectangularDerivation_map_one ρ σ δ hδ]
  have hmul : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    ext x
    apply (WithLp.equiv 2 (F × K)).injective
    apply Prod.ext
    · simp [f, hδ, mul_apply_eq_comp, map_add]; abel
    · simp [f, mul_apply_eq_comp]
  refine ⟨AlgHom.ofLinearMap f hone hmul, ?_⟩
  change Continuous (fun a => rectangularTriangular (ρ a) (δ a) (σ a))
  unfold rectangularTriangular
  exact ((((map_continuous ρ).clm_comp_const _).const_clm_comp _).add
    ((δ.continuous.clm_comp_const _).const_clm_comp _)).add
    (((map_continuous σ).clm_comp_const _).const_clm_comp _)

/-- The norm estimate which gives norm at most two after normalization. -/
theorem norm_rectangularRepresentation_apply (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b)) (a : A) :
    ‖(rectangularRepresentation ρ σ δ hδ).1 a‖ ≤ (1 + ‖δ‖) * ‖a‖ := by
  change ‖rectangularTriangular (ρ a) (δ a) (σ a)‖ ≤ (1 + ‖δ‖) * ‖a‖
  calc
    ‖rectangularTriangular (ρ a) (δ a) (σ a)‖ ≤ ‖a‖ + ‖δ a‖ :=
      norm_rectangularTriangular_le _ _ _ (norm_nonneg _)
        (NonUnitalStarAlgHom.norm_apply_le ρ a) (NonUnitalStarAlgHom.norm_apply_le σ a)
    _ ≤ ‖a‖ + ‖δ‖ * ‖a‖ := add_le_add (le_refl _) (δ.le_opNorm a)
    _ = (1 + ‖δ‖) * ‖a‖ := by ring

/-- Rescaling the derivation before forming the triangular representation. -/
def normalizedRectangularDerivation (δ : A →L[ℂ] (K →L[ℂ] F)) :
    A →L[ℂ] (K →L[ℂ] F) := ((‖δ‖⁻¹ : ℝ) : ℂ) • δ

omit [CompleteSpace F] [CompleteSpace K] in
theorem norm_normalizedRectangularDerivation_le (δ : A →L[ℂ] (K →L[ℂ] F)) :
    ‖normalizedRectangularDerivation δ‖ ≤ 1 := by
  let : SeminormedAddCommGroup (A →L[ℂ] (K →L[ℂ] F)) := inferInstance
  let : NormedSpace ℂ (A →L[ℂ] (K →L[ℂ] F)) := inferInstance
  by_cases h : δ = 0
  · simp [h, normalizedRectangularDerivation]
  · have hn : ‖δ‖ ≠ 0 := (norm_ne_zero_iff (E := A →L[ℂ] (K →L[ℂ] F))).mpr h
    simp [normalizedRectangularDerivation, norm_smul, hn]

theorem normalizedRectangularDerivation_leibniz (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b)) (a b : A) :
    normalizedRectangularDerivation δ (a * b) =
      (ρ a).comp (normalizedRectangularDerivation δ b) +
        (normalizedRectangularDerivation δ a).comp (σ b) := by
  ext x
  simp [normalizedRectangularDerivation, hδ, smul_add]

def normalizedRectangularRepresentation (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b)) :
    BoundedUnitalHom A (RectangularSum F K) :=
  rectangularRepresentation ρ σ (normalizedRectangularDerivation δ)
    (normalizedRectangularDerivation_leibniz ρ σ δ hδ)

/-- The normalized triangular representation meets Dickson's norm-two hypothesis. -/
theorem norm_normalizedRectangularRepresentation_le_two
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b)) (a : A) :
    ‖(rectangularRepresentation ρ σ (normalizedRectangularDerivation δ)
      (normalizedRectangularDerivation_leibniz ρ σ δ hδ)).1 a‖ ≤ 2 * ‖a‖ := by
  refine (norm_rectangularRepresentation_apply ρ σ _ _ a).trans ?_
  have h := norm_normalizedRectangularDerivation_le δ
  nlinarith [norm_nonneg a]

section RowColumn

variable [PartialOrder A] [StarOrderedRing A]

/-- Uniform row-amplification bound with the rectangular C-star matrix norm. -/
def RowBound (f : A → (K →L[ℂ] F)) (C : ℝ) : Prop :=
  ∀ n : ℕ, ∀ X : Matrix (Fin 1) (Fin n) A,
    ‖rectangularMatrixOperator (X.map f)‖ ≤ C * ‖CStarMatrix.ofMatrix X‖

/-- Uniform column-amplification bound with the rectangular C-star matrix norm. -/
def ColumnBound (f : A → (K →L[ℂ] F)) (C : ℝ) : Prop :=
  ∀ n : ℕ, ∀ X : Matrix (Fin n) (Fin 1) A,
    ‖rectangularMatrixOperator (X.map f)‖ ≤ C * ‖CStarMatrix.ofMatrix X‖

/-- The norm-two specialization of Dickson (2014), Lemma 2.9, Eq. (19),
including its column form obtained by taking adjoints. -/
def DicksonTwoBound (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  ∀ π : BoundedUnitalHom A H, (∀ a, ‖π.1 a‖ ≤ 2 * ‖a‖) →
    RowBound π.1 (4 * Real.sqrt 2) ∧ ColumnBound π.1 (4 * Real.sqrt 2)

/-- The upper-right corner transfers any matrix estimate for the normalized
triangular representation to the original derivation. -/
theorem rectangularDerivation_matrix_bound_of_triangular
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    {p q : ℕ} (X : Matrix (Fin p) (Fin q) A) {C : ℝ}
    (htri : ‖rectangularMatrixOperator
      (X.map (normalizedRectangularRepresentation ρ σ δ hδ).1)‖ ≤
        C * ‖CStarMatrix.ofMatrix X‖) :
    ‖rectangularMatrixOperator (X.map δ)‖ ≤ (C * ‖δ‖) * ‖CStarMatrix.ofMatrix X‖ := by
  let : SeminormedAddCommGroup (HilbertCopies K q →L[ℂ] HilbertCopies F p) := inferInstance
  let : NormedSpace ℂ (HilbertCopies K q →L[ℂ] HilbertCopies F p) := inferInstance
  by_cases hz : δ = 0
  · have hzero : X.map δ = 0 := by
      apply Matrix.ext
      intro i j
      simp [hz]
    rw [hzero, rectangularMatrixOperator_zero]
    simp [hz, ContinuousLinearMap.opNorm_zero]
  let δ₀ := normalizedRectangularDerivation δ
  let Φ := normalizedRectangularRepresentation ρ σ δ hδ
  have hupper (a : A) : (WithLp.fstL 2 ℂ F K).comp
      ((Φ.1 a).comp rectangularInr) = δ₀ a := by
    ext x
    simp [Φ, normalizedRectangularRepresentation, rectangularRepresentation,
      rectangularTriangular, rectangularInl, rectangularInr, δ₀]
  have hcompress : ‖rectangularMatrixOperator (X.map δ₀)‖ ≤
      ‖rectangularMatrixOperator (X.map Φ.1)‖ := by
    change ‖rectangularMatrixOperator (fun i j => δ₀ (X i j))‖ ≤
      ‖rectangularMatrixOperator (X.map Φ.1)‖
    simpa only [Matrix.map_apply, hupper] using norm_rectangularCorner_le (X.map Φ.1)
  have hn : ‖δ‖ ≠ 0 := (norm_ne_zero_iff (E := A →L[ℂ] (K →L[ℂ] F))).mpr hz
  have hc : (‖δ‖ : ℂ) * ((‖δ‖⁻¹ : ℝ) : ℂ) = 1 := by
    norm_cast
    exact mul_inv_cancel₀ hn
  have hδrecover (a : A) : δ a = (‖δ‖ : ℂ) • δ₀ a := by
    simp only [δ₀, normalizedRectangularDerivation, smul_apply, smul_smul, hc, one_smul]
  have hrecover : rectangularMatrixOperator (X.map δ) =
      (‖δ‖ : ℂ) • rectangularMatrixOperator (X.map δ₀) := by
    have hm : X.map δ = (‖δ‖ : ℂ) • X.map δ₀ := by
      apply Matrix.ext
      intro i j
      exact hδrecover (X i j)
    rw [hm, rectangularMatrixOperator_smul]
  rw [hrecover, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg δ)]
  calc
    ‖δ‖ * ‖rectangularMatrixOperator (X.map δ₀)‖ ≤
        ‖δ‖ * (C * ‖CStarMatrix.ofMatrix X‖) :=
      mul_le_mul_of_nonneg_left (hcompress.trans htri) (norm_nonneg δ)
    _ = (C * ‖δ‖) * ‖CStarMatrix.ofMatrix X‖ := by ring

/-- The manuscript's row/column derivation estimate, conditional only on the
norm-two specialization of the published Dickson estimate. -/
theorem rectangularDerivation_row_column
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    (dickson : DicksonTwoBound (A := A) (RectangularSum F K)) :
    RowBound δ ((4 * Real.sqrt 2) * ‖δ‖) ∧
      ColumnBound δ ((4 * Real.sqrt 2) * ‖δ‖) := by
  have hΦ := dickson (normalizedRectangularRepresentation ρ σ δ hδ)
    (norm_normalizedRectangularRepresentation_le_two ρ σ δ hδ)
  constructor
  · intro n X
    exact rectangularDerivation_matrix_bound_of_triangular ρ σ δ hδ X (hΦ.1 n X)
  · intro n X
    exact rectangularDerivation_matrix_bound_of_triangular ρ σ δ hδ X (hΦ.2 n X)

end RowColumn

end KadisonSimilarity

end

end OAI
