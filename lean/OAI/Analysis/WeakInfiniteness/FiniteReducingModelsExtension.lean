import Mathlib
import OAI.Analysis.WeakInfiniteness.PolynomialCompression

namespace OAI

noncomputable section

namespace WeakPureInfiniteness

section

section

open scoped TensorProduct ENNReal ComplexOrder

open UniformSpace

universe u v

section



attribute [instance] ComplexHilbert.normedAddCommGroup
  ComplexHilbert.innerProductSpace ComplexHilbert.completeSpace




attribute [instance] CuntzRepresentation.nontrivial

open scoped InnerProductSpace




attribute [instance] ContractionRepresentation.nontrivial


end

section


section UniformRepresentations

open scoped ENNReal

variable {ι : Type*} (B : ι → Type*) [∀ i, NonUnitalCStarAlgebra (B i)]

abbrev UniformCStarProduct := lp B ∞

instance : NonUnitalCStarAlgebra (UniformCStarProduct B) := by
  unfold UniformCStarProduct
  infer_instance

instance : CoeFun (UniformCStarProduct B) (fun _ => ∀ i, B i) := ⟨fun x => x.val⟩

variable {B} {A : Type*} [NonUnitalCStarAlgebra A]

noncomputable def uniformProductHom (ρ : ∀ i, A →⋆ₙₐ[ℂ] B i) :
    A →⋆ₙₐ[ℂ] UniformCStarProduct B where
  toFun x := ⟨fun i => ρ i x, memℓp_infty ⟨‖x‖, by
    rintro _ ⟨i, rfl⟩
    exact NonUnitalStarAlgHom.norm_apply_le (ρ i) x⟩⟩
  map_zero' := Subtype.ext (funext fun i => map_zero (ρ i))
  map_add' x y := Subtype.ext (funext fun i => map_add (ρ i) x y)
  map_mul' x y := Subtype.ext (funext fun i => map_mul (ρ i) x y)
  map_star' x := Subtype.ext (funext fun i => map_star (ρ i) x)
  map_smul' c x := Subtype.ext (funext fun i => map_smul (ρ i) c x)

lemma uniformProductHom_injective (ρ : ∀ i, A →⋆ₙₐ[ℂ] B i)
    (hρ : ∀ x y, (∀ i, ρ i x = ρ i y) → x = y) :
    Function.Injective (uniformProductHom ρ) := by
  intro x y hxy
  apply hρ x y
  intro i
  exact congrArg (fun x : UniformCStarProduct B => x i) hxy

lemma norm_le_iff_representations (ρ : ∀ i, A →⋆ₙₐ[ℂ] B i)
    (hρ : ∀ x y, (∀ i, ρ i x = ρ i y) → x = y)
    (x : A) {C : ℝ} (hC : 0 ≤ C) :
    ‖x‖ ≤ C ↔ ∀ i, ‖ρ i x‖ ≤ C := by
  constructor
  · exact fun hx i => (NonUnitalStarAlgHom.norm_apply_le (ρ i) x).trans hx
  · intro hx
    rw [← NonUnitalStarAlgHom.norm_map (uniformProductHom ρ)
      (uniformProductHom_injective ρ hρ) x]
    exact lp.norm_le_of_forall_le hC hx

lemma norm_matrix_le_iff_representations {n : Type*} [Fintype n]
    [PartialOrder A] [StarOrderedRing A]
    [∀ i, PartialOrder (B i)] [∀ i, StarOrderedRing (B i)]
    (ρ : ∀ i, A →⋆ₙₐ[ℂ] B i)
    (hρ : ∀ x y, (∀ i, ρ i x = ρ i y) → x = y)
    (M : CStarMatrix n n A) {C : ℝ} (hC : 0 ≤ C) :
    ‖M‖ ≤ C ↔ ∀ i, ‖CStarMatrix.mapₙₐ (ρ i) M‖ ≤ C := by
  apply norm_le_iff_representations (fun i => CStarMatrix.mapₙₐ (ρ i)) _ M hC
  intro M N hMN
  ext j k
  apply hρ
  intro i
  exact congrArg (fun z : CStarMatrix n n (B i) => z j k) (hMN i)

end UniformRepresentations



noncomputable instance (priority := 2000) : NonUnitalCStarAlgebra UniversalContraction :=
  CStarAlgebra.toNonUnitalCStarAlgebra _

noncomputable instance (priority := 2000) : PartialOrder UniversalContraction := CStarAlgebra.spectralOrder _

noncomputable instance (priority := 2000) : StarOrderedRing UniversalContraction := CStarAlgebra.spectralOrderedRing _

noncomputable instance : @StarOrderedRing UniversalContraction
    (NonUnitalCStarAlgebra.toNonUnitalNormedRing.toNonUnitalRing.toNonUnitalSemiring)
    (inferInstance) (NonUnitalCStarAlgebra.toStarRing) := by
  exact CStarAlgebra.spectralOrderedRing _

noncomputable def universalMatrixPolynomial {n : Type*}
    (s : Finset (List Bool)) (a : n → n → List Bool → ℂ) : CStarMatrix n n UniversalContraction :=
  CStarMatrix.ofMatrix fun i j => universalPolynomial s (a i j)

noncomputable def matrixPolynomialOperator {n H : Type*} [Fintype n]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (s : Finset (List Bool)) (a : n → n → List Bool → ℂ) (T : H →L[ℂ] H) :
    PiLp 2 (fun _ : n => H) →L[ℂ] PiLp 2 (fun _ : n => H) :=
  matrixOperator (CStarMatrix.ofMatrix fun i j => polynomialOperator s (a i j) T)

@[simp]
lemma matrixPolynomialOperator_apply {n H : Type*} [Fintype n]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (s : Finset (List Bool)) (a : n → n → List Bool → ℂ) (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : n => H)) (i : n) :
    matrixPolynomialOperator s a T x i = ∑ j, polynomialOperator s (a i j) T (x j) := by
  exact matrixOperator_apply _ x i

lemma norm_universalMatrixPolynomial_le_iff {n : Type*} [Fintype n]
    (s : Finset (List Bool)) (a : n → n → List Bool → ℂ) {C : ℝ} (hC : 0 ≤ C) :
    ‖universalMatrixPolynomial s a‖ ≤ C ↔
      ∀ π : ContractionRepresentation, ‖matrixPolynomialOperator s a π.operator‖ ≤ C := by
  have hsep : ∀ x y : UniversalContraction,
      (∀ π, contractionEvaluation π x = contractionEvaluation π y) → x = y := by
    intro x y h
    apply Subtype.ext
    exact Subtype.ext (funext h)
  refine (norm_matrix_le_iff_representations
    (fun π => (contractionEvaluation π).toNonUnitalStarAlgHom) hsep _ hC).trans ?_
  apply forall_congr'
  intro π
  have he : CStarMatrix.mapₙₐ (contractionEvaluation π).toNonUnitalStarAlgHom
      (universalMatrixPolynomial s a) =
      CStarMatrix.ofMatrix (fun i j => polynomialOperator s (a i j) π.operator) := by
    apply CStarMatrix.ext
    intro i j
    exact contractionEvaluation_polynomial π s (a i j)
  have hn : ‖CStarMatrix.mapₙₐ (contractionEvaluation π).toNonUnitalStarAlgHom
      (universalMatrixPolynomial s a)‖ = ‖matrixPolynomialOperator s a π.operator‖ := calc
    _ = ‖CStarMatrix.ofMatrix (fun i j => polynomialOperator s (a i j) π.operator)‖ :=
      congrArg norm he
    _ = _ := (norm_matrixOperator _).symm
  exact Iff.of_eq (congrArg (· ≤ C) hn)

section MatrixPolynomialCompression

variable {H n : Type} [Fintype n]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def piLpSubmoduleInclusion (K : Submodule ℂ H) :
    PiLp 2 (fun _ : n => K) →ₗᵢ[ℂ] PiLp 2 (fun _ : n => H) where
  toFun x := WithLp.toLp 2 (fun i => (x i : H))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := by simp only [PiLp.norm_eq_of_L2]; rfl

omit [CompleteSpace H] in
@[simp]

lemma piLpSubmoduleInclusion_apply (K : Submodule ℂ H)
    (x : PiLp 2 (fun _ : n => K)) (i : n) :
    piLpSubmoduleInclusion K x i = (x i : H) := rfl

lemma polynomialOperator_family_compression_exact {S : Type*} [Finite S]
    (s : Finset (List Bool)) (a : List Bool → ℂ) (T : H →L[ℂ] H)
    (ξ : S → H) (j : S) :
    let m := s.sup List.length
    let K := wordSpace (operatorLetters T) ξ m
    let ξ₀ : K := ⟨ξ j, testVector_mem_wordSpace _ _ _ j⟩
    (polynomialOperator s a (compress K T) ξ₀ : H) = polynomialOperator s a T (ξ j) := by
  dsimp only
  let m := s.sup List.length
  let K := wordSpace (operatorLetters T) ξ m
  let ξ₀ : K := ⟨ξ j, testVector_mem_wordSpace _ _ _ j⟩
  change K.subtypeL (polynomialOperator s a (compress K T) ξ₀) = _
  simp only [polynomialOperator, sum_apply, FunLike.coe_smul,
    Pi.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  have he : operatorLetters (compress K T) = fun i => compress K (operatorLetters T i) := by
    funext i
    exact operatorLetters_compress K T i
  rw [he]
  exact wordSpace_compression_exact (operatorLetters T) ξ m w (Finset.le_sup hw) j

lemma matrixPolynomialOperator_compression_exact
    (s : Finset (List Bool)) (a : n → n → List Bool → ℂ) (T : H →L[ℂ] H)
    (ξ : PiLp 2 (fun _ : n => H)) :
    let m := s.sup List.length
    let K := wordSpace (operatorLetters T) (fun j => ξ j) m
    let ξ₀ : PiLp 2 (fun _ : n => K) := WithLp.toLp 2
      (fun j => ⟨ξ j, testVector_mem_wordSpace _ _ _ j⟩)
    piLpSubmoduleInclusion K (matrixPolynomialOperator s a (compress K T) ξ₀) =
      matrixPolynomialOperator s a T ξ := by
  dsimp only
  ext i
  rw [piLpSubmoduleInclusion_apply, matrixPolynomialOperator_apply]
  simp only [Submodule.coe_sum, matrixPolynomialOperator_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact polynomialOperator_family_compression_exact s (a i j) T (fun j => ξ j) j

end MatrixPolynomialCompression

lemma norm_universalMatrixPolynomial_le_of_finite_tests {n : Type} [Fintype n]
    (s : Finset (List Bool)) (a : n → n → List Bool → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ π : ContractionRepresentation, FiniteDimensional ℂ π.hilbert →
      ‖matrixPolynomialOperator s a π.operator‖ ≤ C) :
    ‖universalMatrixPolynomial s a‖ ≤ C := by
  classical
  apply (norm_universalMatrixPolynomial_le_iff s a hC).mpr
  intro π
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro ξ
  by_cases hξ : ξ = 0
  · simp [hξ]
  obtain ⟨j, hj⟩ : ∃ j, ξ j ≠ 0 := by
    by_contra he
    push Not at he
    exact hξ (by ext j; exact he j)
  let m := s.sup List.length
  let K := wordSpace (operatorLetters π.operator) (fun j => ξ j) m
  let : Nontrivial K := ⟨⟨⟨ξ j, testVector_mem_wordSpace _ _ _ j⟩, 0,
    fun he => hj (congrArg Subtype.val he)⟩⟩
  let π₀ : ContractionRepresentation :=
    { hilbert := { Carrier := K }
      operator := compress K π.operator
      norm_operator_le_one := (norm_compress_le K π.operator).trans π.norm_operator_le_one }
  let ξ₀ : PiLp 2 (fun _ : n => K) := WithLp.toLp 2
    (fun j => ⟨ξ j, testVector_mem_wordSpace _ _ _ j⟩)
  have he : piLpSubmoduleInclusion K (matrixPolynomialOperator s a π₀.operator ξ₀) =
      matrixPolynomialOperator s a π.operator ξ :=
    matrixPolynomialOperator_compression_exact s a π.operator ξ
  have hξ₀ : ‖ξ₀‖ = ‖ξ‖ := (piLpSubmoduleInclusion K).norm_map ξ₀ |>.symm
  rw [← he, LinearIsometry.norm_map]
  exact (ContinuousLinearMap.le_opNorm _ ξ₀).trans
    ((mul_le_mul_of_nonneg_right (h π₀ inferInstance) (norm_nonneg ξ₀)).trans_eq
      (congrArg (C * ·) hξ₀))

end


end
end

end WeakPureInfiniteness

end

end OAI
