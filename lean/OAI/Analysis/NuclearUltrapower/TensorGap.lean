import OAI.Analysis.NuclearUltrapower.HilbertSchmidt
import OAI.Analysis.NuclearUltrapower.VariableUltraproduct
import OAI.Analysis.NuclearUltrapower.Laplacian

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower

section MatrixAction
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual left action of an operator-valued matrix on a Hilbert direct sum. -/
def operatorMatrixAction (M : CStarMatrix n n (H →L[ℂ] H)) :
    PiLp 2 (fun _ : n => H) →L[ℂ] PiLp 2 (fun _ : n => H) where
  toFun x := WithLp.toLp 2 (fun i => ∑ j, M i j (x j))
  map_add' x y := by ext i; simp [map_add, Finset.sum_add_distrib]
  map_smul' c x := by ext i; simp [map_smul, Finset.smul_sum]
  cont := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    exact continuous_finsetSum _ (fun j _ => (M i j).continuous.comp (PiLp.proj (𝕜 := ℂ) 2 (fun _ : n => H) j).continuous)

omit [DecidableEq n] [CompleteSpace H] in
@[simp] theorem operatorMatrixAction_apply (M : CStarMatrix n n (H →L[ℂ] H))
    (x : PiLp 2 (fun _ : n => H)) (i : n) : operatorMatrixAction M x i = ∑ j, M i j (x j) := rfl

/-- Matrix amplification is a genuine unital star homomorphism. -/
def operatorMatrixActionHom : CStarMatrix n n (H →L[ℂ] H) →⋆ₐ[ℂ]
    (PiLp 2 (fun _ : n => H) →L[ℂ] PiLp 2 (fun _ : n => H)) where
  toFun := operatorMatrixAction
  map_zero' := by ext x i; simp
  map_one' := by ext x i; simp [CStarMatrix.one_apply, apply_ite, ite_apply]
  map_add' M N := by ext x i; simp [CStarMatrix.add_apply, Finset.sum_add_distrib]
  map_mul' M N := by
    ext x i
    simp only [operatorMatrixAction_apply, CStarMatrix.mul_apply, sum_apply,
      mul_apply_eq_comp, map_sum]
    rw [Finset.sum_comm]
  commutes' c := by
    ext x i
    simp [CStarMatrix.algebraMap_apply, apply_ite, ite_apply]
  map_star' M := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    simp only [PiLp.inner_apply, operatorMatrixAction_apply, CStarMatrix.star_apply,
      sum_inner, inner_sum]
    change (∑ i, ∑ j, inner ℂ ((M j i).adjoint (x j)) (y i)) = _
    simp only [ContinuousLinearMap.adjoint_inner_left]
    rw [Finset.sum_comm]

@[simp] theorem operatorMatrixActionHom_apply (M : CStarMatrix n n (H →L[ℂ] H))
    (x : PiLp 2 (fun _ : n => H)) (i : n) : operatorMatrixActionHom (n := n) (H := H) M x i = ∑ j, M i j (x j) := rfl

/-- One-column vectors recover every coefficient; amplification is faithful. -/
theorem operatorMatrixActionHom_injective : Function.Injective (operatorMatrixActionHom (n := n) (H := H)) := by
  intro M N h
  apply CStarMatrix.ext
  intro i j
  ext x
  have he := congrArg (fun T : PiLp 2 (fun _ : n => H) →L[ℂ] PiLp 2 (fun _ : n => H) =>
    T (PiLp.single 2 j x) i) h
  simpa [operatorMatrixActionHom_apply, PiLp.single_apply, apply_ite] using he

theorem operatorMatrixActionHom_isometry : Isometry (operatorMatrixActionHom (n := n) (H := H)) :=
  NonUnitalStarAlgHom.isometry _ operatorMatrixActionHom_injective

end MatrixAction

open scoped TensorProduct
section TensorMatrix
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The fixed-factor tensor/direct-sum identification, with its actual Hilbert norm. -/
def tensorPiLinearEquiv (b : OrthonormalBasis n ℂ F) :
    E ⊗[ℂ] F ≃ₗ[ℂ] PiLp 2 (fun _ : n => E) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ E)
    (b.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 ℂ (n → ℂ)))).trans
      ((TensorProduct.piScalarRight ℂ ℂ E n).trans (WithLp.linearEquiv 2 ℂ (n → E)).symm)

@[simp] theorem tensorPiLinearEquiv_tmul (b : OrthonormalBasis n ℂ F)
    (x : E) (y : F) (i : n) : tensorPiLinearEquiv b (x ⊗ₜ[ℂ] y) i = b.repr y i • x := by
  simp [tensorPiLinearEquiv]

theorem tensorPiLinearEquiv_inner (b : OrthonormalBasis n ℂ F) (z w : E ⊗[ℂ] F) :
    inner ℂ (tensorPiLinearEquiv b z) (tensorPiLinearEquiv b w) = inner ℂ z w := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp [hz, hz', TensorProduct.inner_def]
  | tmul x y =>
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp [hw, hw', TensorProduct.inner_def]
    | tmul x' y' =>
      simp only [PiLp.inner_apply, tensorPiLinearEquiv_tmul, inner_smul_left, inner_smul_right,
        TensorProduct.inner_tmul]
      calc
        _ = (∑ i, starRingEnd ℂ (b.repr y i) * b.repr y' i) * inner ℂ x x' := by
          simp only [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = inner ℂ y y' * inner ℂ x x' := by
          congr 1
          simpa only [PiLp.inner_apply, RCLike.inner_apply, mul_comm] using b.repr.inner_map_map y y'
        _ = _ := mul_comm _ _

def tensorPiIsometry (b : OrthonormalBasis n ℂ F) :
    E ⊗[ℂ] F ≃ₗᵢ[ℂ] PiLp 2 (fun _ : n => E) :=
  (tensorPiLinearEquiv b).isometryOfInner (tensorPiLinearEquiv_inner b)

@[simp] theorem tensorPiIsometry_tmul (b : OrthonormalBasis n ℂ F)
    (x : E) (y : F) (i : n) : tensorPiIsometry b (x ⊗ₜ[ℂ] y) i = b.repr y i • x :=
  tensorPiLinearEquiv_tmul b x y i

/-- This matrix has scalar coefficients in the fixed factor; the first factor
may be infinite-dimensional. -/
def tensorOperatorMatrix (b : OrthonormalBasis n ℂ F)
    (U : E →L[ℂ] E) (V : F →L[ℂ] F) : CStarMatrix n n (E →L[ℂ] E) :=
  CStarMatrix.ofMatrix (fun i j => b.repr (V (b j)) i • U)

omit [DecidableEq n] in
@[simp] theorem tensorOperatorMatrix_apply (b : OrthonormalBasis n ℂ F)
    (U : E →L[ℂ] E) (V : F →L[ℂ] F) (i j : n) :
    tensorOperatorMatrix b U V i j = b.repr (V (b j)) i • U := rfl

/-- Entry-by-entry compatibility of the operator tensor with matrix amplification. -/
theorem tensorOperatorMatrix_action [CompleteSpace E] (b : OrthonormalBasis n ℂ F)
    (U : E →L[ℂ] E) (V : F →L[ℂ] F) (z : E ⊗[ℂ] F) :
    operatorMatrixActionHom (n := n) (H := E) (tensorOperatorMatrix b U V) (tensorPiIsometry b z) =
      tensorPiIsometry b (TensorProduct.mapL U V z) := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul x y =>
    ext i
    simp only [operatorMatrixActionHom_apply, tensorOperatorMatrix_apply, smul_apply,
      tensorPiIsometry_tmul, map_smul, TensorProduct.mapL_tmul, smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    have h := congrArg (fun v : F => b.repr (V v) i) (b.sum_repr y)
    simpa only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply,
      WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, mul_comm] using h

end TensorMatrix
end NuclearUltrapower

namespace NuclearUltrapower
open scoped TensorProduct
section MatrixGap
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

def tensorPiUnitary (b : OrthonormalBasis n ℂ F) (U : E ≃ₗᵢ[ℂ] E) (V : F ≃ₗᵢ[ℂ] F) :
    PiLp 2 (fun _ : n => E) ≃ₗᵢ[ℂ] PiLp 2 (fun _ : n => E) :=
  ((tensorPiIsometry b).symm.trans (TensorProduct.congrIsometry U V)).trans (tensorPiIsometry b)

omit [CompleteSpace E] in
@[simp] theorem tensorPiUnitary_apply_tensorPi (b : OrthonormalBasis n ℂ F)
    (U : E ≃ₗᵢ[ℂ] E) (V : F ≃ₗᵢ[ℂ] F) (z : E ⊗[ℂ] F) :
    tensorPiUnitary b U V (tensorPiIsometry b z) =
      tensorPiIsometry b (TensorProduct.congrIsometry U V z) := by
  simp [tensorPiUnitary]

theorem tensorOperatorMatrix_conjugacy (b : OrthonormalBasis n ℂ F)
    (U : E ≃ₗᵢ[ℂ] E) (V : F ≃ₗᵢ[ℂ] F) :
    operatorMatrixActionHom (n := n) (H := E) (tensorOperatorMatrix b U V) =
      (tensorPiUnitary b U V : PiLp 2 (fun _ : n => E) →L[ℂ] PiLp 2 (fun _ : n => E)) := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := (tensorPiIsometry b).surjective x
  change operatorMatrixActionHom (n := n) (H := E) (tensorOperatorMatrix b U V)
    (tensorPiIsometry b z) = tensorPiUnitary b U V (tensorPiIsometry b z)
  rw [tensorOperatorMatrix_action, tensorPiUnitary_apply_tensorPi]
  congr 1
  simp only [TensorProduct.mapL_apply, TensorProduct.congrIsometry_apply]
  rfl

/-- Fixed-factor matrix norms see precisely the tensor Kazhdan estimate. -/
theorem tensorMatrix_complement_bound {Γ : Type*} (S : Finset Γ)
    (b : OrthonormalBasis n ℂ F) (U : Γ → (E ≃ₗᵢ[ℂ] E)) (V : Γ → (F ≃ₗᵢ[ℂ] F))
    {κ : ℝ} (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : ∀ z : E ⊗[ℂ] F, κ * ‖z‖ ^ 2 ≤
      ∑ s ∈ S, ‖TensorProduct.congrIsometry (U s) (V s) z - z‖ ^ 2) :
    ‖(4 * (S.card : ℝ)) • (1 : CStarMatrix n n (E →L[ℂ] E)) -
      laplacian S (fun s => tensorOperatorMatrix b (U s) (V s))‖ ≤
        4 * (S.card : ℝ) - κ := by
  let u : Γ → unitary (PiLp 2 (fun _ : n => E) →L[ℂ] PiLp 2 (fun _ : n => E)) :=
    fun s => Unitary.linearIsometryEquiv.symm (tensorPiUnitary b (U s) (V s))
  have hPi : κ • (1 : PiLp 2 (fun _ : n => E) →L[ℂ] PiLp 2 (fun _ : n => E)) ≤
      laplacian S (fun s => (u s : PiLp 2 (fun _ : n => E) →L[ℂ] PiLp 2 (fun _ : n => E))) := by
    rw [laplacian_lower_iff]
    intro x
    obtain ⟨z, rfl⟩ := (tensorPiIsometry b).surjective x
    have hd (s : Γ) : (u s : PiLp 2 (fun _ : n => E) →L[ℂ] PiLp 2 (fun _ : n => E))
        (tensorPiIsometry b z) - tensorPiIsometry b z =
        tensorPiIsometry b (TensorProduct.congrIsometry (U s) (V s) z - z) := by
      change tensorPiUnitary b (U s) (V s) (tensorPiIsometry b z) - _ = _
      simp only [tensorPiUnitary_apply_tensorPi, map_sub]
    simpa only [hd, (tensorPiIsometry b).norm_map] using hgap z
  have hbound := laplacian_complement_norm S u hκ hPi
  have hmap : operatorMatrixActionHom (n := n) (H := E)
      ((4 * (S.card : ℝ)) • (1 : CStarMatrix n n (E →L[ℂ] E)) -
        laplacian S (fun s => tensorOperatorMatrix b (U s) (V s))) =
      (4 * (S.card : ℝ)) • (1 : PiLp 2 (fun _ : n => E) →L[ℂ] PiLp 2 (fun _ : n => E)) -
        laplacian S (fun s => (u s : PiLp 2 (fun _ : n => E) →L[ℂ] PiLp 2 (fun _ : n => E))) := by
    have hs : operatorMatrixActionHom (n := n) (H := E)
        ((4 * (S.card : ℝ)) • (1 : CStarMatrix n n (E →L[ℂ] E))) =
        (4 * (S.card : ℝ)) • operatorMatrixActionHom (n := n) (H := E) 1 :=
      (operatorMatrixActionHom (n := n) (H := E)).toAlgHom.map_smul_of_tower _ _
    rw [map_sub, hs]
    simp only [map_one, laplacian, map_sum, map_mul, map_star, map_sub,
      tensorOperatorMatrix_conjugacy]
    rfl
  rw [← hmap] at hbound
  exact (NonUnitalStarAlgHom.norm_map
    (operatorMatrixActionHom (n := n) (H := E)).toNonUnitalStarAlgHom
    (operatorMatrixActionHom_injective (n := n) (H := E)) _).symm.le.trans hbound
end MatrixGap
end NuclearUltrapower

namespace NuclearUltrapower

section CoefficientMatrix
variable {A B Γ n : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [Fintype n] [DecidableEq n]

/-- An elementary tensor in coordinates of the fixed second factor. -/
def coefficientMatrix (c : n → n → ℂ) (a : A) : CStarMatrix n n A :=
  CStarMatrix.ofMatrix (fun j k => c j k • a)

omit [Fintype n] [DecidableEq n] in
@[simp] theorem coefficientMatrix_apply (c : n → n → ℂ) (a : A) (j k : n) :
    coefficientMatrix c a j k = c j k • a := rfl

@[simp] theorem matrixMap_coefficientMatrix (φ : A →⋆ₐ[ℂ] B) (c : n → n → ℂ) (a : A) :
    matrixMap n φ (coefficientMatrix c a) = coefficientMatrix c (φ a) := by
  ext j k
  exact map_smul φ _ _

@[simp] theorem map_laplacian (φ : A →⋆ₐ[ℂ] B) (S : Finset Γ) (a : Γ → A) :
    φ (laplacian S a) = laplacian S (fun s => φ (a s)) := by
  simp only [laplacian, map_sum, map_mul, map_star, map_sub, map_one]

@[simp] theorem map_laplacian_complement (φ : A →⋆ₐ[ℂ] B) (S : Finset Γ)
    (a : Γ → A) (R : ℝ) :
    φ (R • (1 : A) - laplacian S a) = R • (1 : B) - laplacian S (fun s => φ (a s)) := by
  rw [map_sub, show φ (R • (1 : A)) = R • φ 1 from φ.toAlgHom.map_smul_of_tower _ _]
  simp only [map_one, map_laplacian]

end CoefficientMatrix

namespace VariableUltra
variable {ι : Type u} (A : ι → Type v) [∀ i, CStarAlgebra (A i)]
  [∀ i, Nontrivial (A i)] (ω : Ultrafilter ι)

/-- Evaluation is an actual unital star homomorphism. -/
def eval (i : ι) : Seq A →⋆ₐ[ℂ] A i where
  toFun x := x i
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl
  commutes' _ := rfl

@[simp] theorem eval_apply (i : ι) (x : Seq A) : eval A i x = x i := rfl

/-- Arbitrary coordinate unitaries are bounded, without a dimension bound. -/
def unitarySequence (u : ∀ i, unitary (A i)) : unitary (Seq A) :=
  ⟨⟨fun i => (u i : A i), memℓp_infty ⟨1, by
    rintro _ ⟨i, rfl⟩
    exact (CStarRing.norm_coe_unitary (u i)).le⟩⟩, by
    constructor <;> ext i
    · exact Unitary.coe_star_mul_self (u i)
    · exact Unitary.coe_mul_star_self (u i)⟩

@[simp] theorem unitarySequence_apply (u : ∀ i, unitary (A i)) (i : ι) :
    (unitarySequence A u : Seq A) i = u i := rfl

variable (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n]
local instance gapEntryOrder (i : ι) : PartialOrder (A i) := CStarAlgebra.spectralOrder _
local instance gapEntryStarOrder (i : ι) : StarOrderedRing (A i) := CStarAlgebra.spectralOrderedRing _
local instance gapSeqOrder : PartialOrder (Seq A) := CStarAlgebra.spectralOrder _
local instance gapSeqStarOrder : StarOrderedRing (Seq A) := CStarAlgebra.spectralOrderedRing _
local instance gapQuotientOrder : PartialOrder (Algebra A ω) := CStarAlgebra.spectralOrder _
local instance gapQuotientStarOrder : StarOrderedRing (Algebra A ω) := CStarAlgebra.spectralOrderedRing _

omit [Nonempty n] in
@[simp] theorem matrixFamily_eval (M : CStarMatrix n n (Seq A)) (i : ι) :
    matrixFamily A n M i = matrixMap n (eval A i) M := rfl

/-- Fixed-size polynomial transfer, with only an EVENTUAL coordinate bound. -/
theorem coefficient_complement_quotient_bound {Γ : Type*} (S : Finset Γ)
    (u : Γ → Seq A) (c : Γ → n → n → ℂ) (R C : ℝ)
    (h : ∀ᶠ i in (ω : Filter ι),
      ‖R • (1 : CStarMatrix n n (A i)) -
        laplacian S (fun s => coefficientMatrix (c s) (u s i))‖ ≤ C) :
    ‖R • (1 : CStarMatrix n n (Algebra A ω)) -
      laplacian S (fun s => coefficientMatrix (c s) (mk A ω (u s)))‖ ≤ C := by
  let M : CStarMatrix n n (Seq A) := R • (1 : CStarMatrix n n (Seq A)) -
    laplacian S (fun s => coefficientMatrix (c s) (u s))
  have hmap : matrixMap n (mk A ω) M =
      R • (1 : CStarMatrix n n (Algebra A ω)) -
        laplacian S (fun s => coefficientMatrix (c s) (mk A ω (u s))) := by
    calc
      _ = R • (1 : CStarMatrix n n (Algebra A ω)) -
          laplacian S (fun s => matrixMap n (mk A ω) (coefficientMatrix (c s) (u s))) :=
        map_laplacian_complement (matrixMap n (mk A ω)) S _ R
      _ = _ := by simp only [matrixMap_coefficientMatrix]
  rw [← hmap]
  apply matrixMap_mk_norm_le
  filter_upwards [h] with i hi
  rw [matrixFamily_eval]
  have hmi : matrixMap n (eval A i) M =
      R • (1 : CStarMatrix n n (A i)) -
        laplacian S (fun s => coefficientMatrix (c s) (u s i)) := by
    have hs : matrixMap n (eval A i) (R • (1 : CStarMatrix n n (Seq A))) =
        R • matrixMap n (eval A i) 1 :=
      (matrixMap n (eval A i)).toAlgHom.map_smul_of_tower _ _
    dsimp only [M]
    rw [map_sub, hs]
    simp only [map_one, map_laplacian, matrixMap_coefficientMatrix, eval_apply]
  rw [hmi]
  exact hi

end VariableUltra
end NuclearUltrapower

namespace NuclearUltrapower
open scoped TensorProduct
section NoInvariant
variable {Γ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A strict complemented-norm gap excludes every common fixed vector. -/
theorem no_invariant_of_complement_norm (S : Finset Γ) (a : Γ → (H →L[ℂ] H))
    {κ : ℝ} (hκ : 0 < κ)
    (h : ‖(4 * (S.card : ℝ)) • (1 : H →L[ℂ] H) - laplacian S a‖ ≤
      4 * (S.card : ℝ) - κ) (x : H) (hx : ∀ s ∈ S, a s x = x) : x = 0 := by
  have hxL : laplacian S a x = 0 := by
    simp only [laplacian, sum_apply, mul_apply_eq_comp]
    apply Finset.sum_eq_zero
    intro s hs
    rw [sub_apply, one_apply_eq_self, hx s hs, sub_self, map_zero]
  have hh := ((4 * (S.card : ℝ)) • (1 : H →L[ℂ] H) - laplacian S a).le_opNorm x
  rw [sub_apply, smul_apply, one_apply_eq_self, hxL, sub_zero, norm_smul,
    Real.norm_of_nonneg (by positivity : 0 ≤ 4 * (S.card : ℝ))] at hh
  have hbound := hh.trans (mul_le_mul_of_nonneg_right h (norm_nonneg x))
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg x]
end NoInvariant

namespace VariableUltra
variable {ι : Type u} (E : ι → Type v)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)] [∀ i, Nontrivial (E i)] (ω : Ultrafilter ι)

abbrev operatorSeq := Seq (fun i => E i →L[ℂ] E i)
abbrev operatorQuotient := Algebra (fun i => E i →L[ℂ] E i) ω

def isoSequence (U : ∀ i, E i ≃ₗᵢ[ℂ] E i) : unitary (operatorSeq E) :=
  unitarySequence _ (fun i => Unitary.linearIsometryEquiv.symm (U i))

def starAlgToStarMonoid {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) : A →⋆* B where
  toFun := φ
  map_one' := map_one φ
  map_mul' := map_mul φ
  map_star' := map_star φ

def quotientIsoUnitary (U : ∀ i, E i ≃ₗᵢ[ℂ] E i) : unitary (operatorQuotient E ω) :=
  Unitary.map (starAlgToStarMonoid (mk (fun i => E i →L[ℂ] E i) ω)) (isoSequence E U)

variable {K F : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

def representedIso (φ : operatorQuotient E ω →⋆ₐ[ℂ] (K →L[ℂ] K))
    (U : ∀ i, E i ≃ₗᵢ[ℂ] E i) : K ≃ₗᵢ[ℂ] K :=
  Unitary.linearIsometryEquiv (Unitary.map (starAlgToStarMonoid φ) (quotientIsoUnitary E ω U))

local instance operatorQuotientOrder : PartialOrder (operatorQuotient E ω) :=
  CStarAlgebra.spectralOrder _
local instance operatorQuotientStarOrder : StarOrderedRing (operatorQuotient E ω) :=
  CStarAlgebra.spectralOrderedRing _

/-- The strict coordinate tensor gap survives in EVERY unital representation
of the varying matrix quotient. No faithfulness is needed here. -/
theorem quotient_tensor_complement_bound {Γ : Type*} (S : Finset Γ)
    (b : OrthonormalBasis n ℂ F) (U : ∀ i, Γ → (E i ≃ₗᵢ[ℂ] E i))
    (V : Γ → (F ≃ₗᵢ[ℂ] F)) {κ : ℝ} (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : ∀ᶠ i in (ω : Filter ι), ∀ z : E i ⊗[ℂ] F,
      κ * ‖z‖ ^ 2 ≤ ∑ s ∈ S, ‖TensorProduct.congrIsometry (U i s) (V s) z - z‖ ^ 2)
    (φ : operatorQuotient E ω →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    ‖(4 * (S.card : ℝ)) • (1 : CStarMatrix n n (K →L[ℂ] K)) -
      laplacian S (fun s => tensorOperatorMatrix b
        (representedIso E ω φ (fun i => U i s)) (V s))‖ ≤ 4 * (S.card : ℝ) - κ := by
  let u : Γ → operatorSeq E := fun s => (isoSequence E (fun i => U i s) : operatorSeq E)
  let c : Γ → n → n → ℂ := fun s j k => b.repr (V s (b k)) j
  have hcoord : ∀ᶠ i in (ω : Filter ι),
      ‖(4 * (S.card : ℝ)) • (1 : CStarMatrix n n (E i →L[ℂ] E i)) -
        laplacian S (fun s => coefficientMatrix (c s) (u s i))‖ ≤ 4 * (S.card : ℝ) - κ := by
    filter_upwards [hgap] with i hi
    exact tensorMatrix_complement_bound S b (U i) V hκ hi
  have hQ := coefficient_complement_quotient_bound (fun i => E i →L[ℂ] E i) ω n S u c
    (4 * (S.card : ℝ)) (4 * (S.card : ℝ) - κ) hcoord
  have hφ := (NonUnitalStarAlgHom.norm_apply_le (matrixMap n φ).toNonUnitalStarAlgHom
    ((4 * (S.card : ℝ)) • (1 : CStarMatrix n n (operatorQuotient E ω)) -
      laplacian S (fun s => coefficientMatrix (c s) (mk _ ω (u s))))).trans hQ
  change ‖matrixMap n φ _‖ ≤ _ at hφ
  have he : matrixMap n φ
      ((4 * (S.card : ℝ)) • (1 : CStarMatrix n n (operatorQuotient E ω)) -
        laplacian S (fun s => coefficientMatrix (c s) (mk _ ω (u s)))) =
      (4 * (S.card : ℝ)) • (1 : CStarMatrix n n (K →L[ℂ] K)) -
        laplacian S (fun s => coefficientMatrix (c s) (φ (mk _ ω (u s)))) := by
    have hs : matrixMap n φ ((4 * (S.card : ℝ)) • (1 : CStarMatrix n n (operatorQuotient E ω))) =
        (4 * (S.card : ℝ)) • matrixMap n φ 1 :=
      (matrixMap n φ).toAlgHom.map_smul_of_tower _ _
    rw [map_sub, hs]
    simp only [map_one, map_laplacian, matrixMap_coefficientMatrix]
  rw [he] at hφ
  exact hφ

/-- In particular a tensor intertwiner in a quotient representation must vanish. -/
theorem quotient_tensor_no_invariants {Γ : Type*} (S : Finset Γ)
    (b : OrthonormalBasis n ℂ F) (U : ∀ i, Γ → (E i ≃ₗᵢ[ℂ] E i))
    (V : Γ → (F ≃ₗᵢ[ℂ] F)) {κ : ℝ} (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : ∀ᶠ i in (ω : Filter ι), ∀ z : E i ⊗[ℂ] F,
      κ * ‖z‖ ^ 2 ≤ ∑ s ∈ S, ‖TensorProduct.congrIsometry (U i s) (V s) z - z‖ ^ 2)
    (φ : operatorQuotient E ω →⋆ₐ[ℂ] (K →L[ℂ] K))
    (z : K ⊗[ℂ] F)
    (hz : ∀ s ∈ S, TensorProduct.congrIsometry
      (representedIso E ω φ (fun i => U i s)) (V s) z = z) : z = 0 := by
  have hm := quotient_tensor_complement_bound E ω S b U V hκ hgap φ
  let u : Γ → (PiLp 2 (fun _ : n => K) →L[ℂ] PiLp 2 (fun _ : n => K)) :=
    fun s => tensorPiUnitary b (representedIso E ω φ (fun i => U i s)) (V s)
  have hnorm : ‖(4 * (S.card : ℝ)) • (1 : PiLp 2 (fun _ : n => K) →L[ℂ] PiLp 2 (fun _ : n => K)) -
      laplacian S u‖ ≤ 4 * (S.card : ℝ) - κ := by
    have ha := (NonUnitalStarAlgHom.norm_apply_le
      (operatorMatrixActionHom (n := n) (H := K)).toNonUnitalStarAlgHom _).trans hm
    change ‖operatorMatrixActionHom (n := n) (H := K) _‖ ≤ _ at ha
    have he : operatorMatrixActionHom (n := n) (H := K)
        ((4 * (S.card : ℝ)) • (1 : CStarMatrix n n (K →L[ℂ] K)) -
          laplacian S (fun s => tensorOperatorMatrix b
            (representedIso E ω φ (fun i => U i s)) (V s))) =
        (4 * (S.card : ℝ)) • (1 : PiLp 2 (fun _ : n => K) →L[ℂ] PiLp 2 (fun _ : n => K)) -
          laplacian S u := by
      have hs : operatorMatrixActionHom (n := n) (H := K)
          ((4 * (S.card : ℝ)) • (1 : CStarMatrix n n (K →L[ℂ] K))) =
          (4 * (S.card : ℝ)) • operatorMatrixActionHom (n := n) (H := K) 1 :=
        (operatorMatrixActionHom (n := n) (H := K)).toAlgHom.map_smul_of_tower _ _
      rw [map_sub, hs]
      simp only [map_one, laplacian, map_sum, map_mul, map_star, map_sub,
        tensorOperatorMatrix_conjugacy]
      rfl
    rw [he] at ha
    exact ha
  have hy := no_invariant_of_complement_norm S u hκ0 hnorm (tensorPiIsometry b z) (by
    intro s hs
    change tensorPiUnitary _ _ _ (tensorPiIsometry b z) = _
    rw [tensorPiUnitary_apply_tensorPi, hz s hs])
  exact (tensorPiIsometry b).injective (by simpa using hy)
end VariableUltra
end NuclearUltrapower

end
end
end
end
end

end OAI
