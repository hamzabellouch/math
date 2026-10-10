import OAI.Probability.SignedSweeps.MarkedSites

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {Z E : Type*} [Fintype Z]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

abbrev HilbertFibers (Z E : Type*) [Fintype Z] [NormedAddCommGroup E] :=
  PiLp 2 (fun _ : Z => E)

def fiberEvaluation (z : Z) : HilbertFibers Z E →ₗ[ℂ] E where
  toFun f := f.ofLp z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def fiberInsertionLinear (z : Z) : E →ₗ[ℂ] HilbertFibers Z E where
  toFun x := PiLp.single 2 z x
  map_add' x y := by
    apply PiLp.ext
    intro w
    simp only [PiLp.single_apply, PiLp.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    apply PiLp.ext
    intro w
    simp only [PiLp.single_apply, PiLp.smul_apply]
    split_ifs <;> simp

omit [FiniteDimensional ℂ E] in
@[simp] lemma fiberInsertionLinear_apply [FiniteDimensional ℂ E] (z w : Z) (x : E) :
    (fiberInsertionLinear z x).ofLp w = if w = z then x else 0 := by
  exact PiLp.single_apply 2 E z x w

def fiberInsertion (z : Z) : E →ₗᵢ[ℂ] HilbertFibers Z E where
  toLinearMap := fiberInsertionLinear z
  norm_map' x := by
    rw [PiLp.norm_eq_of_L2]
    simp only [fiberInsertionLinear_apply]
    simp only [apply_ite, norm_zero]
    simp [Real.sqrt_sq]

@[simp] lemma fiberInsertion_apply (z w : Z) (x : E) :
    (fiberInsertion z x).ofLp w = if w = z then x else 0 := fiberInsertionLinear_apply z w x

@[simp] lemma fiberEvaluation_insertion (z : Z) (x : E) :
    fiberEvaluation z (fiberInsertion z x) = x := by
  change (fiberInsertion z x).ofLp z = x
  simp

lemma fiberInsertion_adjoint (z : Z) :
    (fiberInsertion (E:=E) z).toLinearMap.adjoint = fiberEvaluation z := by
  apply LinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [LinearMap.adjoint_inner_right]
  change inner ℂ (fiberInsertion z y) x = inner ℂ y (x.ofLp z)
  rw [PiLp.inner_apply]
  simp only [fiberInsertion_apply]
  rw [Finset.sum_eq_single z]
  · simp
  · intro w _ hw
    simp [hw]
  · simp

lemma hilbertBlock_fiber_apply (z w : Z) (A : E →ₗ[ℂ] E) (x : HilbertFibers Z E) :
    (hilbertBlock (fiberInsertion z) A x).ofLp w = if w = z then A (x.ofLp z) else 0 := by
  rw [hilbertBlock_apply, fiberInsertion_adjoint, fiberInsertion_apply]; rfl

def fiberDiagonal (A : Z → E →ₗ[ℂ] E) : HilbertFibers Z E →ₗ[ℂ] HilbertFibers Z E where
  toFun x := WithLp.toLp 2 (fun z => A z (x.ofLp z))
  map_add' x y := by apply PiLp.ext; intro z; exact map_add (A z) _ _
  map_smul' c x := by apply PiLp.ext; intro z; exact map_smul (A z) _ _

omit [FiniteDimensional ℂ E] in
@[simp] lemma fiberDiagonal_apply [FiniteDimensional ℂ E]
    (A : Z → E →ₗ[ℂ] E) (x : HilbertFibers Z E) (z : Z) :
    (fiberDiagonal A x).ofLp z = A z (x.ofLp z) := rfl

lemma fiberDiagonal_eq_sum (A : Z → E →ₗ[ℂ] E) :
    fiberDiagonal A = ∑ z, hilbertBlock (fiberInsertion z) (A z) := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro z
  simp only [fiberDiagonal_apply, LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply,
    hilbertBlock_fiber_apply]
  simp

omit [FiniteDimensional ℂ E] in
lemma fiberDiagonal_mul [FiniteDimensional ℂ E] (A B : Z → E →ₗ[ℂ] E) :
    fiberDiagonal A * fiberDiagonal B = fiberDiagonal (fun z => A z * B z) := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro z
  rfl

omit [FiniteDimensional ℂ E] in
lemma fiberDiagonal_positive [FiniteDimensional ℂ E]
    (A : Z → E →ₗ[ℂ] E) (hA : ∀ z, (A z).IsPositive) :
    (fiberDiagonal A).IsPositive := by
  constructor
  · intro x y
    rw [PiLp.inner_apply, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro z _
    exact (hA z).isSymmetric _ _
  · intro x
    rw [PiLp.inner_apply, map_sum]
    exact Finset.sum_nonneg (fun z _ => (hA z).re_inner_nonneg_left _)

lemma fiberDiagonal_idempotent (A : Z → E →ₗ[ℂ] E) (hA : ∀ z, A z * A z = A z) :
    fiberDiagonal A * fiberDiagonal A = fiberDiagonal A := by
  rw [fiberDiagonal_mul]
  simp only [hA]

lemma trace_fiberDiagonal_mul (P : Z → E →ₗ[ℂ] E)
    (A : HilbertFibers Z E →ₗ[ℂ] HilbertFibers Z E) :
    LinearMap.trace ℂ (HilbertFibers Z E) (fiberDiagonal P * A) =
      ∑ z, LinearMap.trace ℂ E
        (P z * (fiberEvaluation z ∘ₗ A ∘ₗ (fiberInsertion z).toLinearMap)) := by
  rw [fiberDiagonal_eq_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro z hz
  change LinearMap.trace ℂ _ ((fiberInsertion z).toLinearMap ∘ₗ
    (P z ∘ₗ (fiberInsertion z).toLinearMap.adjoint ∘ₗ A)) = _
  rw [LinearMap.trace_comp_comm', fiberInsertion_adjoint]
  rfl

end SignedSweeps
end

end OAI
