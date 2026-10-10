import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace OAI
noncomputable section
open scoped TensorProduct
open TensorProduct
namespace LittleFinitistic.DirectedBound
universe u v
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] {n : ℕ}

/-- The displayed algebraic hypotheses of Section 3, Lemma directed-bound.
The field and algebra are unital; zero idempotents are allowed by the source. -/
structure DirectedSystem (k A : Type u) [Field k] [Ring A] [Algebra k A] (n : ℕ) where
  e : Fin n → A
  idem : ∀ i, e i * e i = e i
  orthogonal : ∀ i j, i ≠ j → e i * e j = 0
  complete : ∑ i, e i = 1
  diagonal : ∀ i a, ∃ c : k, e i * a * e i = c • e i
  directed : ∀ i j, j < i → ∀ a, e j * a * e i = 0

namespace DirectedSystem
variable (D : DirectedSystem k A n)
variable (M : Type v) [AddCommGroup M] [Module A M] [Module k M]
  [IsScalarTower k A M]

/-- Vanishing of vertex components below p, for arbitrary modules. -/
def Supported (p : ℕ) : Prop := ∀ j : Fin n, j.val < p → ∀ m : M, D.e j • m = 0

/-- Evaluation of the free induced module. -/
def evaluation (_D : DirectedSystem k A n) : A ⊗[k] M →ₗ[A] M := AlgebraTensorModule.lift
  { toFun := fun a =>
      { toFun := fun m => a • m
        map_add' := smul_add a
        map_smul' := fun c m => smul_comm a c m }
    map_add' := fun a b => by ext m; exact add_smul a b m
    map_smul' := fun a b => by ext m; exact mul_smul a b m }

@[simp] theorem evaluation_tmul (a : A) (m : M) :
    evaluation M D (a ⊗ₜ[k] m) = a • m := rfl

/-- One summand of the separable diagonal projection. -/
def vertexProjection (i : Fin n) : A ⊗[k] M →ₗ[A] A ⊗[k] M :=
  AlgebraTensorModule.lift
    { toFun := fun a =>
        { toFun := fun m => (a * D.e i) ⊗ₜ[k] (D.e i • m)
          map_add' := fun x y => by simp [smul_add, tmul_add]
          map_smul' := fun c m => by
            simp only [RingHom.id_apply, smul_comm (D.e i) c, tmul_smul] }
      map_add' := fun a b => by ext m; simp [add_mul, add_tmul]
      map_smul' := fun a b => by
        ext m
        change ((a * b) * D.e i) ⊗ₜ[k] (D.e i • m) =
          a • ((b * D.e i) ⊗ₜ[k] (D.e i • m))
        rw [smul_tmul', smul_eq_mul, mul_assoc] }

@[simp] theorem vertexProjection_tmul (i : Fin n) (a : A) (m : M) :
    D.vertexProjection M i (a ⊗ₜ[k] m) = (a * D.e i) ⊗ₜ[k] (D.e i • m) := rfl

def projection : A ⊗[k] M →ₗ[A] A ⊗[k] M := ∑ i, D.vertexProjection M i

@[simp] theorem projection_tmul (a : A) (m : M) :
    D.projection M (a ⊗ₜ[k] m) = ∑ i, (a * D.e i) ⊗ₜ[k] (D.e i • m) := by
  simp [projection]


lemma projection_vertexTensor (i : Fin n) (a : A) (m : M) :
    D.projection M ((a * D.e i) ⊗ₜ[k] (D.e i • m)) =
      (a * D.e i) ⊗ₜ[k] (D.e i • m) := by
  rw [projection_tmul, Finset.sum_eq_single i]
  · simp only [mul_assoc, D.idem, ← mul_smul]
  · intro j _ hji
    rw [mul_assoc, D.orthogonal i j hji.symm, mul_zero, zero_tmul]
  · simp

lemma projection_idempotent (x : A ⊗[k] M) :
    D.projection M (D.projection M x) = D.projection M x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    rw [projection_tmul, map_sum]
    simp only [projection_vertexTensor]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma evaluation_projection (x : A ⊗[k] M) :
    evaluation M D (D.projection M x) = evaluation M D x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    simp only [projection_tmul, map_sum, evaluation_tmul, ← mul_smul, mul_assoc, D.idem]
    rw [← Finset.sum_smul, ← Finset.mul_sum, D.complete, mul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The manuscript's projective cover, realized as an actual direct summand. -/
abbrev Cover := LinearMap.range (D.projection M)

instance cover_addCommGroup : AddCommGroup (D.Cover M) :=
  Submodule.addCommGroup _

instance cover_projective : Module.Projective A (D.Cover M) := by
  apply Module.Projective.of_split (D.projection M).range.subtype
    (D.projection M).rangeRestrict
  ext x
  obtain ⟨t, ht⟩ := x.property
  change D.projection M x.val = x.val
  rw [← ht, projection_idempotent]

/-- Evaluation restricted to the projective summand. -/
abbrev coverMap : D.Cover M →ₗ[A] M :=
  (evaluation M D).comp (D.projection M).range.subtype

lemma coverMap_surjective : Function.Surjective (D.coverMap M) := by
  intro m
  refine ⟨(D.projection M).rangeRestrict (1 ⊗ₜ[k] m), ?_⟩
  change evaluation M D (D.projection M (1 ⊗ₜ[k] m)) = m
  rw [evaluation_projection, evaluation_tmul, one_smul]

lemma low_tensor {p : ℕ} (hM : D.Supported M p) (j : Fin n) (hj : j.val ≤ p)
    (i : Fin n) (a : A) (m : M) :
    (D.e j * a * D.e i) ⊗ₜ[k] (D.e i • m) =
      D.e j ⊗ₜ[k] ((D.e j * a * D.e i) • (D.e i • m)) := by
  by_cases hij : i = j
  · subst i
    obtain ⟨c, hc⟩ := D.diagonal j a
    rw [hc, smul_tmul, smul_assoc, ← mul_smul, D.idem, tmul_smul]
  · rcases lt_or_gt_of_ne hij with hij | hij
    · have hz := hM i (by omega) m
      simp [hz]
    · rw [D.directed i j hij a]
      simp

lemma low_projection {p : ℕ} (hM : D.Supported M p) (j : Fin n) (hj : j.val ≤ p)
    (x : A ⊗[k] M) :
    D.e j • D.projection M x =
      D.e j ⊗ₜ[k] evaluation M D (D.e j • D.projection M x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    simp only [projection_tmul, Finset.smul_sum, smul_tmul', smul_eq_mul, map_sum,
      evaluation_tmul, tmul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [← mul_assoc] using D.low_tensor M hM j hj i a m
  | add x y hx hy =>
    simp only [map_add, smul_add, tmul_add]
    exact congrArg₂ (· + ·) hx hy

/-- One syzygy raises the lower bound on the support by one. -/
lemma kernel_supported {p : ℕ} (hM : D.Supported M p) :
    D.Supported (LinearMap.ker (D.coverMap M)) (p + 1) := by
  intro j hj x
  apply Subtype.ext
  apply Subtype.ext
  change D.e j • x.val.val = 0
  obtain ⟨t, ht⟩ := x.val.property
  have h := D.low_projection M hM j (by omega) t
  rw [ht] at h
  rw [h, map_smul]
  have hz : evaluation M D x.val.val = 0 := x.property
  rw [hz, smul_zero, tmul_zero]

open CategoryTheory

omit [Module k M] [IsScalarTower k A M] in
lemma supported_subsingleton (hM : D.Supported M n) : Subsingleton M := by
  have hz (m : M) : m = 0 := by
    calc
      m = (1 : A) • m := (one_smul A m).symm
      _ = (∑ i, D.e i) • m := by rw [D.complete]
      _ = ∑ i, D.e i • m := Finset.sum_smul
      _ = 0 := Finset.sum_eq_zero (fun i _ => hM i i.isLt m)
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- The support induction uses genuine projective dimensions (vanishing Ext),
via mathlib's short exact sequence dimension-shifting theorem. -/
theorem supported_projectiveDimensionLT (r : ℕ) :
    ∀ (p : ℕ), p + r = n → ∀ (N : Type (max u v))
      [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N],
      D.Supported N p → HasProjectiveDimensionLT (ModuleCat.of A N) r := by
  induction r with
  | zero =>
    intro p hp N _ _ _ _ hN
    have hp' : p = n := by omega
    subst p
    have := D.supported_subsingleton N hN
    exact (ModuleCat.isZero_iff_subsingleton.mpr inferInstance).hasProjectiveDimensionLT_zero
  | succ r ih =>
    intro p hp N _ _ _ _ hN
    have hK := ih (p + 1) (by omega) (LinearMap.ker (D.coverMap N))
      (D.kernel_supported N hN)
    have hP : HasProjectiveDimensionLT (ModuleCat.of A (D.Cover N)) (r + 1) :=
      hasProjectiveDimensionLT_of_ge _ 1 (r + 1) (by omega)
    exact (LinearMap.shortExact_shortComplexKer (D.coverMap_surjective N)).hasProjectiveDimensionLT_X₃ r hK hP

include D

/-- Every left module is covered, with no finite generation restriction. -/
theorem all_modules_projectiveDimensionLT (N : ModuleCat.{max u v} A) :
    HasProjectiveDimensionLT N n := by
  let : Module k N := Module.compHom N (algebraMap k A)
  let : IsScalarTower k A N := IsScalarTower.of_compHom k A N
  exact D.supported_projectiveDimensionLT n 0 (by omega) N (by
    intro j hj
    omega)

theorem all_modules_projectiveDimension_le (N : ModuleCat.{max u v} A) :
    projectiveDimension N ≤ (n - 1 : ℕ) := by
  have := D.all_modules_projectiveDimensionLT N
  apply (projectiveDimension_le_iff N (n - 1)).mpr
  exact hasProjectiveDimensionLT_of_ge N n ((n - 1) + 1) (by omega)

/-- Reversing the vertices transfers exactly the hypotheses to right modules. -/
def opposite : DirectedSystem k Aᵐᵒᵖ n where
  e i := MulOpposite.op (D.e i.rev)
  idem i := by
    apply MulOpposite.unop_injective
    exact D.idem i.rev
  orthogonal i j hij := by
    apply MulOpposite.unop_injective
    exact D.orthogonal j.rev i.rev (fun h => hij (Fin.rev_injective h.symm))
  complete := by
    apply MulOpposite.unop_injective
    change (MulOpposite.opAddEquiv.symm : Aᵐᵒᵖ ≃+ A)
      (∑ i : Fin n, MulOpposite.op (D.e i.rev)) = 1
    rw [map_sum]
    change (∑ i : Fin n, D.e i.rev) = 1
    calc
      ∑ i : Fin n, D.e i.rev = ∑ i, D.e i := Equiv.sum_comp Fin.revPerm D.e
      _ = 1 := D.complete
  diagonal i a := by
    obtain ⟨c, hc⟩ := D.diagonal i.rev a.unop
    refine ⟨c, ?_⟩
    apply MulOpposite.unop_injective
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul,
      mul_assoc] using hc
  directed i j hij a := by
    apply MulOpposite.unop_injective
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_zero,
      mul_assoc] using D.directed j.rev i.rev (Fin.rev_lt_rev.mpr hij) a.unop

/-- Both sides, quantified over arbitrary modules in any larger universe. -/
theorem both_sides_projectiveDimension_le :
    (∀ N : ModuleCat.{max u v} A, projectiveDimension N ≤ (n - 1 : ℕ)) ∧
    (∀ N : ModuleCat.{max u v} Aᵐᵒᵖ, projectiveDimension N ≤ (n - 1 : ℕ)) :=
  ⟨D.all_modules_projectiveDimension_le, D.opposite.all_modules_projectiveDimension_le⟩

/-- The global dimensions are the suprema of the actual module projective dimensions. -/
theorem both_sides_globalDimension_le :
    (⨆ N : ModuleCat.{max u v} A, projectiveDimension N) ≤ (n - 1 : ℕ) ∧
    (⨆ N : ModuleCat.{max u v} Aᵐᵒᵖ, projectiveDimension N) ≤ (n - 1 : ℕ) :=
  ⟨iSup_le D.all_modules_projectiveDimension_le,
   iSup_le D.opposite.all_modules_projectiveDimension_le⟩
end DirectedSystem

open CategoryTheory
/-- Section 3, Lemma directed-bound, with its displayed hypotheses expanded.
Finite dimensionality is retained here although the proof proves a stronger result. -/
theorem directed_bound [FiniteDimensional k A] (e : Fin n → A)
    (idem : ∀ i, e i * e i = e i)
    (orthogonal : ∀ i j, i ≠ j → e i * e j = 0)
    (complete : ∑ i, e i = 1)
    (diagonal : ∀ i a, ∃ c : k, e i * a * e i = c • e i)
    (directed : ∀ i j, j < i → ∀ a, e j * a * e i = 0) :
    (⨆ N : ModuleCat.{max u v} A, projectiveDimension N) ≤ (n - 1 : ℕ) ∧
    (⨆ N : ModuleCat.{max u v} Aᵐᵒᵖ, projectiveDimension N) ≤ (n - 1 : ℕ) :=
  (DirectedSystem.mk e idem orthogonal complete diagonal directed).both_sides_globalDimension_le
end LittleFinitistic.DirectedBound

end

end OAI
