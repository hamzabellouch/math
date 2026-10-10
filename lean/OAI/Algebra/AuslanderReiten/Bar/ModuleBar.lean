import OAI.Algebra.AuslanderReiten.Bar.BarResolution
import Mathlib.RingTheory.TensorProduct.Finite

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

abbrev object : ℕ → ModuleCat.{u} k
  | 0 => ModuleCat.of k M
  | n + 1 => ModuleCat.of k (R ⊗[k] object n)

def left : (n : ℕ) → R →ₐ[k] Module.End k (object k R M n)
  | 0 => Algebra.lsmul k k M
  | n + 1 => (Module.End.rTensorAlgHom k R (object k R M n)).comp (Algebra.lsmul k k R)

@[simp] theorem left_zero (a : R) (x : M) : left k R M 0 a x = a • x := rfl
@[simp] theorem left_tmul (n : ℕ) (a b : R) (x : object k R M n) :
    left k R M (n + 1) a (b ⊗ₜ[k] x) = (a * b) ⊗ₜ[k] x := rfl

@[simp] theorem left_one (n : ℕ) (x : object k R M n) : left k R M n 1 x = x := by
  rw [map_one]
  rfl

theorem left_mul (n : ℕ) (a b : R) (x : object k R M n) :
    left k R M n (a * b) x = left k R M n a (left k R M n b x) := by
  rw [map_mul]
  rfl

def boundary : (n : ℕ) → object k R M (n + 1) →ₗ[k] object k R M n
  | 0 => TensorProduct.lift (Algebra.lsmul k k M).toLinearMap
  | n + 1 => TensorProduct.lift (left k R M (n + 1)).toLinearMap + (boundary n).lTensor R

@[simp] theorem boundary_zero_tmul (a : R) (x : M) :
    boundary k R M 0 (a ⊗ₜ[k] x) = a • x := rfl
@[simp] theorem boundary_succ_tmul (n : ℕ) (a : R) (x : object k R M (n + 1)) :
    boundary k R M (n + 1) (a ⊗ₜ[k] x) =
      left k R M (n + 1) a x + a ⊗ₜ[k] boundary k R M n x := rfl

theorem boundary_left (n : ℕ) (a : R) (x : object k R M (n + 1)) :
    boundary k R M n (left k R M (n + 1) a x) =
      left k R M n a (boundary k R M n x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b x =>
    cases n with
    | zero => exact mul_smul _ _ _
    | succ n =>
      rw [left_tmul, boundary_succ_tmul, boundary_succ_tmul, map_add, left_tmul, ← left_mul]

@[instance_reducible] def leftModule (n : ℕ) : Module R (object k R M n) :=
  Module.compHom (object k R M n) (left k R M n).toRingHom

def moduleObject (n : ℕ) : ModuleCat.{u} R :=
  letI := leftModule k R M n
  ModuleCat.of R (object k R M n)

instance baseModule (n : ℕ) : Module k (moduleObject k R M n) := (object k R M n).isModule
instance moduleTower (n : ℕ) : IsScalarTower k R (moduleObject k R M n) :=
  IsScalarTower.of_algebraMap_smul (A := R) fun a x => by
    change left k R M n (algebraMap k R a) x = a • x
    rw [AlgHom.commutes]
    rfl

def differential (n : ℕ) : moduleObject k R M (n + 1) →ₗ[R] moduleObject k R M n where
  toAddHom := (boundary k R M n).toAddHom
  map_smul' a x := boundary_left k R M n a x

theorem free (n : ℕ) : Module.Free R (moduleObject k R M (n + 1)) := by
  change @Module.Free R (R ⊗[k] object k R M n) _ _ (leftModule k R M (n + 1))
  have hm : leftModule k R M (n + 1) =
      (inferInstance : Module R (R ⊗[k] object k R M n)) := by
    apply Module.ext'
    intro a x
    change left k R M (n + 1) a x = a • x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
    | tmul b x => rfl
  rw [hm]
  infer_instance

omit [Module R M] [IsScalarTower k R M] in
theorem finiteBase [Module.Finite k R] [Module.Finite k M] (n : ℕ) :
    Module.Finite k (object k R M n) := by
  induction n with
  | zero => infer_instance
  | succ n ih =>
    let := ih
    change Module.Finite k (R ⊗[k] object k R M n)
    infer_instance

theorem finite [Module.Finite k R] [Module.Finite k M] (n : ℕ) :
    Module.Finite R (moduleObject k R M (n + 1)) := by
  let : Module.Finite k (moduleObject k R M (n + 1)) := finiteBase k R M (n + 1)
  exact Module.Finite.of_restrictScalars_finite k R _

variable [CharP k 2]

private theorem double_zero {V : Type u} [AddCommGroup V] [Module k V] (x : V) : x + x = 0 := by
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  rw [← two_smul k x, htwo, zero_smul]

theorem boundary_squared (n : ℕ) (x : object k R M (n + 2)) :
    boundary k R M n (boundary k R M (n + 1) x) = 0 := by
  induction n with
  | zero =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
    | tmul a x =>
      rw [boundary_succ_tmul, map_add, boundary_left, boundary_zero_tmul, left_zero]
      exact double_zero k _
  | succ n ih =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
    | tmul a x =>
      rw [boundary_succ_tmul, map_add, boundary_left, boundary_succ_tmul, ih,
        TensorProduct.tmul_zero, add_zero]
      exact double_zero k _

def contraction (n : ℕ) : object k R M n →ₗ[k] object k R M (n + 1) :=
  TensorProduct.mk k R (object k R M n) 1

theorem contraction_identity (n : ℕ) (x : object k R M (n + 1)) :
    boundary k R M (n + 1) (contraction k R M (n + 1) x) +
      contraction k R M n (boundary k R M n x) = x := by
  change boundary k R M (n + 1) ((1 : R) ⊗ₜ[k] x) +
    (1 : R) ⊗ₜ[k] boundary k R M n x = x
  rw [boundary_succ_tmul, left_one, add_assoc, double_zero k, add_zero]

omit [CharP k 2] in
theorem augmentation_contraction (x : M) : boundary k R M 0 (contraction k R M 0 x) = x :=
  one_smul R x

theorem differential_exact (n : ℕ) :
    LinearMap.range (differential k R M (n + 1)) = LinearMap.ker (differential k R M n) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact boundary_squared k R M n x
  · intro x hx
    refine ⟨contraction k R M (n + 1) x, ?_⟩
    have h := contraction_identity k R M n x
    change boundary k R M n x = 0 at hx
    rw [hx, map_zero, add_zero] at h
    exact h

def complex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun n => moduleObject k R M (n + 1))
    (fun n => ModuleCat.ofHom (X := moduleObject k R M (n + 2))
      (Y := moduleObject k R M (n + 1)) (differential k R M (n + 1)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact boundary_squared k R M (n + 1))

@[simp] theorem complex_d (n : ℕ) : (complex k R M).d (n + 1) n =
    ModuleCat.ofHom (X := moduleObject k R M (n + 2))
      (Y := moduleObject k R M (n + 1)) (differential k R M (n + 1)) := by
  simp only [complex, ChainComplex.of.d]
  apply Category.id_comp

def augmentation : complex k R M ⟶
    (ChainComplex.single₀ (ModuleCat.{u} R)).obj (moduleObject k R M 0) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (X := moduleObject k R M 1) (Y := moduleObject k R M 0)
      (differential k R M 0), by
      rw [complex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact boundary_squared k R M 0⟩

@[simp] theorem augmentation_zero : (augmentation k R M).f 0 =
    ModuleCat.ofHom (X := moduleObject k R M 1) (Y := moduleObject k R M 0)
      (differential k R M 0) := ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

theorem complex_exactAt (n : ℕ) : (complex k R M).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range ((complex k R M).d (n + 1 + 1) (n + 1)).hom =
    LinearMap.ker ((complex k R M).d (n + 1) n).hom
  rw [complex_d, complex_d]
  exact differential_exact k R M (n + 1)

def resolution : ProjectiveResolution (moduleObject k R M 0) where
  complex := complex k R M
  projective n := by
    let := free k R M n
    let : Module.Projective R (moduleObject k R M (n + 1)) := Module.Projective.of_free
    exact (moduleObject k R M (n + 1)).projective_of_categoryTheory_projective
  π := augmentation k R M
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · constructor
        · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
          change LinearMap.range ((complex k R M).d 1 0).hom =
            LinearMap.ker ((augmentation k R M).f 0).hom
          rw [complex_d, augmentation_zero]
          exact differential_exact k R M 0
        · rw [ModuleCat.epi_iff_surjective]
          intro x
          exact ⟨contraction k R M 0 x, augmentation_contraction k R M x⟩
      · exact (complex k R M).shape 0 0 (by simp)
      · rfl
      · rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact complex_exactAt k R M n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

end ArExplicit.ModuleBar

end

end OAI
