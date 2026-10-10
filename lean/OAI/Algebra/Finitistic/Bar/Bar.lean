import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

namespace OAI

open scoped TensorProduct
open TensorProduct
noncomputable section
namespace DerivedBar
universe u
variable (k A N : Type u) [Field k] [Ring A] [Algebra k A]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- The augmented bar terms: term 0 is N; term (n+1) is A ⊗ term n. -/
@[reducible] def term : ℕ → ModuleCat k
  | 0 => ModuleCat.of k N
  | n+1 => ModuleCat.of k (A ⊗[k] term n)

@[reducible] instance termModule : (n : ℕ) → Module A (term k A N n)
  | 0 => inferInstanceAs (Module A N)
  | n+1 => inferInstanceAs (Module A (A ⊗[k] term k A N n))

instance termTower : (n : ℕ) → IsScalarTower k A (term k A N n)
  | 0 => inferInstanceAs (IsScalarTower k A N)
  | n+1 => inferInstanceAs (IsScalarTower k A (A ⊗[k] term k A N n))


/-- Multiplication/action on the first two positions of an augmented bar word. -/
def action (M : Type u) [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] : A ⊗[k] M →ₗ[A] M :=
  { (TensorProduct.lift (Algebra.lsmul k k M).toLinearMap).toAddHom with
    map_smul' := by
      intro a z
      induction z using TensorProduct.inductionOn with
      | tmul b m => simp [TensorProduct.smul_tmul']
      | add x y hx hy => simp_all [smul_add] }

@[simp] theorem action_tmul (M : Type u) [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] (a : A) (m : M) :
    action k A M (a ⊗ₜ[k] m) = a • m := rfl

/-- Recursive alternating face differential. No A-flatness of N is required. -/
def differential : (n : ℕ) → term k A N (n+1) →ₗ[A] term k A N n
  | 0 => action k A N
  | n+1 => action k A (term k A N (n+1)) -
      AlgebraTensorModule.lTensor A A ((differential n).restrictScalars k)

@[simp] theorem differential_zero_tmul (a : A) (z : N) :
    differential k A N 0 (a ⊗ₜ[k] z) = a • z := rfl

@[simp] theorem differential_succ_tmul (n : ℕ) (a : A) (z : term k A N (n+1)) :
    differential k A N (n+1) (a ⊗ₜ[k] z) =
      a • z - a ⊗ₜ[k] differential k A N n z := rfl

/-- The actual bar differential squares to zero in every degree. -/
theorem differential_sq (n : ℕ) :
    (differential k A N n).comp (differential k A N (n+1)) = 0 := by
  induction n with
  | zero =>
    apply AlgebraTensorModule.ext
    intro a z
    change differential k A N 0 (differential k A N 1 (a ⊗ₜ[k] z)) = 0
    rw [differential_succ_tmul k A N 0 a z, map_sub, map_smul,
      differential_zero_tmul k A N a (differential k A N 0 z), sub_self]
  | succ n ih =>
    apply AlgebraTensorModule.ext
    intro a z
    have hz := LinearMap.congr_fun ih z
    change differential k A N n (differential k A N (n+1) z) = 0 at hz
    change differential k A N (n+1) (differential k A N (n+2) (a ⊗ₜ[k] z)) = 0
    rw [differential_succ_tmul k A N (n+1) a z, map_sub, map_smul,
      differential_succ_tmul k A N n a (differential k A N (n+1) z), hz,
      TensorProduct.tmul_zero, sub_zero, sub_self]

/-- Unit insertion; this is k-linear, generally not A-linear. -/
def contraction (n : ℕ) : term k A N n →ₗ[k] term k A N (n+1) :=
  TensorProduct.mk k A (term k A N n) 1

omit [Module A N] [IsScalarTower k A N] in
@[simp] theorem contraction_apply (n : ℕ) (z : term k A N n) :
    contraction k A N n z = 1 ⊗ₜ[k] z := rfl

/-- The augmented degree-zero contraction identity. -/
theorem contraction_zero (z : N) :
    differential k A N 0 (contraction k A N 0 z) = z := by
  change (1 : A) • z = z
  exact one_smul A z

/-- Contracting homotopy in every positive augmented degree. -/
theorem contraction_identity (n : ℕ) (z : term k A N (n+1)) :
    differential k A N (n+1) (contraction k A N (n+1) z) +
      contraction k A N n (differential k A N n z) = z := by
  change differential k A N (n+1) (1 ⊗ₜ[k] z) + 1 ⊗ₜ[k] differential k A N n z = z
  rw [differential_succ_tmul k A N n 1 z, one_smul, sub_add_cancel]

/-- Exactness of the augmented absolute bar complex as actual A-linear maps. -/
theorem differential_exact (n : ℕ) :
    LinearMap.range (differential k A N (n+1)) =
      LinearMap.ker (differential k A N n) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact LinearMap.congr_fun (differential_sq k A N n) z
  · intro z hz
    refine ⟨contraction k A N (n+1) z, ?_⟩
    have h := contraction_identity k A N n z
    have hz' : differential k A N n z = 0 := hz
    simpa [hz'] using h

/-- The augmented chain complex, including N at homological degree zero. -/
def augmentedComplex : ChainComplex (ModuleCat A) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of A (term k A N n))
    (fun n => ModuleCat.ofHom (differential k A N n))
    (fun n => by exact ModuleCat.hom_ext (differential_sq k A N n))

/-- The unaugmented absolute bar complex, degree n = A ⊗ A^⊗n ⊗ N. -/
def complex : ChainComplex (ModuleCat A) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of A (term k A N (n+1)))
    (fun n => ModuleCat.ofHom (differential k A N (n+1)))
    (fun n => by exact ModuleCat.hom_ext (differential_sq k A N (n+1)))


open CategoryTheory CategoryTheory.Limits

/-- Every unaugmented bar term is free as a left A-module, even for noncommutative A. -/
instance term_free (n : ℕ) : Module.Free A (term k A N (n+1)) :=
  Module.Free.of_basis (Algebra.TensorProduct.basis A (Module.Free.chooseBasis k (term k A N n)))

instance complex_projective (n : ℕ) : Projective ((complex k A N).X n) := by
  change Projective (ModuleCat.of A (term k A N (n+1)))
  exact inferInstance

/-- Surjectivity of the bar augmentation, witnessed by insertion of 1. -/
theorem augmentation_surjective : Function.Surjective (differential k A N 0) := by
  intro z
  exact ⟨contraction k A N 0 z, contraction_zero k A N z⟩

/-- The bar augmentation as a chain map to N concentrated in degree zero. -/
def augmentation : complex k A N ⟶ (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A N) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (differential k A N 0), by
      change ModuleCat.ofHom (differential k A N 1) ≫
        ModuleCat.ofHom (differential k A N 0) = 0
      exact ModuleCat.hom_ext (differential_sq k A N 0)⟩

/-- All positive-degree homology of the unaugmented bar complex vanishes. -/
theorem complex_exactAt_succ (n : ℕ) : (complex k A N).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+1+1) (n+1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  simpa only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    complex, ChainComplex.of_d, ModuleCat.hom_ofHom] using! differential_exact k A N (n+1)

/-- Exactness at the augmentation term, stated in the abelian category of A-modules. -/
theorem augmentation_exact :
    (ShortComplex.mk ((complex k A N).d 1 0) (ModuleCat.ofHom (differential k A N 0))
      (ModuleCat.hom_ext (differential_sq k A N 0))).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact differential_exact k A N 0

instance augmentation_epi : Epi (ModuleCat.ofHom (differential k A N 0)) :=
  (ModuleCat.epi_iff_surjective _).mpr (augmentation_surjective k A N)

/-- The absolute algebra bar augmentation is a genuine quasi-isomorphism. -/
instance augmentation_quasiIso : QuasiIso (augmentation k A N) := by
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · dsimp [augmentation]
      exact ⟨augmentation_exact k A N, augmentation_epi k A N⟩
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · exact complex_exactAt_succ k A N n
    · apply ChainComplex.exactAt_succ_single_obj

/-- Explicit free absolute bar resolution, packaged for derived functor computations. -/
def projectiveResolution : ProjectiveResolution (ModuleCat.of A N) where
  complex := complex k A N
  π := augmentation k A N
end DerivedBar

end

end OAI
