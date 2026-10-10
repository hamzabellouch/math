import OAI.Algebra.AuslanderReiten.Bar.BarProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]

@[simp] theorem complex_d (n : ℕ) :
    (complex k R).d (n + 1) n =
      ModuleCat.ofHom (X := moduleObject k R (n + 2)) (Y := moduleObject k R (n + 1))
        (differential k R (n + 1)) := by
  simp only [complex, ChainComplex.of.d]
  apply Category.id_comp

def augmentation : complex k R ⟶
    (ChainComplex.single₀ (ModuleCat.{u} (Enveloping k R))).obj (moduleObject k R 0) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (X := moduleObject k R 1) (Y := moduleObject k R 0)
      (differential k R 0), by
      rw [complex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact boundary_squared k R 0⟩

@[simp] theorem augmentation_zero :
    (augmentation k R).f 0 = ModuleCat.ofHom (X := moduleObject k R 1)
      (Y := moduleObject k R 0) (differential k R 0) := by
  apply ChainComplex.toSingle₀Equiv_symm_apply_f_zero

theorem complex_exactAt (n : ℕ) : (complex k R).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range ((complex k R).d (n + 1 + 1) (n + 1)).hom =
    LinearMap.ker ((complex k R).d (n + 1) n).hom
  rw [complex_d, complex_d]
  exact differential_exact k R (n + 1)

def resolution : ProjectiveResolution (moduleObject k R 0) where
  complex := complex k R
  projective n := by
    let := projective k R n
    exact (moduleObject k R (n + 1)).projective_of_categoryTheory_projective
  π := augmentation k R
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · constructor
        · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
          change LinearMap.range ((complex k R).d 1 0).hom =
            LinearMap.ker ((augmentation k R).f 0).hom
          rw [complex_d, augmentation_zero]
          exact differential_exact k R 0
        · rw [ModuleCat.epi_iff_surjective]
          intro x
          exact ⟨contraction k R 0 x, augmentation_contraction k R x⟩
      · change (complex k R).d 0 0 = 0
        exact (complex k R).shape _ _ (by simp)
      · rfl
      · rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact complex_exactAt k R n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

end ArExplicit.AbsoluteBar

end

end OAI
