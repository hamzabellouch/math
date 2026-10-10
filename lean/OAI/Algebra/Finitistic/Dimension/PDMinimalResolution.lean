import OAI.Algebra.Finitistic.Dimension.PDMinimalData
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

namespace OAI
noncomputable section
namespace LittleFinitistic.PDMinimal
open CategoryTheory CategoryTheory.Limits
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (M : FiniteModule k A)

/-- The actual chain complex of the successive projective covers. -/
def complex : ChainComplex (ModuleCat A) ℕ := ChainComplex.of
  (fun n => (term M n).cat)
  (fun n => ModuleCat.ofHom (differential M n))
  (fun n => ModuleCat.hom_ext (differential_comp M n))

@[simp] theorem complex_d (n : ℕ) :
    (complex M).d (n+1) n = ModuleCat.ofHom (differential M n) := by
  exact ChainComplex.of_d (fun n => (term M n).cat)
    (fun n => ModuleCat.ofHom (differential M n)) n

instance term_projective (n : ℕ) : Projective ((complex M).X n) := by
  exact (IsProjective.iff_projective _).mp (cover (syzygy M n)).projective

lemma complex_exactAt (n : ℕ) : (complex M).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  change LinearMap.range ((complex M).d (n+2) (n+1)).hom =
    LinearMap.ker ((complex M).d (n+1) n).hom
  rw [complex_d, complex_d]
  exact exact_differential M n

lemma complex_d_augment : (complex M).d 1 0 ≫ ModuleCat.ofHom (augment M 0) = 0 := by
  rw [complex_d]
  exact ModuleCat.hom_ext (augment_differential M 0)

lemma complex_exact_augment :
    (ShortComplex.mk _ _ (complex_d_augment M)).Exact := by
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  change LinearMap.range ((complex M).d 1 0).hom = LinearMap.ker (augment M 0)
  rw [complex_d]
  exact range_differential M 0

instance augment_epi : Epi (ModuleCat.ofHom (augment M 0)) :=
  (ModuleCat.epi_iff_surjective _).mpr (cover _).surjective

/-- A projective resolution, including its augmentation quasi-isomorphism. -/
def resolution : ProjectiveResolution M.cat where
  complex := complex M
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨ModuleCat.ofHom (augment M 0),
    complex_d_augment M⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      ·
        refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨complex_exact_augment M, augment_epi M⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by erw [Category.id_comp])
          (by erw [Category.id_comp])
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact complex_exactAt M n
      · apply ChainComplex.exactAt_succ_single_obj⟩
end LittleFinitistic.PDMinimal

end

end OAI
