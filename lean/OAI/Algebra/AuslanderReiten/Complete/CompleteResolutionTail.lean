import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit
universe u
variable {R : Type u} [Ring R]

def nonnegativeTail (P : ChainComplex (ModuleCat.{u} R) ℤ) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun n => P.X (n : ℤ))
    (fun n => P.d ((n + 1 : ℕ) : ℤ) (n : ℤ))
    (fun _n => P.d_comp_d _ _ _)

@[simp]
theorem nonnegativeTail_d (P : ChainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    (nonnegativeTail P).d (n + 1) n = P.d ((n + 1 : ℕ) : ℤ) (n : ℤ) := by
  simp [nonnegativeTail]

abbrev CompleteCokernel (P : ChainComplex (ModuleCat.{u} R) ℤ) :=
  P.X 0 ⧸ LinearMap.range (P.d 1 0).hom

def nonnegativeTailAugmentation (P : ChainComplex (ModuleCat.{u} R) ℤ) :
    nonnegativeTail P ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj
      (ModuleCat.of R (CompleteCokernel P)) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (LinearMap.range (P.d 1 0).hom).mkQ, by
      rw [nonnegativeTail_d]
      apply ModuleCat.hom_ext
      exact LinearMap.range_mkQ_comp _⟩

@[simp]
theorem nonnegativeTailAugmentation_f_zero (P : ChainComplex (ModuleCat.{u} R) ℤ) :
    (nonnegativeTailAugmentation P).f 0 =
      ModuleCat.ofHom (LinearMap.range (P.d 1 0).hom).mkQ := by
  apply ChainComplex.toSingle₀Equiv_symm_apply_f_zero

theorem nonnegativeTail_exactAt (P : ChainComplex (ModuleCat.{u} R) ℤ)
    (hex : ∀ n : ℤ, LinearMap.range (P.d (n + 1) n).hom =
      LinearMap.ker (P.d n (n - 1)).hom) (n : ℕ) :
    (nonnegativeTail P).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range ((nonnegativeTail P).d (n + 1 + 1) (n + 1)).hom =
    LinearMap.ker ((nonnegativeTail P).d (n + 1) n).hom
  rw [nonnegativeTail_d, nonnegativeTail_d]
  have aux (i j l : ℤ) (hi : i = j + 1) (hl : l = j - 1) :
      LinearMap.range (P.d i j).hom = LinearMap.ker (P.d j l).hom := by
    subst i
    subst l
    exact hex j
  exact aux _ _ _ (by omega) (by omega)

def completeCokernelResolution (P : ChainComplex (ModuleCat.{u} R) ℤ)
    (hproj : ∀ n : ℤ, Module.Projective R (P.X n))
    (hex : ∀ n : ℤ, LinearMap.range (P.d (n + 1) n).hom =
      LinearMap.ker (P.d n (n - 1)).hom) :
    ProjectiveResolution (ModuleCat.of R (CompleteCokernel P)) where
  complex := nonnegativeTail P
  projective n := by
    let := hproj (n : ℤ)
    exact (P.X (n : ℤ)).projective_of_categoryTheory_projective
  π := nonnegativeTailAugmentation P
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · constructor
        · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
          change LinearMap.range ((nonnegativeTail P).d 1 0).hom =
            LinearMap.ker ((nonnegativeTailAugmentation P).f 0).hom
          rw [nonnegativeTail_d, nonnegativeTailAugmentation_f_zero]
          exact (Submodule.ker_mkQ _).symm
        · rw [ModuleCat.epi_iff_surjective]
          change Function.Surjective (LinearMap.range (P.d 1 0).hom).mkQ
          exact Submodule.mkQ_surjective _
      · change (nonnegativeTail P).d 0 0 = 0
        exact (nonnegativeTail P).shape _ _ (by simp)
      · rfl
      · rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact nonnegativeTail_exactAt P hex n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

def transportProjectiveResolution {X Y : ModuleCat.{u} R}
    (Q : ProjectiveResolution X) (e : X ≅ Y) : ProjectiveResolution Y where
  complex := Q.complex
  projective := Q.projective
  π := Q.π ≫ (ChainComplex.single₀ (ModuleCat.{u} R)).map e.hom

end ArExplicit

end

end OAI
