import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

namespace OAI

noncomputable section
universe w v u

namespace PiExponentSiegelAux.W31
open Module
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open HomologicalComplex

section General
variable {C : Type u} [Category.{v} C] [Abelian C]

def projectiveResolutionOfExact (P : ChainComplex C ℕ) (M : C)
    (ε : P.X 0 ⟶ M) (hε : P.d 1 0 ≫ ε = 0)
    (hzero : (ShortComplex.mk (P.d 1 0) ε hε).Exact)
    (hepi : Epi ε) (hexact : ∀ n : ℕ, P.ExactAt (n + 1))
    (hproj : ∀ n : ℕ, CategoryTheory.Projective (P.X n)) :
    CategoryTheory.ProjectiveResolution M where
  complex := P
  projective := hproj
  π := (ChainComplex.toSingle₀Equiv P M).symm ⟨ε, hε⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_of_zeros' _ (by simp; rfl) (by simp; rfl)
          (by simp; rfl)]
      simpa [ChainComplex.toSingle₀Equiv] using! And.intro hzero hepi
    | succ n =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
      exact hexact n⟩

theorem projectiveResolutionOfExact_complex (P : ChainComplex C ℕ) (M : C)
    (ε : P.X 0 ⟶ M) (hε : P.d 1 0 ≫ ε = 0)
    (hzero : (ShortComplex.mk (P.d 1 0) ε hε).Exact)
    (hepi : Epi ε) (hexact : ∀ n : ℕ, P.ExactAt (n + 1))
    (hproj : ∀ n : ℕ, CategoryTheory.Projective (P.X n)) :
    (projectiveResolutionOfExact P M ε hε hzero hepi hexact hproj).complex = P := rfl

variable [HasExt.{w} C]

def resolutionExtAddEquiv (M Y : C) (P : ProjectiveResolution M) (n : ℕ) :
    Ext M Y n ≃+
      CochainComplex.HomComplex.CohomologyClass P.cochainComplex
        ((CochainComplex.singleFunctor C 0).obj Y) n :=
  P.extAddEquivCohomologyClass

theorem ext_subsingleton_iff_cocycles_are_boundaries
    (M Y : C) (P : ProjectiveResolution M) (n : ℕ) :
    Subsingleton (Ext M Y (n + 1)) ↔
      ∀ (f : P.complex.X (n + 1) ⟶ Y),
        P.complex.d (n + 2) (n + 1) ≫ f = 0 →
        ∃ g : P.complex.X n ⟶ Y, P.complex.d (n + 1) n ≫ g = f := by
  constructor
  · intro h f hf
    exact (P.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mp
      (h.elim _ 0)
  · intro h
    apply subsingleton_of_forall_eq 0
    intro e
    obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (n + 2) rfl
    exact (P.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mpr (h f hf)

theorem ext_subsingleton_of_isZero_resolution_term
    (M Y : C) (P : ProjectiveResolution M) (n : ℕ)
    (hterm : IsZero (P.complex.X n)) : Subsingleton (Ext M Y n) := by
  apply subsingleton_of_forall_eq 0
  intro e
  obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (n + 1) rfl
  have hfzero : f = 0 := hterm.eq_of_src f 0
  subst f
  exact P.extMk_zero (n + 1) rfl

end General

variable {R : Type u} [CommRing R]

theorem module_exactAt_succ_of_range_eq_ker (P : ChainComplex (ModuleCat.{u} R) ℕ)
    (n : ℕ)
    (h : LinearMap.range (P.d (n + 2) (n + 1)).hom =
      LinearMap.ker (P.d (n + 1) n).hom) : P.ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact h

def finiteFreeResolutionOfExact (P : ChainComplex (ModuleCat.{u} R) ℕ)
    (M : ModuleCat.{u} R) (ε : P.X 0 ⟶ M) (hε : P.d 1 0 ≫ ε = 0)
    (hzero : LinearMap.range (P.d 1 0).hom = LinearMap.ker ε.hom)
    (hepi : Function.Surjective ε.hom)
    (hexact : ∀ n : ℕ, LinearMap.range (P.d (n + 2) (n + 1)).hom =
      LinearMap.ker (P.d (n + 1) n).hom)
    (rank : ℕ → ℕ) (basis : ∀ n : ℕ, Basis (Fin (rank n)) R (P.X n)) :
    ProjectiveResolution M :=
  projectiveResolutionOfExact P M ε hε
    ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr hzero)
    ((ModuleCat.epi_iff_surjective ε).mpr hepi)
    (fun n => module_exactAt_succ_of_range_eq_ker P n (hexact n))
    (fun n => ModuleCat.projective_of_free (basis n))

def moduleFreeResolutionOfExact (P : ChainComplex (ModuleCat.{u} R) ℕ)
    (M : ModuleCat.{u} R) (ε : P.X 0 ⟶ M) (hε : P.d 1 0 ≫ ε = 0)
    (hzero : LinearMap.range (P.d 1 0).hom = LinearMap.ker ε.hom)
    (hepi : Function.Surjective ε.hom)
    (hexact : ∀ n : ℕ, LinearMap.range (P.d (n + 2) (n + 1)).hom =
      LinearMap.ker (P.d (n + 1) n).hom)
    (hfree : ∀ n : ℕ, Module.Free R (P.X n)) : ProjectiveResolution M :=
  projectiveResolutionOfExact P M ε hε
    ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr hzero)
    ((ModuleCat.epi_iff_surjective ε).mpr hepi)
    (fun n => module_exactAt_succ_of_range_eq_ker P n (hexact n))
    (fun n => by
      let := hfree n
      exact ModuleCat.projective_of_free (Module.Free.chooseBasis R (P.X n)))

end PiExponentSiegelAux.W31

end

end OAI
