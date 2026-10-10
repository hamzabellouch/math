import OAI.Algebra.AuslanderReiten.Cones.ConeExactness
import OAI.Algebra.AuslanderReiten.Complete.CompleteComparison
import OAI.Algebra.AuslanderReiten.Basic
import Mathlib.RingTheory.Finiteness.Prod

namespace OAI

namespace ArExplicit

open CategoryTheory

universe u

variable {R : Type u} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{u} R) ℤ}

def completeConeTerm (_f : P ⟶ Q) (n : ℤ) : ModuleCat.{u} R :=
  ModuleCat.of R (Q.X (n + 1) × P.X n)

def completeConeDifferential (f : P ⟶ Q) (n : ℤ) :
    completeConeTerm f (n + 1) ⟶ completeConeTerm f n :=
  ModuleCat.ofHom (coneBlock (Q.d ((n + 1) + 1) (n + 1)).hom
    (P.d (n + 1) n).hom (f.f (n + 1)).hom)

theorem completeConeDifferential_square (f : P ⟶ Q) (n : ℤ) :
    completeConeDifferential f (n + 1) ≫ completeConeDifferential f n = 0 := by
  apply ModuleCat.hom_ext
  apply coneBlock_comp_zero
  · exact congrArg ModuleCat.Hom.hom (Q.d_comp_d _ _ _)
  · exact congrArg ModuleCat.Hom.hom (P.d_comp_d _ _ _)
  · exact congrArg ModuleCat.Hom.hom (f.comm _ _)

def completeCone (f : P ⟶ Q) : ChainComplex (ModuleCat.{u} R) ℤ :=
  ChainComplex.of (completeConeTerm f) (completeConeDifferential f) (completeConeDifferential_square f)

theorem completeCone_adjacent_exact (f : P ⟶ Q)
    (hP : ExactProjectiveComplex P) (hQ : ExactProjectiveComplex Q) (n : ℤ) :
    LinearMap.range (completeConeDifferential f (n + 1)).hom =
      LinearMap.ker (completeConeDifferential f n).hom := by
  apply (LinearMap.exact_iff.mp _).symm
  apply coneBlock_exact
  · apply LinearMap.exact_iff.mpr
    exact (hQ.exactAt_of_indices (by omega) (by omega)).symm
  · apply LinearMap.exact_iff.mpr
    exact (hP.exactAt_of_indices (by omega) (by omega)).symm
  · exact congrArg ModuleCat.Hom.hom (f.comm _ _)

theorem completeCone_adjacent_dualExact (f : P ⟶ Q)
    (hP : TotallyAcyclicComplex P) (hQ : TotallyAcyclicComplex Q) (n : ℤ) :
    HomExactAt (completeConeDifferential f (n + 1)).hom (completeConeDifferential f n).hom := by
  apply coneBlock_homExact
  · exact hQ.dualExact_of_indices (by omega) (by omega)
  · exact hP.dualExact_of_indices (by omega) (by omega)
  · exact congrArg ModuleCat.Hom.hom (f.comm _ _)

theorem completeCone_totallyAcyclic (f : P ⟶ Q)
    (hP : TotallyAcyclicComplex P) (hQ : TotallyAcyclicComplex Q) :
    TotallyAcyclicComplex (completeCone f) where
  finite n := by
    let := hQ.finite (n + 1)
    let := hP.finite n
    exact inferInstanceAs (Module.Finite R (Q.X (n + 1) × P.X n))
  projective n := by
    let := hQ.projective (n + 1)
    let := hP.projective n
    exact inferInstanceAs (Module.Projective R (Q.X (n + 1) × P.X n))
  exactAt n := by
    have aux (i j : ℤ) (hij : i = j + 1) :
        LinearMap.range ((completeCone f).d (i + 1) i).hom =
          LinearMap.ker ((completeCone f).d i j).hom := by
      subst i
      simp only [completeCone, ChainComplex.of_d]
      exact completeCone_adjacent_exact f hP.toExactProjectiveComplex hQ.toExactProjectiveComplex j
    exact aux n (n - 1) (by omega)
  dualExact n := by
    have aux (i j : ℤ) (hij : i = j + 1) :
        HomExactAt ((completeCone f).d (i + 1) i).hom ((completeCone f).d i j).hom := by
      subst i
      simp only [completeCone, ChainComplex.of_d]
      exact completeCone_adjacent_dualExact f hP hQ j
    exact aux n (n - 1) (by omega)

theorem completeCone_cokernel_gorenstein (f : P ⟶ Q)
    (hP : TotallyAcyclicComplex P) (hQ : TotallyAcyclicComplex Q) :
    GorensteinProjective R (CompleteComparison.Cokernel (completeCone f) 0) := by
  have h := completeCone_totallyAcyclic f hP hQ
  refine ⟨completeCone f, fun n => ⟨h.finite n, h.projective n⟩, h.exactAt, ?_, ⟨LinearEquiv.refl R _⟩⟩
  intro n g hg
  obtain ⟨g', hg'⟩ := h.dualExact n g hg
  exact ⟨g', hg'.symm⟩

end ArExplicit

end OAI
