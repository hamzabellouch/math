import OAI.NumberTheory.DukePrimeDegree.Arithmetic.FullLattice
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.FreeModule.PID

namespace OAI

/-!
# Bases of full lattices

The finitely generated, rationally spanning submodules used in
`FullLattice` are free of rank equal to the field degree. Their integer
bases become rational bases without changing the underlying vectors.
-/

namespace DukePrimeDegree

variable {K : Type*} [Field K] [NumberField K]

/-- An integer basis of a full lattice is a rational basis of the field. -/
noncomputable def FullLattice.rationalBasis {ι : Type*} (M : FullLattice K)
    (b : Module.Basis ι ℤ M.toSubmodule) : Module.Basis ι ℚ K := by
  have hlin : LinearIndependent ℤ (fun i => (b i : K)) :=
    b.linearIndependent.map' M.toSubmodule.subtype (Submodule.ker_subtype _)
  have hlinQ : LinearIndependent ℚ (fun i => (b i : K)) :=
    hlin.localization ℚ (nonZeroDivisors ℤ)
  have hz : Submodule.span ℤ (Set.range fun i => (b i : K)) = M.toSubmodule := by
    rw [show (Set.range fun i => (b i : K)) =
      M.toSubmodule.subtype '' Set.range b by ext; simp]
    rw [← Submodule.map_span, b.span_eq]
    simp
  have hspan : Submodule.span ℚ (Set.range fun i => (b i : K)) = ⊤ := by
    rw [← Submodule.span_span_of_tower (R := ℤ), hz]
    exact M.span_eq_top
  exact Module.Basis.mk hlinQ hspan.ge

@[simp] lemma FullLattice.rationalBasis_apply {ι : Type*} (M : FullLattice K)
    (b : Module.Basis ι ℤ M.toSubmodule) (i : ι) :
    M.rationalBasis b i = (b i : K) := by
  simp [FullLattice.rationalBasis]

/-- The rank in the manuscript's definition follows from finite generation
and rational spanning; it is not an extra hypothesis. -/
lemma FullLattice.finrank (M : FullLattice K) :
    Module.finrank ℤ M.toSubmodule = Module.finrank ℚ K := by
  let : Module.Finite ℤ M.toSubmodule := Module.Finite.iff_fg.mpr M.fg
  let b := Module.finBasis ℤ M.toSubmodule
  simpa using (Module.finrank_eq_card_basis (M.rationalBasis b)).symm

/-- A full lattice has an integer basis indexed by the degree of the field. -/
noncomputable def FullLattice.integralBasis (M : FullLattice K) :
    Module.Basis (Fin (Module.finrank ℚ K)) ℤ M.toSubmodule := by
  let : Module.Finite ℤ M.toSubmodule := Module.Finite.iff_fg.mpr M.fg
  exact (Module.finBasis ℤ M.toSubmodule).reindex (finCongr M.finrank)

end DukePrimeDegree

end OAI
