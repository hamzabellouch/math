import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteTraceLinearGroup
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SimpleAlgebraAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialMatrixStabilizer

namespace OAI

/-! # An irreducible matrix group with finitely many traces is finite -/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

variable {K G : Type*} [Field K] [IsAlgClosed K] [Group G] {n : ℕ}

theorem irreducible_entries_span_eq_top (ι : G →* PolynomialMatrixGroup K n)
    [Representation.IsIrreducible (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (linearAction.toMonoidHom.comp ι))] :
    Submodule.span K (Set.range (fun g => entries (ι g))) = ⊤ := by
  let R : Representation K G (Fin n → K) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (linearAction.toMonoidHom.comp ι)
  let e := Matrix.toLinAlgEquiv' (R := K) (n := Fin n)
  have he (g : G) : e.symm (R g) = entries (ι g) := by
    apply e.injective
    rw [e.apply_symm_apply]
    rfl
  have himage : e.symm '' Set.range R = Set.range (fun g => entries (ι g)) := by
    ext B
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, (he g).symm⟩
    · rintro ⟨g, rfl⟩
      exact ⟨R g, Set.mem_range_self g, he g⟩
  calc
    Submodule.span K (Set.range (fun g => entries (ι g))) =
        (Submodule.span K (Set.range R)).map e.symm.toLinearMap := by
      rw [Submodule.map_span]
      exact congrArg (Submodule.span K) himage.symm
    _ = (⊤ : Submodule K (Module.End K (Fin n → K))).map e.symm.toLinearMap := by
      rw [irreducible_linear_span_eq_top R]
    _ = ⊤ := by
      rw [Submodule.map_top]
      exact LinearMap.range_eq_top.mpr e.symm.surjective

theorem finite_of_irreducible_finite_trace (ι : G →* PolynomialMatrixGroup K n)
    (hι : Function.Injective ι)
    [Representation.IsIrreducible (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (linearAction.toMonoidHom.comp ι))]
    (htrace : (Set.range (fun g => Matrix.trace (entries (ι g)))).Finite) : Finite G := by
  exact finite_matrix_group_of_full_span_finite_trace (mulEquivGL.toMonoidHom.comp ι)
    (mulEquivGL.injective.comp hι) (irreducible_entries_span_eq_top ι) htrace

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
