import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic

namespace OAI

/-! # Boundaries detected by vanishing homology classes -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {R : Type} [CommRing R]

theorem exists_boundary_of_homologyπ_eq_zero (C : ChainComplex (ModuleCat R) ℕ)
    (n : ℕ) (z : C.cycles n) (hz : C.homologyπ n z = 0) :
    ∃ w : C.X (n + 1), C.d (n + 1) n w = C.iCycles n z := by
  let S := ShortComplex.mk (C.toCycles (n + 1) n) (C.homologyπ n)
    (C.toCycles_comp_homologyπ (n + 1) n)
  have he : S.Exact := S.exact_of_g_is_cokernel
    (C.homologyIsCokernel (n + 1) n (ChainComplex.prev ℕ n))
  obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff S).mp he z hz
  refine ⟨w, ?_⟩
  have h := congrArg (fun t => C.iCycles n t) hw
  exact (congrArg (fun f => f w) (C.toCycles_i (n + 1) n)).symm.trans h

theorem homologyπ_eq_zero_of_boundary (C : ChainComplex (ModuleCat R) ℕ)
    (n : ℕ) (z : C.cycles n) (w : C.X (n + 1))
    (hw : C.d (n + 1) n w = C.iCycles n z) : C.homologyπ n z = 0 := by
  have hz : C.toCycles (n + 1) n w = z := by
    apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
    exact (congrArg (fun f => f w) (C.toCycles_i (n + 1) n)).trans hw
  rw [← hz]
  exact congrArg (fun f => f w) (C.toCycles_comp_homologyπ (n + 1) n)

end PolycyclicRecognition

end

end OAI
