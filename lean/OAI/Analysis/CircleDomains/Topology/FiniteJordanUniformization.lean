import OAI.Analysis.CircleDomains.Uniformization.AnalyticFiniteUniformization
import OAI.Analysis.CircleDomains.Reflection.AnalyticCircularization

namespace OAI

/-! One finite cycle makes every Jordan boundary analytic. Applying the
proved invariant-coefficient construction then uniformizes the original
finite Jordan exterior. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer FiniteJordanConfiguration

lemma exists_fin_jordan_uniformization (n : ℕ) (C : FiniteJordanConfiguration (Fin n)) :
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ IsConformalEquivalence f C.region V := by
  cases n with
  | zero =>
    have he : C.region=univ := by
      change (⋃i : Fin 0,closedTerminalCap (C.hole i))ᶜ=univ
      simp
    rw [he]
    exact circleDomainModel_univ
  | succ m =>
    obtain ⟨V,f,hV,hf⟩ := exists_analytic_finite_uniformization
      (iterate C (cyclicSchedule m) (m+1)) (cyclic_iterate_analytic C le_rfl)
    exact ⟨V,f ∘ cumulativeMap C (cyclicSchedule m) (m+1),hV,
      (cumulativeMap_conformal C (cyclicSchedule m) (m+1)).trans hf⟩

lemma exists_finite_jordan_uniformization {I : Type*} [Finite I]
    (C : FiniteJordanConfiguration I) :
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ IsConformalEquivalence f C.region V := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let C' : FiniteJordanConfiguration (Fin (Fintype.card I)) :=
    ⟨fun i => C.hole (e.symm i),fun i j hij => C.disjoint (e.symm.injective.ne hij)⟩
  have hreg : C'.region=C.region := by
    have hu : (⋃i,closedTerminalCap (C'.hole i))=⋃i,closedTerminalCap (C.hole i) := by
      ext p
      constructor
      · intro hp
        obtain ⟨i,hi⟩ := mem_iUnion.mp hp
        exact mem_iUnion.mpr ⟨e.symm i,hi⟩
      · intro hp
        obtain ⟨i,hi⟩ := mem_iUnion.mp hp
        apply mem_iUnion.mpr
        refine ⟨e i,?_⟩
        simpa only [C',e.symm_apply_apply] using hi
    exact congrArg compl hu
  obtain ⟨V,f,hV,hf⟩ := exists_fin_jordan_uniformization (Fintype.card I) C'
  exact ⟨V,f,hV,hreg ▸ hf⟩

end CircleDomainRigidity

end

end OAI
