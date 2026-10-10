import OAI.Analysis.CircleDomains.Uniformization.FiniteCoreCorrespondence

namespace OAI

/-! The compact boundary correspondence is retained by every finite
composition starting from an analytic Jordan configuration. -/
open Set Function Filter Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration
variable {I:Type*} [Finite I]

lemma iterate_analytic_of_initial (C:FiniteJordanConfiguration I)
    (ha:∀i,IsAnalyticJordanCap (C.hole i)) (schedule:ℕ→I) (n:ℕ) :
    ∀i,IsAnalyticJordanCap ((iterate C schedule n).hole i) := by
  induction n with
  | zero => exact ha
  | succ n ih =>
    intro i
    by_cases he : i=schedule n
    · subst i
      exact (chosenStep (iterate C schedule n) (schedule n)).analytic_selected
    · exact (chosenStep (iterate C schedule n) (schedule n)).analytic_other he (ih i)

lemma exists_cumulative_core_correspondence (C:FiniteJordanConfiguration I)
    (ha:∀i,IsAnalyticJordanCap (C.hole i)) (schedule:ℕ→I) (n:ℕ) :
    ∃e : closure C.region ≃ₜ closure (iterate C schedule n).region,
      ∀p : closure C.region, (p:Sphere)∈C.region →
        (e p:Sphere)=cumulativeMap C schedule n p := by
  induction n with
  | zero => exact ⟨Homeomorph.refl _,fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨e,he⟩ := ih
    let q := chosenStep (iterate C schedule n) (schedule n)
    obtain ⟨d,hd⟩ := q.exists_core_correspondence
      (iterate_analytic_of_initial C ha schedule n (schedule n))
    refine ⟨e.trans d,?_⟩
    intro p hp
    have hep : (e p:Sphere)∈(iterate C schedule n).region := by
      rw [he p hp]
      exact (cumulativeMap_conformal C schedule n).bijOn.mapsTo hp
    change (d (e p):Sphere)=stageMap C schedule n (cumulativeMap C schedule n p)
    rw [hd (e p) hep,he p hp]
    rfl

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
