import OAI.Analysis.CircleDomains.Uniformization.UniformSelectedAnnulus

namespace OAI

/-! Uniform separation of each actual selected circle from all other
holes in the same finite configuration. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration

lemma selected_planar_cap_eq {I:Type*} [Finite I]
    (C:FiniteJordanConfiguration I) (schedule:ℕ→I) (n:ℕ) :
    closure (jordanInterior ((iterate C schedule (n+1)).hole (schedule n)))=
      closedBall (selectedCenter C schedule n) (selectedRadius C schedule n) := by
  apply OnePoint.coe_injective.image_injective
  exact selected_cap_eq C schedule n

lemma selectedCircles_other_hole_separation {m:ℕ}
    (C:FiniteJordanConfiguration (Fin (m+1))) (ha:∀i,IsAnalyticJordanCap (C.hole i)) :
    ∃ε:ℝ,0<ε ∧ ∀n (i j:Fin (m+1)),j≠i → ∀y,
      y∈closure (jordanInterior ((iterate C (cyclicSchedule m) (visitTime n i+1)).hole j)) →
      selectedRadius C (cyclicSchedule m) (visitTime n i)+ε≤
        ‖y-selectedCenter C (cyclicSchedule m) (visitTime n i)‖ := by
  obtain ⟨ε,hε,hcollar⟩ := selectedCircles_common_collar C ha
  refine ⟨ε,hε,?_⟩
  intro n i j hji y hy
  have hcap : closure (jordanInterior ((iterate C (cyclicSchedule m) (visitTime n i+1)).hole i))=
      closedBall (selectedCenter C (cyclicSchedule m) (visitTime n i))
        (selectedRadius C (cyclicSchedule m) (visitTime n i)) := by
    simpa only [cyclicSchedule_visit] using selected_planar_cap_eq C (cyclicSchedule m) (visitTime n i)
  have hnot : y∉closedBall (selectedCenter C (cyclicSchedule m) (visitTime n i))
      (selectedRadius C (cyclicSchedule m) (visitTime n i)) := by
    intro h
    rw [←hcap] at h
    exact Set.disjoint_left.mp ((iterate C (cyclicSchedule m) (visitTime n i+1)).disjoint hji) hy h
  have hout : selectedRadius C (cyclicSchedule m) (visitTime n i)<
      ‖y-selectedCenter C (cyclicSchedule m) (visitTime n i)‖ :=
    lt_of_not_ge (fun h => hnot (mem_closedBall_iff_norm.mpr h))
  by_contra hn
  have hym := hcollar n i y hout (lt_of_not_ge hn)
  exact hym (mem_iUnion.mpr ⟨j,y,hy,rfl⟩)

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
