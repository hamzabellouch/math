import OAI.Analysis.CircleDomains.Topology.UnorientedCircleGreen
import OAI.Analysis.CircleDomains.Topology.JordanGreenProof
import OAI.Analysis.CircleDomains.Topology.TranslatedDiskGreen
import OAI.Analysis.CircleDomains.Sobolev.FiniteHoleIntegral
import OAI.Analysis.CircleDomains.Transfer.FiniteHoleCore
import OAI.Analysis.CircleDomains.Topology.CollarExtension

namespace OAI

/-! Discharge of the signed finite-round-hole Green input. The sign is
chosen from the outer Jordan circuit before the holes or the form. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff BigOperators
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma unorientedFiniteCircleGreenFormula : UnorientedFiniteCircleGreenFormula := by
  intro H γ hγ
  obtain ⟨ε,hε,hgreen⟩ := regular_jordan_green hγ
  refine ⟨ε,hε,?_⟩
  intro n c r hr hd hin O hO hsub P Q hP hQ
  let K := closure (jordanInterior H) \ ⋃ i, ball (c i) (r i)
  obtain ⟨p,hp,hep,_⟩ := exists_smooth_collar_extension hO
    (finite_hole_core_closed H c r) hsub hP 0
  obtain ⟨q,hq,heq,_⟩ := exists_smooth_collar_extension hO
    (finite_hole_core_closed H c r) hsub hQ 0
  have houter : planarFormIntegral p q γ = planarFormIntegral P Q γ := by
    unfold planarFormIntegral
    apply intervalIntegral.integral_congr
    intro t _
    have ht := jordan_boundary_mem_finite_hole_core hγ c r hin t
    dsimp only
    rw [hep.self_of_nhdsSet ht,heq.self_of_nhdsSet ht]
  have hcircle (i : Fin n) :
      planarFormIntegral p q (unitCircleParam (c i) (r i)) =
        planarFormIntegral P Q (unitCircleParam (c i) (r i)) := by
    unfold planarFormIntegral
    apply intervalIntegral.integral_congr
    intro t _
    have ht := circle_mem_finite_hole_core H c r hr hd hin i t
    dsimp only
    rw [hep.self_of_nhdsSet ht,heq.self_of_nhdsSet ht]
  have hsum : (∑ i, planarFormIntegral p q (unitCircleParam (c i) (r i))) =
      ∑ i, planarFormIntegral P Q (unitCircleParam (c i) (r i)) :=
    Finset.sum_congr rfl (fun i _ => hcircle i)
  have hcurl : Continuous (fun z => (fderiv ℝ q z) 1 - (fderiv ℝ p z) Complex.I) :=
    ((hq.continuous_fderiv (by simp)).clm_apply continuous_const).sub
      ((hp.continuous_fderiv (by simp)).clm_apply continuous_const)
  calc
    ε * planarFormIntegral P Q γ - ∑ i, planarFormIntegral P Q (unitCircleParam (c i) (r i)) =
        ε * planarFormIntegral p q γ - ∑ i, planarFormIntegral p q (unitCircleParam (c i) (r i)) := by
      rw [houter,hsum]
    _ = ∫ z in jordanInterior H \ ⋃ i, closedBall (c i) (r i),
        (fderiv ℝ q z) 1 - (fderiv ℝ p z) Complex.I := by
      rw [hgreen p q hp hq]
      simp_rw [translated_disk_green hp hq _ (hr _)]
      exact integral_finite_round_holes H c r hd hin hcurl
    _ = _ := by
      apply setIntegral_congr_fun ((jordanInterior_isOpen H).measurableSet.diff
        (MeasurableSet.iUnion fun _ => isClosed_closedBall.measurableSet))
      intro z hz
      have hzK : z ∈ K := by
        refine ⟨subset_closure hz.1,?_⟩
        intro hm
        obtain ⟨i,hi⟩ := mem_iUnion.mp hm
        exact hz.2 (mem_iUnion.mpr ⟨i,ball_subset_closedBall hi⟩)
      have hpz := hep.filter_mono (nhds_le_nhdsSet hzK)
      have hqz := heq.filter_mono (nhds_le_nhdsSet hzK)
      dsimp only
      rw [hpz.fderiv_eq,hqz.fderiv_eq]

end CircleDomainRigidity

end

end OAI
