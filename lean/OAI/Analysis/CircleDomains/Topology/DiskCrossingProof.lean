import OAI.Analysis.CircleDomains.Topology.CrosscutAvoidingContinuum
import OAI.Analysis.CircleDomains.Topology.CrosscutBoundarySeparation
import OAI.Analysis.CircleDomains.Topology.AlternatingBoundaryCoordinates

namespace OAI

/-! Alternating compact continua in the closed disk intersect, derived
from the existing Schoenflies input and the constructed simple crosscut. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

theorem unitDiskAlternatingContinua (hsch : PlanarSchoenflies) : UnitDiskAlternatingContinua := by
  intro A B hAc hA hBc hB hAd hBd θ hθ h0 h2 h1 h3
  by_contra hn
  have hAB : Disjoint A B := Set.disjoint_left.mpr (fun z hzA hzB => hn ⟨z,hzA,hzB⟩)
  let z : Fin 4 → ℂ := fun i => standardCirclePoint (θ i)
  have hz0 : z 0 ≠ 0 := by
    intro h
    have he := Circle.norm_coe ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero) (θ 0))
    change ‖z 0‖ = 1 at he
    rw [h,norm_zero] at he
    exact zero_ne_one he
  have h20 : z 2 ≠ z 0 := by
    intro h
    have he := congrArg unitCircleCut (standardCirclePoint_injective h)
    exact (ne_of_gt (hθ (by decide : (0 : Fin 4) < 2))) he
  obtain ⟨p,hpi,hpint,hpB⟩ := exists_disk_crosscut_avoiding hAc hA hAd hBc.isClosed hAB
    h2 h0 (Circle.norm_coe _) (Circle.norm_coe _) h20
  let R := Homeomorph.mulLeft₀ (z 0) hz0
  let q : Path ((z 0)⁻¹ * z 2) 1 := {
    toFun := fun t => (z 0)⁻¹ * p t
    continuous_toFun := continuous_const.mul p.continuous
    source' := by rw [p.source]
    target' := by rw [p.target,inv_mul_cancel₀ hz0] }
  have hqp (t : PathTime) : R (q t) = p t := by
    change z 0 * ((z 0)⁻¹ * p t) = p t
    rw [← mul_assoc,mul_inv_cancel₀ hz0,one_mul]
  have hRnorm (w : ℂ) : ‖R.symm w‖ = ‖w‖ := by
    change ‖(z 0)⁻¹ * w‖ = ‖w‖
    rw [norm_mul,norm_inv,show ‖z 0‖ = 1 from Circle.norm_coe _,inv_one,one_mul]
  have hqi : Injective q := fun s t he => hpi (by rw [← hqp s,← hqp t,he])
  have hqint : ∀ t ∈ Ioo (0 : PathTime) 1, ‖q t‖ < 1 := by
    intro t ht
    change ‖R.symm (p t)‖ < 1
    rw [hRnorm]
    exact hpint t ht
  obtain ⟨ha,ha1,hx,hy⟩ := alternating_boundary_rotated_arcs θ hθ
  obtain ⟨H,hf,_,hinside⟩ := exists_disk_crosscut_jordan hsch q hqi hqint ha ha1
  let C := R.symm '' B
  have hC : IsPreconnected C := hB.isPreconnected.image R.symm R.symm.continuous.continuousOn
  have hCd : C ⊆ closedBall (0 : ℂ) 1 := by
    rintro _ ⟨w,hw,rfl⟩
    rw [mem_closedBall_zero_iff,hRnorm]
    exact mem_closedBall_zero_iff.mp (hBd hw)
  have hCq : Disjoint C (range q) := by
    apply Set.disjoint_left.mpr
    rintro w ⟨b,hb,he⟩ ⟨t,ht⟩
    have hpt : p t = b := by
      rw [← hqp t,ht,← he,R.apply_symm_apply]
    exact Set.disjoint_left.mp hpB ⟨t,hpt⟩ hb
  have hxC : (z 0)⁻¹ * z 1 ∈ C := ⟨z 1,h1,rfl⟩
  have hyC : (z 0)⁻¹ * z 3 ∈ C := ⟨z 3,h3,rfl⟩
  have hxcl : (z 0)⁻¹ * z 1 ∈ closure (jordanInterior H) :=
    frontier_subset_closure (hf ▸ Or.inr hx)
  have hynot : (z 0)⁻¹ * z 3 ∉ closure (jordanInterior H) := by
    have he := disk_crosscut_exterior_circle q ha hqint H hf hinside
    have hh := he.symm ▸ hy
    exact hh.1
  rcases connected_avoiding_crosscut_one_side q ha H hf hinside hC hCd hCq with h | h
  · exact hynot (h hyC)
  · exact h hxC hxcl

end CircleDomainRigidity

end

end OAI
