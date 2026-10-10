import OAI.Analysis.CircleDomains.Sobolev.PhysicalCoordinateLines
import Mathlib.Topology.Order.Compact

namespace OAI

/-! A compact bounded region has a first boundary point on each
coordinate line meeting its closure. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def planeTransverse (i : Fin 2) (z : EuclideanPlane) : ℝ :=
  if i = 0 then z 1 else z 0

 theorem continuous_planeTransverse (i : Fin 2) : Continuous (planeTransverse i) := by
  unfold planeTransverse
  split <;> fun_prop

 theorem physicalCoordinateLine_transverse (i : Fin 2) (y x : ℝ) :
    planeTransverse i (physicalCoordinateLine i y x) = y := by
  fin_cases i
  · change (euclideanPlaneCoordinates.symm (x,y)) 1 = y
    exact congrArg Prod.snd (euclideanPlaneCoordinates.apply_symm_apply (x,y))
  · change (euclideanPlaneCoordinates.symm (y,x)) 0 = y
    exact congrArg Prod.fst (euclideanPlaneCoordinates.apply_symm_apply (y,x))

 theorem physicalCoordinateLine_of_transverse (i : Fin 2) {z : EuclideanPlane} {y : ℝ}
    (hy : planeTransverse i z = y) : physicalCoordinateLine i y (z i) = z := by
  apply euclideanPlaneCoordinates.injective
  fin_cases i <;> simpa [physicalCoordinateLine,planeTransverse] using hy.symm

 theorem exists_coordinate_frontier {U : Set EuclideanPlane}
    (hU : IsOpen U) (hcompact : IsCompact (closure U)) (i : Fin 2) {y : ℝ}
    (hne : ∃ z ∈ closure U, planeTransverse i z = y) :
    ∃ x : ℝ, physicalCoordinateLine i y x ∈ frontier U := by
  let K := closure U ∩ {z : EuclideanPlane | planeTransverse i z = y}
  have hK : IsCompact K := hcompact.inter_right
    (isClosed_eq (continuous_planeTransverse i) continuous_const)
  have hKne : K.Nonempty := by
    obtain ⟨z,hz,hy⟩ := hne
    exact ⟨z,hz,hy⟩
  have hi : Continuous (fun z : EuclideanPlane => z i) := by fun_prop
  obtain ⟨x,hx⟩ := (hK.image hi).exists_isLeast (hKne.image (fun z => z i))
  obtain ⟨z,hz,hzx⟩ := hx.1
  have he : physicalCoordinateLine i y x = z := by
    rw [← hzx]
    exact physicalCoordinateLine_of_transverse i hz.2
  have hxcl : physicalCoordinateLine i y x ∈ closure U := he.symm ▸ hz.1
  have hmin : ∀ w ∈ closure U, planeTransverse i w = y → x ≤ w i := by
    intro w hw hwy
    exact hx.2 (mem_image_of_mem _ ⟨hw,hwy⟩)
  have hnot : physicalCoordinateLine i y x ∉ U := by
    intro hin
    have hn : (physicalCoordinateLine i y) ⁻¹' U ∈ 𝓝 x :=
      (hU.preimage (physicalCoordinateLine_contDiff i y).continuous).mem_nhds hin
    obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp hn
    have hback : x-ε/2 ∈ ball x ε := by
      rw [mem_ball,Real.dist_eq]
      rw [show x-ε/2-x = -(ε/2) by ring,abs_neg,abs_of_pos (half_pos hε)]
      linarith
    have hm := hmin _ (subset_closure (hεU hback))
      (physicalCoordinateLine_transverse i y (x-ε/2))
    rw [physicalCoordinateLine_coordinate] at hm
    linarith
  exact ⟨x,by rw [frontier,hU.interior_eq]; exact ⟨hxcl,hnot⟩⟩

end CircleDomainRigidity

end

end OAI
