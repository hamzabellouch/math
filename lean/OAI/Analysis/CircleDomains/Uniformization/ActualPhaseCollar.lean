import OAI.Analysis.CircleDomains.Topology.BoundedAnalyticCollar
import OAI.Analysis.CircleDomains.Rigidity.FiniteCoreAnalyticTrace
import OAI.Analysis.CircleDomains.Uniformization.SelectedPhaseBoundary
import OAI.Analysis.CircleDomains.Reflection.MovingCircleReflectionLimit

namespace OAI

/-! Fixed source collars and uniformly bounded circle traces for the
actual cumulative maps at one phase of the cyclic construction. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration

structure PhaseCollar {m:ℕ} (C:FiniteJordanConfiguration (Fin (m+1))) (i:Fin (m+1)) where
  radius : ℝ
  radius_gt : 1<radius
  coordinate : ℂ→ℂ
  analytic : DifferentiableOn ℂ coordinate (symmetricCircleAnnulus radius)
  injective : InjOn coordinate (symmetricCircleAnnulus radius)
  boundary_image : coordinate '' sphere 0 1=frontier (jordanInterior (C.hole i))
  exterior_source : ∀z∈symmetricCircleAnnulus radius,1<‖z‖ → (coordinate z:Sphere)∈C.region
  trace : ℕ→ℂ→ℂ
  agrees : ∀n z,z∈symmetricCircleAnnulus radius → 1<‖z‖ →
    trace n z=finiteCoord (cumulativeMap C (cyclicSchedule m) (visitTime n i+1) (coordinate z:Sphere))
  trace_injective : ∀n,InjOn (trace n) (symmetricCircleAnnulus radius∩{z | 1≤‖z‖})
  outside_strict : ∀n z,z∈symmetricCircleAnnulus radius → 1<‖z‖ →
    selectedRadius C (cyclicSchedule m) (visitTime n i)<
      ‖trace n z-selectedCenter C (cyclicSchedule m) (visitTime n i)‖
  continuous : ∀n,ContinuousOn (trace n) (symmetricCircleAnnulus radius∩{z | 1≤‖z‖})
  holomorphic : ∀n z,z∈symmetricCircleAnnulus radius → 1<‖z‖ → DifferentiableAt ℂ (trace n) z
  outside : ∀n z,z∈symmetricCircleAnnulus radius → 1≤‖z‖ →
    selectedRadius C (cyclicSchedule m) (visitTime n i)≤
      ‖trace n z-selectedCenter C (cyclicSchedule m) (visitTime n i)‖
  circle : ∀n z,z∈symmetricCircleAnnulus radius → ‖z‖=1 →
    ‖trace n z-selectedCenter C (cyclicSchedule m) (visitTime n i)‖=
      selectedRadius C (cyclicSchedule m) (visitTime n i)
  bound : ℝ
  centers_bounded : ∀n,‖selectedCenter C (cyclicSchedule m) (visitTime n i)‖+
    selectedRadius C (cyclicSchedule m) (visitTime n i)≤bound
  trace_bounded : ∀n z,z∈symmetricCircleAnnulus radius → 1≤‖z‖ → ‖trace n z‖≤bound

lemma phaseCollar_nonempty {m:ℕ} (C:FiniteJordanConfiguration (Fin (m+1)))
    (ha:∀j,IsAnalyticJordanCap (C.hole j)) (i:Fin (m+1)) : Nonempty (PhaseCollar C i) := by
  classical
  obtain ⟨A,L,β,hA,hL,hβ,hiβ,hboundary,hβbound,houter,hclosed⟩ :=
    C.exists_bounded_analytic_boundary_collar i (ha i)
  choose E hEc hEi hEe hEimg hEboundary using
    (fun n:ℕ => exists_global_cumulative_core_extension C ha (cyclicSchedule m) (visitTime n i+1))
  let F := fun n z => finiteCoord (E n (β z:Sphere))
  have hfix (n:ℕ) : E n ∞=∞ :=
    (hEe n C.infty_mem_region).trans (cumulativeMap_principal C (cyclicSchedule m) (visitTime n i+1)).1
  have hagrees (n:ℕ) (z:ℂ) (hz:z∈symmetricCircleAnnulus A) (hzn:1<‖z‖) :
      F n z=finiteCoord (cumulativeMap C (cyclicSchedule m) (visitTime n i+1) (β z:Sphere)) := by
    change finiteCoord (E n (β z:Sphere))=_
    rw [hEe n (houter z hz hzn)]
  have hcircle (n:ℕ) (z:ℂ) (hz:z∈symmetricCircleAnnulus A) (hzn:‖z‖=1) :
      ‖F n z-selectedCenter C (cyclicSchedule m) (visitTime n i)‖=
        selectedRadius C (cyclicSchedule m) (visitTime n i) := by
    apply selected_phase_boundary_norm C i n (hEboundary n)
    exact hboundary ▸ mem_image_of_mem β (mem_sphere_zero_iff_norm.mpr hzn)
  have hout (n:ℕ) (z:ℂ) (hz:z∈symmetricCircleAnnulus A) (hzn:1<‖z‖) :
      selectedRadius C (cyclicSchedule m) (visitTime n i)<
        ‖F n z-selectedCenter C (cyclicSchedule m) (visitTime n i)‖ := by
    rw [hagrees n z hz hzn]
    apply lt_of_not_ge
    intro hle
    exact selected_disk_omitted C (cyclicSchedule m) (visitTime n i) (β z)
      (houter z hz hzn) (mem_closedBall_iff_norm.mpr hle)
  obtain ⟨R₀,hR₀,hsource₀⟩ := C.exists_exterior_radius
  let R := max R₀ L
  have hR : 0<R := hR₀.trans_le (le_max_left _ _)
  have hsource : ((((↑):ℂ→Sphere) '' ball 0 R)ᶜ)⊆C.region := by
    apply Subset.trans _ hsource₀
    exact compl_subset_compl.mpr (image_mono (ball_subset_ball (le_max_left _ _)))
  have hcBound (n:ℕ) : ‖selectedCenter C (cyclicSchedule m) (visitTime n i)‖+
      selectedRadius C (cyclicSchedule m) (visitTime n i)≤6*R := by
    obtain ⟨hc,_,hr⟩ := selected_disk_bounded C (cyclicSchedule m) hR hsource (visitTime n i)
    linarith
  refine ⟨{
    radius := A
    radius_gt := hA
    coordinate := β
    analytic := hβ
    injective := hiβ
    boundary_image := hboundary
    exterior_source := houter
    trace := F
    agrees := hagrees
    trace_injective := ?_
    outside_strict := hout
    continuous := ?_
    holomorphic := ?_
    outside := ?_
    circle := hcircle
    bound := 6*R
    centers_bounded := hcBound
    trace_bounded := ?_ }⟩
  · intro n z hz w hw he
    apply hiβ hz.1 hw.1
    apply OnePoint.coe_injective
    apply hEi n (hclosed z hz.1 hz.2) (hclosed w hw.1 hw.2)
    have hzfin := finite_core_image_ne_infty (hEi n) (hfix n) (hclosed z hz.1 hz.2)
    have hwfin := finite_core_image_ne_infty (hEi n) (hfix n) (hclosed w hw.1 hw.2)
    change finiteCoord (E n (β z:Sphere))=finiteCoord (E n (β w:Sphere)) at he
    exact (coe_finiteCoord hzfin).symm.trans ((congrArg ((↑):ℂ→Sphere) he).trans (coe_finiteCoord hwfin))
  · intro n
    exact finite_core_trace_continuousOn (hEc n) (hEi n) (hfix n)
      (hβ.continuousOn.mono inter_subset_left) (fun z hz => hclosed z hz.1 hz.2)
  · intro n z hz hzn
    exact finite_core_trace_differentiableAt (hEe n)
      (cumulativeMap_conformal C (cyclicSchedule m) (visitTime n i+1))
      (cumulativeMap_principal C (cyclicSchedule m) (visitTime n i+1)).1
      ((hβ z hz).differentiableAt ((isOpen_symmetricCircleAnnulus A).mem_nhds hz))
      (houter z hz hzn)
  · intro n z hz hzn
    rcases eq_or_lt_of_le hzn with he|he
    · exact (hcircle n z hz he.symm).ge
    · exact (hout n z hz he).le
  · intro n z hz hzn
    rcases eq_or_lt_of_le hzn with he|he
    · have hnorm := hcircle n z hz he.symm
      calc
        ‖F n z‖ ≤ ‖F n z-selectedCenter C (cyclicSchedule m) (visitTime n i)‖+
            ‖selectedCenter C (cyclicSchedule m) (visitTime n i)‖ := by
          simpa only [sub_add_cancel] using norm_add_le
            (F n z-selectedCenter C (cyclicSchedule m) (visitTime n i))
            (selectedCenter C (cyclicSchedule m) (visitTime n i))
        _ ≤ 6*R := by rw [hnorm];linarith [hcBound n]
    · rw [hagrees n z hz he]
      have hn := (circularization_uniform_bounds C (cyclicSchedule m) hR hsource
        (visitTime n i+1)).2.1 (β z) (houter z hz he)
        ((hβbound z hz).trans (by have := le_max_right R₀ L;dsimp [R];linarith))
      exact hn.trans (by linarith)

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
