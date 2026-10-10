import OAI.Analysis.CircleDomains.Reflection.ActualPhaseReflection
import OAI.Analysis.CircleDomains.Topology.AnalyticCircleImage
import OAI.Analysis.CircleDomains.Reflection.MovingCircleReflectionSides

namespace OAI

/-! Exact circle images and the two sides for every finite reflected phase. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma circleReflectionExtension_inside_norm_lt {U:Set ℂ} {f:ℂ→ℂ} {c:ℂ} {r:ℝ}
    (hr:0<r) (hz:∀z∈U,z≠0) (hs:∀z∈U,unitCircleReflection z∈U)
    (hf:∀z∈U,1<‖z‖ → r<‖f z-c‖) {z:ℂ} (hzU:z∈U) (hzn:‖z‖<1) :
    ‖circleReflectionExtension c r f z-c‖<r := by
  let g := fun w => (f w-c)/(r:ℂ)
  have hge : 1<‖g (unitCircleReflection z)‖ := by
    change 1<‖(f (unitCircleReflection z)-c)/(r:ℂ)‖
    rw [normalized_circle_norm c hr]
    exact (one_lt_div hr).mpr
      (hf _ (hs z hzU) (unitCircleReflection_strict_outer (hz z hzU) hzn))
  have hsmall : ‖annularCircleReflect g z‖<1 := by
    rw [annularCircleReflect,ite_eq_right (not_le_of_gt hzn),unitCircleReflection_norm]
    exact (inv_lt_one₀ (zero_lt_one.trans hge)).mpr hge
  change ‖c+(r:ℂ)*annularCircleReflect g z-c‖<r
  rw [add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  nlinarith

namespace FiniteJordanConfiguration
variable {m:ℕ} {C:FiniteJordanConfiguration (Fin (m+1))} {i:Fin (m+1)}

lemma PhaseCollar.reflected_boundary_iff (P:PhaseCollar C i) (n:ℕ) {z:ℂ}
    (hz:z∈symmetricCircleAnnulus P.radius) :
    ‖P.reflected n z-selectedCenter C (cyclicSchedule m) (visitTime n i)‖=
      selectedRadius C (cyclicSchedule m) (visitTime n i) ↔ ‖z‖=1 := by
  let c := selectedCenter C (cyclicSchedule m) (visitTime n i)
  let r := selectedRadius C (cyclicSchedule m) (visitTime n i)
  have hr:0<r := selectedRadius_pos C (cyclicSchedule m) (visitTime n i)
  constructor
  · intro he
    rcases lt_trichotomy ‖z‖ 1 with h|h|h
    · have hlt := circleReflectionExtension_inside_norm_lt hr
        (fun _ hw => symmetricCircleAnnulus_ne_zero (zero_lt_one.trans P.radius_gt) hw)
        (fun _ hw => symmetricCircleAnnulus_reflection (zero_lt_one.trans P.radius_gt) hw)
        (P.outside_strict n) hz h
      exact False.elim ((ne_of_lt hlt) he)
    · exact h
    · have hlt := P.outside_strict n z hz h
      have heq : P.reflected n z=P.trace n z := circleReflectionExtension_outer hr h.le
      rw [heq] at he
      exact False.elim ((ne_of_gt hlt) he)
  · intro he
    rw [show P.reflected n z=P.trace n z from circleReflectionExtension_outer hr he.ge]
    exact P.circle n z hz he

lemma PhaseCollar.reflected_circle_image (P:PhaseCollar C i) (n:ℕ) :
    P.reflected n '' sphere (0:ℂ) 1=
      sphere (selectedCenter C (cyclicSchedule m) (visitTime n i))
        (selectedRadius C (cyclicSchedule m) (visitTime n i)) :=
  analytic_circle_image_eq (isOpen_symmetricCircleAnnulus P.radius)
    (unit_circle_subset_symmetricCircleAnnulus P.radius_gt)
    (P.reflected_holomorphic n) (P.reflected_injective n)
    (selectedRadius_pos C (cyclicSchedule m) (visitTime n i)).le
    (fun _ hz => P.reflected_boundary_iff n hz)

lemma PhaseCollar.reflected_image_outside_subset (P:PhaseCollar C i) (n:ℕ) :
    (P.reflected n '' symmetricCircleAnnulus P.radius)\
      closedBall (selectedCenter C (cyclicSchedule m) (visitTime n i))
        (selectedRadius C (cyclicSchedule m) (visitTime n i)) ⊆
      (iterate C (cyclicSchedule m) (visitTime n i+1)).planeRegion := by
  rintro _ ⟨⟨z,hz,rfl⟩,hn⟩
  have ho:1<‖z‖ := by
    by_contra hh
    rcases lt_or_eq_of_le (le_of_not_gt hh) with hlt|he
    · exact hn (mem_closedBall_iff_norm.mpr (circleReflectionExtension_inside_norm_le
        (selectedRadius_pos C (cyclicSchedule m) (visitTime n i))
        (fun _ hw => symmetricCircleAnnulus_ne_zero (zero_lt_one.trans P.radius_gt) hw)
        (fun _ hw => symmetricCircleAnnulus_reflection (zero_lt_one.trans P.radius_gt) hw)
        (P.outside n) hz hlt))
    · exact hn (mem_closedBall_iff_norm.mpr ((P.reflected_boundary_iff n hz).mpr he).le)
  rw [P.reflected_agrees n hz ho]
  have hmap := (cumulativeMap_conformal C (cyclicSchedule m) (visitTime n i+1)).bijOn.mapsTo
    (P.exterior_source z hz ho)
  have hfinite := finite_image_of_fixes_infty
    (cumulativeMap_conformal C (cyclicSchedule m) (visitTime n i+1)).bijOn.injOn
    C.infty_mem_region (cumulativeMap_principal C (cyclicSchedule m) (visitTime n i+1)).1
    (P.exterior_source z hz ho)
  change (finiteCoord (cumulativeMap C (cyclicSchedule m) (visitTime n i+1)
    (P.coordinate z:Sphere)):Sphere)∈(iterate C (cyclicSchedule m) (visitTime n i+1)).region
  rwa [coe_finiteCoord hfinite]

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
