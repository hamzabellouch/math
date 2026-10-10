import OAI.Analysis.CircleDomains.Uniformization.ActualPhaseCollar
import OAI.Analysis.CircleDomains.Reflection.MovingCircleReflectionInjection

namespace OAI

/-! Explicit bounded holomorphic reflections of the actual fixed-phase
cumulative maps on their common source collar. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration
variable {m:ℕ} {C:FiniteJordanConfiguration (Fin (m+1))} {i:Fin (m+1)}

def PhaseCollar.reflected (P:PhaseCollar C i) (n:ℕ) : ℂ→ℂ :=
  circleReflectionExtension (selectedCenter C (cyclicSchedule m) (visitTime n i))
    (selectedRadius C (cyclicSchedule m) (visitTime n i)) (P.trace n)

lemma PhaseCollar.reflected_holomorphic (P:PhaseCollar C i) (n:ℕ) :
    DifferentiableOn ℂ (P.reflected n) (symmetricCircleAnnulus P.radius) :=
  circleReflectionExtension_differentiableOn (selectedRadius_pos C (cyclicSchedule m) (visitTime n i))
    (isOpen_symmetricCircleAnnulus P.radius)
    (fun _ hz => symmetricCircleAnnulus_ne_zero (zero_lt_one.trans P.radius_gt) hz)
    (fun _ hz => symmetricCircleAnnulus_reflection (zero_lt_one.trans P.radius_gt) hz)
    (P.continuous n) (P.holomorphic n) (P.outside n) (P.circle n)

lemma PhaseCollar.reflected_injective (P:PhaseCollar C i) (n:ℕ) :
    InjOn (P.reflected n) (symmetricCircleAnnulus P.radius) :=
  injOn_circleReflectionExtension (selectedRadius_pos C (cyclicSchedule m) (visitTime n i))
    (fun _ hz => symmetricCircleAnnulus_ne_zero (zero_lt_one.trans P.radius_gt) hz)
    (fun _ hz => symmetricCircleAnnulus_reflection (zero_lt_one.trans P.radius_gt) hz)
    (P.trace_injective n) (P.outside_strict n) (P.circle n)

lemma PhaseCollar.reflected_bounded (P:PhaseCollar C i) (n:ℕ) {z:ℂ}
    (hz:z∈symmetricCircleAnnulus P.radius) : ‖P.reflected n z‖≤P.bound :=
  circleReflectionExtension_norm_le (selectedRadius_pos C (cyclicSchedule m) (visitTime n i))
    (fun _ hz => symmetricCircleAnnulus_ne_zero (zero_lt_one.trans P.radius_gt) hz)
    (fun _ hz => symmetricCircleAnnulus_reflection (zero_lt_one.trans P.radius_gt) hz)
    (P.centers_bounded n) (fun z hz hzo => ⟨P.outside n z hz hzo,P.trace_bounded n z hz hzo⟩) hz

lemma PhaseCollar.reflected_agrees (P:PhaseCollar C i) (n:ℕ) {z:ℂ}
    (hz:z∈symmetricCircleAnnulus P.radius) (hzo:1<‖z‖) :
    P.reflected n z=finiteCoord
      (cumulativeMap C (cyclicSchedule m) (visitTime n i+1) (P.coordinate z:Sphere)) := by
  rw [PhaseCollar.reflected,circleReflectionExtension_outer
    (selectedRadius_pos C (cyclicSchedule m) (visitTime n i)) hzo.le]
  exact P.agrees n z hz hzo

lemma PhaseCollar.exists_reflected_limit (P:PhaseCollar C i) (t:ℕ→ℕ) :
    ∃s:ℕ→ℕ, ∃F:ℂ→ℂ, StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n => P.reflected (t (s n))) F atTop
        (symmetricCircleAnnulus P.radius) ∧
      DifferentiableOn ℂ F (symmetricCircleAnnulus P.radius) := by
  obtain ⟨s,F,hs,hlim⟩ := montelExhaustion (fun _ => symmetricCircleAnnulus P.radius)
    (fun n => P.reflected (t n)) (fun _ => isOpen_symmetricCircleAnnulus P.radius)
    (fun _ _ _ => Subset.refl _) (fun n => P.reflected_holomorphic (t n)) (by
      intro K hK hKU
      exact ⟨P.bound,fun n z _ hz => P.reflected_bounded (t n) hz⟩)
  simp only [iUnion_const] at hlim
  exact ⟨s,F,hs,hlim,hlim.differentiableOn
    (Eventually.of_forall (fun n => P.reflected_holomorphic (t (s n))))
    (isOpen_symmetricCircleAnnulus P.radius)⟩

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
