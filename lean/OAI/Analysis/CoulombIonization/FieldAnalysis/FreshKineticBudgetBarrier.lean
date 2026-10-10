import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.CoupledCoreExcessBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

namespace CoulombAtom

lemma cut_out_kinetic_le_field_work {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevFermion ψ) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    (∑ c : Fin L → Fin 2, outKinetic (orderedCutForm p hp ψ c)) ≤
      corePriceExcess Z lam ψ+(1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight p)+
        (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          conditionalFieldSum Z lam (orderedCutForm p hp ψ c) s u) := by
  have hid := fock_cut_excess_identity p hp hψ.sobolevVector Z lam
  simp_rw [cutExteriorPrice_eq_field_work p hp hψ.sobolevVector Z lam] at hid
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib] at hid
  have he : 0 ≤ ∑ c : Fin L → Fin 2, cutCoreExcess p hp Z lam ψ c :=
    Finset.sum_nonneg (fun c _ => cutCoreExcess_nonneg p hp hψ c hZ hlam)
  have hr : 0 ≤ ∑ c : Fin L → Fin 2, outRepulsion (orderedCutForm p hp ψ c) :=
    Finset.sum_nonneg (fun c _ => outRepulsion_nonneg _)
  linarith only [hid,he,hr]

 theorem radial_out_kinetic_coupling {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (y : Space) {t b R : ℝ} (ht : 0 ≤ t)
    (hb : 0 < b) (hy : t+2*b ≤ ‖y‖) (hR : t+b ≤ R) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    (∑ c : Fin L → Fin 2, outKinetic (orderedCutForm p hp ψ c)) ≤
      corePriceExcess Z lam ψ+(1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight p)+
        Real.sqrt (freshOutMaximumSecondMoment p hp ψ Z lam)*
          Real.sqrt (rawCountMoment ψ y R) := by
  dsimp only
  refine (cut_out_kinetic_le_field_work _ _ hψ hZ hlam).trans (add_le_add le_rfl
    ((radial_full_field_work_budget hψ.sobolevVector y ht hb hy hZ hlam.le).trans ?_))
  rw [rawCountMoment_eq_integral hψ.sobolevVector]
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (radialCut_out_second_moment hψ.sobolevVector y ht hb hR))
    (Real.sqrt_nonneg _)

end CoulombAtom

end

end OAI
