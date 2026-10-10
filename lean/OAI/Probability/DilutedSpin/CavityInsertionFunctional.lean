import OAI.Probability.DilutedSpin.CavityAllocatedMean
import OAI.Probability.DilutedSpin.CavitySiteMean
import OAI.Probability.DilutedSpin.CavityTrialIdentity
import OAI.Probability.DilutedSpin.CountBridgeTools
import OAI.Probability.DilutedSpin.FullRootIncrement

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N p k : ℕ} [NeZero N]

omit [MeasurableSpace X] in
lemma cavityArray_insertionFunctional (ρ : Measure ((Fin N → Spin) → ℝ)) [IsProbabilityMeasure ρ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (theta : X → InteractionSample p) (field : Y → ℝ)
    (hhm : Measurable field) {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : LipschitzWith 1 F)
    {H C : ℝ} (hH : 0≤H) (hC : 0≤C) (hh : ∀ y,|field y|≤H)
    (z : Fin k → X) (hz : ∀ a,‖(theta (z a)).1‖≤C) :
    (FiniteLaw.uniform : FiniteLaw (Fin k → Fin (p-1) → Fin N)).expect (fun j =>
      ∫ y,energyInsertionFunctional ρ F
        (fun σ => cavitySiteEnergy (fun a => theta (z a)) (field y) (fun a => σ (j a.1 a.2))) ∂ξ)=
      ∫ E,cavityArrayValue ξ theta field F E z-F E ∂ρ := by
  let V := fun (j : Fin k → Fin (p-1) → Fin N) (y : Y) (σ : Fin N → Spin) =>
    cavitySiteEnergy (fun a => theta (z a)) (field y) (fun a => σ (j a.1 a.2))
  have hVm j : Measurable (V j) := by
    apply Measurable.of_eval
    intro σ
    change Measurable (fun y => cavitySiteEnergy (fun a => theta (z a)) (field y)
      (fun a => σ (j a.1 a.2)))
    unfold cavitySiteEnergy
    apply Measurable.log
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro ε _
    apply Measurable.exp
    exact (hhm.mul_const _).add measurable_const
  have hVb j y : ‖V j y‖≤H+C*k := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro σ
    have hb := cavitySiteEnergy_bound (fun a => theta (z a)) (field y) (fun a => σ (j a.1 a.2))
    have hs : (∑ a : Fin k,‖(theta (z a)).1‖)≤C*k := by
      simpa [mul_comm] using Finset.sum_le_sum (fun a (_ : a∈(Finset.univ : Finset (Fin k))) => hz a)
    simpa only [Real.norm_eq_abs] using hb.trans (add_le_add (hh y) hs)
  have hi j : Integrable (fun w : Y×((Fin N → Spin) → ℝ) => F (w.2+V j w.1)-F w.2) (ξ.prod ρ) := by
    apply Integrable.of_bound ((hF.continuous.measurable.comp (measurable_snd.add ((hVm j).comp measurable_fst))).sub
      (hF.continuous.measurable.comp measurable_snd)).aestronglyMeasurable (H+C*k)
    exact ae_of_all _ (fun w => by
      simpa only [Real.norm_eq_abs,add_sub_cancel_left,NNReal.coe_one,one_mul,Pi.sub_apply,Pi.add_apply,Function.comp_apply] using
        (hF.norm_sub_le (w.2+V j w.1) w.2).trans (by simpa using hVb j w.1))
  have hj j : (∫ y,energyInsertionFunctional ρ F (V j y) ∂ξ)=
      ∫ E,∫ y,F (E+V j y)-F E ∂ξ ∂ρ := integral_integral_swap (hi j)
  have hsub E j : (∫ y,F (E+V j y)-F E ∂ξ)=(∫ y,F (E+V j y) ∂ξ)-F E := by
    have he : Integrable (fun y => F (E+V j y)-F E) ξ := by
      apply Integrable.of_bound ((hF.continuous.measurable.comp (measurable_const.add (hVm j))).sub measurable_const).aestronglyMeasurable (H+C*k)
      exact ae_of_all _ (fun y => by simpa using (hF.norm_sub_le (E+V j y) E).trans (by simpa using hVb j y))
    have he' : Integrable (fun y => F (E+V j y)) ξ := by
      exact (he.add (integrable_const (F E))).congr (ae_of_all _ (fun y => by simp))
    rw [integral_sub he' (integrable_const _)]; simp
  change (FiniteLaw.uniform : FiniteLaw (Fin k → Fin (p-1) → Fin N)).expect
    (fun j => ∫ y,energyInsertionFunctional ρ F (V j y) ∂ξ)=_
  simp_rw [hj]
  rw [← FiniteLaw.integral_expect _ ρ _ (fun j => (hi j).integral_prod_right)]
  apply integral_congr_ae
  filter_upwards [] with E
  simp only [hsub,FiniteLaw.expect_sub,FiniteLaw.expect_const,cavityArrayValue]
  rfl

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators
variable {Λ R : Type} [Fintype Λ] [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]

lemma activeCountMean_site (q : ℕ) (M : Model (q+1)) (hM : Admissible M)
    (a : Λ) (r : ℕ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin (r+1) → ℝ)
    (hm : ∀ d,0 < m d) (hend : m (Fin.last r)=1) (k : ℕ) (h : ℝ) :
    activeCountMean M Q (terminalTower false (FiniteLaw.uniform : FiniteLaw Spin) r)
      (fun b => pad a r (U b)) (terminalState r)
      (fun b y => x b (pathPrefix r y)) m (Fin.last q)
      (fun y => h*spin (terminalState r y)) k=
    ∫ z : Fin k → InteractionSample (q+1),
      trialLog r (finiteTrialLaw r Q U x) (fun d => m d.castSucc) (siteLog z h)
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) := by
  let F := fun z : RootPath (InteractionSample (q+1)) k × RootPath (Fin (q+1) → R) k =>
    backwardLog (r+1)
      (cavityTower (terminalTower false (FiniteLaw.uniform : FiniteLaw Spin) r)
        (fun b => pad a r (U b)) k z.2) m
      (activeEnergy (terminalState r) (fun b y => x b (pathPrefix r y)) (Fin.last q) k z.2 z.1
        (fun y => h*spin (terminalState r y)))
  have hFm : Measurable F := by
    apply measurable_from_prod_countable_left
    intro b
    dsimp only [F]
    exact measurable_backwardLog (r+1) _ m (measurable_activeEnergy (terminalState r)
      (fun b y => x b (pathPrefix r y)) (Fin.last q) k b id measurable_id
      (fun y => h*spin (terminalState r y)))
  have hB (z : RootPath (InteractionSample (q+1)) k × RootPath (Fin (q+1) → R) k) :
      |F z|≤|h|+∑ i,‖(rootArray k z.1 i).1‖ := by
    apply backwardLog_bound _ _ _ hm
    intro y
    apply activeEnergy_bound _ _ _ _ _ _ _ _ y
    intro y
    simp only [abs_mul,abs_spin,mul_one]
    exact le_refl _
  have hi : Integrable F ((rootLaw k (fun _ => M.disorder.toMeasure)).prod
      (rootLaw k (fun _ => ((FiniteLaw.pi (fun _ : Fin (q+1) => Q)).asProbability id).toMeasure))) := by
    exact ((integrable_const |h|).add ((integrable_rootArray_sum M.disorder.toMeasure
      (fun a => ‖a.1‖) hM.interaction_integrable k).comp_fst _)).mono'
        hFm.aestronglyMeasurable (ae_of_all _ hB)
  unfold activeCountMean activeDatumRoot
  change (∫ z,F (rootMap Prod.fst k z,rootMap Prod.snd k z) ∂rootLaw k (fun _ => _))=_
  rw [integral_rootSplit _ _ k F hFm hi]
  have he (z : RootPath (InteractionSample (q+1)) k) :
      (∫ b,F (z,b) ∂rootLaw k (fun _ => ((FiniteLaw.pi (fun _ : Fin (q+1) => Q)).asProbability id).toMeasure))=
      trialLog r (finiteTrialLaw r Q U x) (fun d => m d.castSucc) (siteLog (rootArray k z) h) :=
    activeRoot_site_mean a r Q U x m hend q k z h
  simp only [he]
  exact integral_rootArray_eq_pi M.disorder.toMeasure k
    (fun z : Fin k → InteractionSample (q+1) =>
      trialLog r (finiteTrialLaw r Q U x) (fun d => m d.castSucc) (siteLog z h))

end DilutedSpinGlass.PrescribedTree

end

end OAI
