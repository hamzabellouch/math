import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.UniformDerivatives

namespace OAI

noncomputable section
namespace VelocityDetection.TimeIntegral
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {K L : ℝ → ℝ → E}

omit [CompleteSpace E] in
theorem hasDerivAt_parameter (hK : Continuous (uncurry K)) (hL : Continuous (uncurry L))
    (hd : ∀ t r, HasDerivAt (fun s => K s r) (L t r) t) (a b t : ℝ) :
    HasDerivAt (fun s => ∫ r in a..b, K s r) (∫ r in a..b, L t r) t := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn
    (s := Icc (t-1) (t+1) ×ˢ uIcc a b) hL.continuousOn
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := K) (F' := L) (bound := fun _ => C) (s := Ioo (t-1) (t+1))
      (Ioo_mem_nhds (by linarith) (by linarith))
      (Eventually.of_forall (fun s => (hK.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable))
      ((hK.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b)
      ((hL.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall (fun r hr s hs => hC (s,r) ⟨⟨hs.1.le, hs.2.le⟩, uIoc_subset_uIcc hr⟩))
      intervalIntegrable_const
      (Eventually.of_forall (fun r _ s _ => hd s r))).2

theorem hasDerivAt_diagonal (hK : Continuous (uncurry K)) (hL : Continuous (uncurry L))
    (hd : ∀ t r, HasDerivAt (fun s => K s r) (L t r) t) (a t : ℝ) :
    HasDerivAt (fun s => ∫ r in a..s, K s r)
      ((∫ r in a..t, L t r) + K t t) t := by
  let P : ℝ → ℝ → E := fun s b => ∫ r in a..b, K s r
  let Q : ℝ → ℝ → ℝ →L[ℝ] E := fun s b =>
    (1 : ℝ →L[ℝ] ℝ).smulRight (∫ r in a..b, L s r)
  let R : ℝ → ℝ → ℝ →L[ℝ] E := fun s b => (1 : ℝ →L[ℝ] ℝ).smulRight (K s b)
  have dQ : ∀ s b, HasFDerivAt (fun x => P x b) (Q s b) s := by
    intro s b
    exact (hasDerivAt_parameter hK hL hd a b s).hasFDerivAt
  have dR : ∀ s b, HasFDerivAt (P s) (R s b) b := by
    intro s b
    have hc : Continuous (K s) := hK.comp (continuous_const.prodMk continuous_id)
    exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable a b)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).hasFDerivAt
  have cQ : Continuous (uncurry Q) := by
    apply (ContinuousLinearMap.smulRightL ℝ ℝ E 1).continuous.comp
    exact intervalIntegral.continuous_parametric_primitive_of_continuous hL
  have cR : Continuous (uncurry R) :=
    (ContinuousLinearMap.smulRightL ℝ ℝ E 1).continuous.comp hK
  have hh := (hasStrictFDerivAt_uncurry_coprod (f := P) (f₁ := Q) (f₂ := R) (u := (t,t))
    (Eventually.of_forall (fun p => dQ p.1 p.2))
    (Eventually.of_forall (fun p => dR p.1 p.2)) cQ.continuousAt cR.continuousAt).hasFDerivAt
  have hc := hh.comp_hasDerivAt (f := fun s : ℝ => (s,s)) t ((hasDerivAt_id t).prodMk (hasDerivAt_id t))
  change HasDerivAt (fun s => ∫ r in a..s, K s r) (Q t t 1 + R t t 1) t at hc
  simpa only [Q, R, ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] using hc

end VelocityDetection.TimeIntegral
end

end OAI
