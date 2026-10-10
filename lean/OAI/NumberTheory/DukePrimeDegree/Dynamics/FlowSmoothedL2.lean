import OAI.NumberTheory.DukePrimeDegree.Dynamics.FlowWindowAverages
import OAI.NumberTheory.DukePrimeDegree.Dynamics.FiniteKoopmanAverages
import OAI.NumberTheory.DukePrimeDegree.Dynamics.OrbitAverageFunctions

namespace OAI

/-!
# Mean convergence for a real flow without time-one ergodicity

Unit smoothing removes the possible nonconstant time-one invariant
vectors. The boundary estimate makes the Hilbert-space limit invariant
under every real time, and ergodicity of the entire flow then makes it
constant. This is the averaging statement needed on actual ergodic
components of a root flow.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree

variable {X : Type*} [MulAction (Multiplicative ℝ) X]

def realActionTime (s : ℝ) (x : X) : X := Multiplicative.ofAdd s • x

lemma realActionTime_zero (x : X) : realActionTime 0 x = x := by
  simp [realActionTime]

lemma realActionTime_add (s t : ℝ) (x : X) :
    realActionTime (s + t) x = realActionTime s (realActionTime t x) := by
  simp only [realActionTime, ofAdd_add, mul_smul]

variable [MeasurableSpace X] [MeasurableConstSMul (Multiplicative ℝ) X]

/-- Flow ergodicity, with no ergodicity assumption on its time-one map. -/
theorem L2_unit_smoothed_real_action_tendsto_integral
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul (Multiplicative ℝ) X μ]
    (f : X → ℝ) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, |f x| ≤ C)
    (hint : ∀ x a b, IntervalIntegrable
      (fun t => f (realActionTime t x)) volume a b)
    (hg : MemLp (unitFlowSmooth realActionTime f) 2 μ) :
    Tendsto (fun N => birkhoffAverage ℝ
      (Lp.compMeasurePreserving (realActionTime 1)
        (measurePreserving_smul (Multiplicative.ofAdd 1) μ)) id N
      (hg.toLp (unitFlowSmooth realActionTime f))) atTop
      (𝓝 (constantL2 μ (∫ x, unitFlowSmooth realActionTime f x ∂μ))) := by
  let T : X → X := realActionTime 1
  have hT : MeasurePreserving T μ μ := measurePreserving_smul (Multiplicative.ofAdd 1) μ
  let g : X → ℝ := unitFlowSmooth realActionTime f
  let F : Lp ℝ 2 μ := hg.toLp g
  let V : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    (Lp.compMeasurePreservingₗᵢ ℝ T hT).toContinuousLinearMap
  have hVe : (V : Lp ℝ 2 μ → Lp ℝ 2 μ) = Lp.compMeasurePreserving T hT := by
    funext v
    rfl
  let A (N : ℕ) : Lp ℝ 2 μ := birkhoffAverage ℝ V id N F
  have hV : ‖V‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    change ‖Lp.compMeasurePreserving T hT v‖ ≤ 1 * ‖v‖
    simpa only [one_mul] using (Lp.norm_compMeasurePreserving v hT).le
  let S := V.eqLocus (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
  let q : Lp ℝ 2 μ := S.orthogonalProjectionOnto F
  have hA : Tendsto A atTop (𝓝 q) := V.tendsto_birkhoffAverage_orthogonalProjection hV F
  have hrep (N : ℕ) : (A N : X → ℝ) =ᵐ[μ] birkhoffAverage ℝ T g N :=
    (Lp_orbit_average_ae μ T hT F N).trans
      (orbit_average_congr_ae μ T hT hg.coeFn_toLp N)
  have hfixed (s : ℝ) :
      Lp.compMeasurePreserving (realActionTime s)
        (measurePreserving_smul (Multiplicative.ofAdd s) μ) q = q := by
    have hs := measurePreserving_smul (Multiplicative.ofAdd s) μ
    let W : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
      (Lp.compMeasurePreservingₗᵢ ℝ (realActionTime s) hs).toContinuousLinearMap
    have hb (N : ℕ) : ‖W (A N) - A N‖ ≤ (N : ℝ)⁻¹ * (2 * C * |s|) := by
      have hWA : (W (A N) : X → ℝ) =ᵐ[μ] fun x => A N (realActionTime s x) := by
        change (Lp.compMeasurePreserving (realActionTime s) hs (A N) : X → ℝ) =ᵐ[μ] _
        exact Lp.coeFn_compMeasurePreserving (A N) hs
      have hp : ∀ᵐ x ∂μ, ‖(W (A N) - A N) x‖ ≤ (N : ℝ)⁻¹ * (2 * C * |s|) := by
        filter_upwards [Lp.coeFn_sub (W (A N)) (A N),
          hWA,
          hs.quasiMeasurePreserving.ae_eq_comp (hrep N), hrep N] with x hsub hcomp hshift hplain
        change A N (realActionTime s x) = birkhoffAverage ℝ T g N (realActionTime s x) at hshift
        rw [hsub, Pi.sub_apply, hcomp, hshift, hplain, Real.norm_eq_abs]
        exact birkhoffAverage_unitFlowSmooth_shift_bound realActionTime f
          realActionTime_zero realActionTime_add hint C hC N s x
      simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (by positivity) hp
    have hbzero : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (2 * C * |s|)) atTop (𝓝 0) := by
      simpa only [div_eq_inv_mul] using
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
          Tendsto (fun N : ℕ => (2 * C * |s|) / (N : ℝ)) atTop (𝓝 0))
    have hzero : Tendsto (fun N => W (A N) - A N) atTop (𝓝 0) :=
      squeeze_zero_norm hb hbzero
    have hq := (W.continuous.tendsto q |>.comp hA).sub hA
    exact sub_eq_zero.mp (tendsto_nhds_unique hq hzero)
  have hqae : ∀ a : Multiplicative ℝ, (fun x => q (a • x)) =ᵐ[μ] (q : X → ℝ) := by
    intro a
    have he := (Lp.coeFn_compMeasurePreserving q
      (measurePreserving_smul a μ)).symm
    have hf := hfixed a.toAdd
    change Lp.compMeasurePreserving (fun x => a • x)
      (measurePreserving_smul a μ) q = q at hf
    rwa [hf] at he
  obtain ⟨c, hc⟩ := ae_eq_const_of_group_invariant μ q (Lp.aestronglyMeasurable q) hqae
  have hqconst : q = constantL2 μ c := Lp.ext (hc.trans (constantL2_ae μ c).symm)
  rw [hqconst] at hA
  have hmean := (meanL2 μ).continuous.tendsto (constantL2 μ c) |>.comp hA
  have hconst : Tendsto (fun N => meanL2 μ (A N)) atTop (𝓝 (meanL2 μ F)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact (meanL2_birkhoffAverage μ T hT F N (Nat.ne_of_gt hN)).symm
  have hcmean := tendsto_nhds_unique hmean hconst
  rw [meanL2_constant, meanL2_apply] at hcmean
  have hFg : (∫ x, F x ∂μ) = ∫ x, g x ∂μ := integral_congr_ae hg.coeFn_toLp
  rw [hFg] at hcmean
  simpa only [A, hVe, F, g, T, hcmean] using hA

end DukePrimeDegree

end

end OAI
