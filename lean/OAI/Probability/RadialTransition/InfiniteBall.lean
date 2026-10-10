import OAI.Probability.RadialTransition.InitialSeparation

namespace OAI

noncomputable section
open scoped BigOperators NNReal
open Set Filter
namespace RadialTransition

lemma exists_family_pressure_ball :
    ∃ t b : ℝ, 1 ≤ t ∧ 2 ≤ b ∧
      2197*t*bumpIntegral⁻¹*iterationBudget ≤ (t^2/8)/8 ∧
      ∃ x ∈ phaseWindow (1/8), Metric.closedBall targetSlope pressureRadius ⊆
        supportSet (onParameters (grandPressure (familyPotential t (iterationMass b) (scaleRange b)) t)) positiveParameters x := by
  have hinitE := initial_separation phaseRadius_pos (show 0<pressureRadius/64 by have := pressureRadius_pos; positivity)
  obtain ⟨t,⟨⟨⟨hinit,ht⟩,htA⟩,htrow⟩⟩ := (hinitE.and (eventually_ge_atTop (1:ℝ)) |>.and
    (eventually_ge_atTop (6912*iterationBudget)) |>.and
    (eventually_ge_atTop (140608*bumpIntegral⁻¹*iterationBudget))).exists
  have ht0 : 0 < t := by linarith
  have hrow : 2197*t*bumpIntegral⁻¹*iterationBudget ≤ (t^2/8)/8 := by
    have hh := mul_le_mul_of_nonneg_left htrow ht0.le
    nlinarith only [hh]
  obtain ⟨U,C,C₀,hU,hC,hC₀,hcontrol⟩ := family_controls ht iterationBudget_pos.le htA hrow
  obtain ⟨D,K,hD,hK,hkac⟩ := family_kac_uniform ht (by norm_num : (0:ℝ)<1/2)
    (by norm_num : (1/2:ℝ)≤3/2) (by norm_num : (0:ℝ)≤2) iterationBudget_pos.le htA
  obtain ⟨b,k,l,hb,hbK,hk,hl,hdom,hrad,hband,hpress⟩ :=
    scale_budgets (K := K) (by linarith : 0≤U) (by linarith : 0≤C) hC₀ (show 0<2*D by positivity)
  have had := iteration_admissible hb t
  have hpre (n : ℕ) := reversePrefix_admissible (t := t) had.1 had.2.1 had.2.2.1 had.2.2.2 n
  have hmass (n : ℕ) : iterationMass b n ∈ Ioc (0:ℝ) iterationBudget :=
    ⟨iterationMass_pos (by linarith) n,iterationMass_le hb n⟩
  have hctrl (n : ℕ) := hcontrol _ _ (hpre n) _ (hmass n)
  have hP (n : ℕ) : ConvexOn ℝ positiveParameters (onParameters (iterationP t b n)) :=
    convexOn_idealAttraction (admissible_pressure_convex ht (hpre n) hrow) (hctrl n).1
  have hQ (n : ℕ) : ConvexOn ℝ positiveParameters (onParameters (iterationQ t b n)) :=
    admissible_pressure_convex ht (hpre (n+1)) hrow
  have happ := iteration_kac ht hD hK hb hbK hrow hkac
  have hlip (n : ℕ) (x : Parameter) (hx : x ∈ phaseWindow (1/4))
      (y : Parameter) (hy : y ∈ phaseWindow (1/4)) :
      |onParameters (iterationP t b n) x-onParameters (iterationP t b n) y| ≤ C*dist x y :=
    (hctrl n).2.2.1 x hx y hy
  have hinc (n : ℕ) (x : Parameter) (hx : x ∈ phaseWindow (1/4)) :
      |onParameters (iterationP t b (n+1)) x-onParameters (iterationQ t b n) x| ≤ C₀*scaleTail b n := by
    have hh := (hctrl (n+1)).2.2.2 x hx
    change 0 ≤ onParameters (iterationP t b (n+1)) x-onParameters (iterationQ t b n) x ∧
      onParameters (iterationP t b (n+1)) x-onParameters (iterationQ t b n) x ≤ C₀*scaleTail b n at hh
    rw [abs_of_nonneg hh.1]
    exact hh.2
  have hball : ∀ n, ∃ x ∈ Metric.ball phaseCenter (1/8), Metric.closedBall targetSlope pressureRadius ⊆
      supportSet (onParameters (iterationP t b n)) positiveParameters x := by
    apply multiscale_pressure_balls (fun n => scaleTail_pos (by linarith) n)
      (fun n => show 0≤2*D*(scaleTail b n)^2 by positivity) (by linarith : 0≤U)
      (by linarith : 0≤C) hk hl hP hQ (iterationP_succ t b) happ hlip hinc
      (fun n => (hctrl (n+1)).1) (fun n => (hctrl (n+1)).2.1) ?_ hdom hrad hband hpress
    intro x hx
    rw [iterationP_zero]
    exact ⟨(hinit x hx).2,(hinit x hx).1⟩
  have hlim (x : Parameter) (hx : x ∈ phaseWindow (1/4)) :
      Tendsto (fun n => onParameters (iterationP t b n) x) atTop
        (nhds (onParameters (grandPressure (familyPotential t (iterationMass b) (scaleRange b)) t) x)) := by
    have hβ : 0 < x 0 := phaseWindow_positive (by norm_num) hx
    have hlimQ := (grandPressure_reversePrefix_tendsto (h := x 1) ht hβ had hrow).comp (tendsto_add_atTop_nat 1)
    have hdiff : Tendsto (fun n => onParameters (iterationP t b n) x-onParameters (iterationQ t b n) x) atTop (nhds 0) := by
      apply squeeze_zero_norm (a := fun n => 2*D*(scaleTail b n)^2)
      · intro n
        simpa only [Real.norm_eq_abs,abs_sub_comm] using happ n x hx
      · simpa using ((summable_scaleTail hb).tendsto_atTop_zero.pow 2).const_mul (2*D)
    have hsum := hdiff.add hlimQ
    simpa only [Function.comp_apply,onParameters,iterationQ,sub_add_cancel,zero_add] using hsum
  exact ⟨t,b,ht,hb,hrow,pressure_ball_limit (admissible_pressure_convex ht had hrow) hball hlip hlim⟩

end RadialTransition
end

end OAI
