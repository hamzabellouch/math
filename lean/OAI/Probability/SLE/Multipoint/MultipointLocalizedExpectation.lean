import OAI.Probability.SLE.Multipoint.MultipointLocalizedStages
import OAI.Probability.SLE.Multipoint.MultipointPatternExpectation

namespace OAI

/-! Optional stopping for the complete four-phase product, including
simultaneous switches and a separate random localization time. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SLEExactGauge.Multipoint

theorem localized_pattern_expectation_le
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (Q V : ℝ → Ω → (ι → ℂ × ℝ)) (L : ℝ≥0)
    (hQm : Measurable (fun p : ℝ × Ω => Q p.1 p.2))
    (hQa : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t : ℝ≥0 => Q t))
    (hQl : ∀ ω, LipschitzWith L (fun t => Q t ω))
    (hVm : Measurable (fun p : ℝ × Ω => V p.1 p.2))
    (hVb : ∀ t ω, ‖V t ω‖ ≤ L)
    (hQd : ∀ ω, ∀ᵐ t : ℝ, 0 < t → HasDerivAt (fun u => Q u ω) (V t ω) t)
    (r : ℝ≥0 → Ω → ℝ) (hrm : Measurable (Function.uncurry r))
    (hrp : IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) r)
    (C : ℝ≥0) (hrb : ∀ t ω, |r t ω| ≤ C)
    (κ β : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (a U : ι → ℝ) (hU : ∀ i, 0 ≤ U i)
    (ρ : (ι × Fin 3) → Ω → ℝ≥0) (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (hlstop : ∀ σ ∈ l, IsStoppingTime
      (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hlbound : ∀ σ ∈ l, ∀ ω, σ ω ≤ H+1) (hρmem : ∀ k, ρ k ∈ l)
    (hρorder : ∀ ω i, Monotone (fun k => ρ (i,k) ω))
    (hzero : (fun _ : Ω => (0 : ℝ≥0)) ∈ l)
    (χ : Ω → ℝ≥0)
    (hχstop : IsStoppingTime
      (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (χ ω : WithTop ℝ≥0))) (hχbound : ∀ ω, χ ω ≤ H)
    (R : ℝ) (hR : 0 ≤ R)
    (hnorm : ∀ ω t, 0 ≤ t → t ≤ (χ ω : ℝ) →
      ‖((Q t ω,discountClock r t ω),B t.toNNReal ω)‖ ≤ R)
    (hδ : ∀ ω (t : ℝ≥0), t < χ ω → ∀ i ∈ patternActiveSet (phaseAt ρ t ω),
      branchRegulator κ (phaseRegulatorScale β (a i) (U i) (phaseAt ρ t ω i))
        (phaseRegulatorSlope β (phaseAt ρ t ω i)) (Q t ω i) ≤ 1)
    (hV : ∀ ω (t : ℝ≥0), t < χ ω → ∀ i ∈ patternActiveSet (phaseAt ρ t ω),
      V t ω i = physicalLogLoewnerField (Real.sqrt κ*B t ω) (Q t ω i))
    (hr : ∀ ω (t : ℝ≥0), t < χ ω → r t ω =
      productDriftCost (patternActiveSet (phaseAt ρ t ω)) κ
        (fun i => phaseRegulatorScale β (a i) (U i) (phaseAt ρ t ω i))
        (fun i => phaseRegulatorSlope β (phaseAt ρ t ω i)) (Q t ω) (B t ω))
    (hclock : ∀ ω i (k : Fin 3), ρ (i,k) ω ≤ χ ω →
      logFactorClock κ (Q (ρ (i,k) ω) ω i)-a i =
        if k = 0 then 0 else if k = 1 then U i/2 else U i) :
    Integrable (fun ω => discountedPatternProduct κ β a U (phaseAt ρ (χ ω) ω)
      (Q (χ ω) ω,discountClock r (χ ω) ω) (B (χ ω) ω)) P ∧
    (∫ ω, discountedPatternProduct κ β a U (phaseAt ρ (χ ω) ω)
      (Q (χ ω) ω,discountClock r (χ ω) ω) (B (χ ω) ω) ∂P) ≤
      ∫ ω, discountedPatternProduct κ β a U (phaseAt ρ 0 ω)
        (Q 0 ω,discountClock r 0 ω) (B 0 ω) ∂P := by
  classical
  let τ := localizedStage l H χ
  let j := fun n ω => phaseAt ρ (τ n ω) ω
  let X := fun n ω => discountedPatternProduct κ β a U (j n ω)
    (Q (τ n ω) ω,discountClock r (τ n ω) ω) (B (τ n ω) ω)
  let Y := fun n ω => discountedPatternProduct κ β a U (j n ω)
    (Q (τ (n+1) ω) ω,discountClock r (τ (n+1) ω) ω) (B (τ (n+1) ω) ω)
  have hτ (n : ℕ) := localizedStage_stopping _ l hlstop H χ hχstop n
  have hmono (ω : Ω) := localizedStage_monotone l H χ hlbound ω
  have hρstop (k : ι × Fin 3) := hlstop (ρ k) (hρmem k)
  have hstep (n : ℕ) : Integrable (Y n) P ∧ Integrable (X n) P ∧
      (∫ ω, Y n ω ∂P) ≤ ∫ ω, X n ω ∂P := by
    let F := fun (A : Finset (ι × Fin 3)) ω =>
      discountedPatternProduct κ β a U (phaseOfPattern A)
        (Q (τ (n+1) ω) ω,discountClock r (τ (n+1) ω) ω) (B (τ (n+1) ω) ω)
    let G := fun (A : Finset (ι × Fin 3)) ω =>
      discountedPatternProduct κ β a U (phaseOfPattern A)
        (Q (τ n ω) ω,discountClock r (τ n ω) ω) (B (τ n ω) ω)
    have hb (A : Finset (ι × Fin 3)) :
        IntegrableOn (F A) (switchPatternEvent Finset.univ ρ (τ n) A) P ∧
        IntegrableOn (G A) (switchPatternEvent Finset.univ ρ (τ n) A) P ∧
        (∫ ω in switchPatternEvent Finset.univ ρ (τ n) A, F A ω ∂P) ≤
          ∫ ω in switchPatternEvent Finset.univ ρ (τ n) A, G A ω ∂P := by
      let s := patternActiveSet (phaseOfPattern A)
      let D := fun i => phaseRegulatorScale β (a i) (U i) (phaseOfPattern A i)
      let σ := fun i => phaseRegulatorSlope β (phaseOfPattern A i)
      have hD (i) (_ : i ∈ s) : 0 < D i := phaseRegulatorScale_pos _ _ _ _
      obtain ⟨φ,K,_,he,heD,he2,hfield⟩ := compact_discounted_smooth_field B hm
        Q V L hQm hQa hQl hVm hVb hQd r hrm hrp C hrb s κ D σ hD R hR
      have hphase (ω : Ω) (hω : ω ∈ switchPatternEvent Finset.univ ρ (τ n) A)
          (u : ℝ) (hu : (τ n ω : ℝ) ≤ u) (hu' : u < (τ (n+1) ω : ℝ)) :
          phaseAt ρ u.toNNReal ω = phaseOfPattern A := by
        have hu0 := (τ n ω).coe_nonneg.trans hu
        have ht : τ n ω ≤ u.toNNReal := by exact_mod_cast (show (τ n ω : ℝ) ≤
          (u.toNNReal : ℝ) by simpa only [Real.coe_toNNReal u hu0] using hu)
        have ht' : u.toNNReal < τ (n+1) ω := by exact_mod_cast (show
          (u.toNNReal : ℝ) < (τ (n+1) ω : ℝ) by simpa only [Real.coe_toNNReal u hu0] using hu')
        exact (phaseAt_const_localized_interval ρ l H χ hlbound hρmem n ω _ ht ht').trans
          (phaseAt_of_pattern ρ (τ n) A hω)
      have huχ (ω : Ω) (u : ℝ) (hu : (τ n ω : ℝ) ≤ u)
          (hu' : u < (τ (n+1) ω : ℝ)) : u.toNNReal < χ ω := by
        have hu0 := (τ n ω).coe_nonneg.trans hu
        have hlt : (u.toNNReal : ℝ) < (χ ω : ℝ) := by
          rw [Real.coe_toNNReal u hu0]
          exact hu'.trans_le (by exact_mod_cast localizedStage_le l H χ (n+1) ω)
        exact_mod_cast hlt
      have hb := discounted_product_optional_interval_le hB hm hBm hBc Q V r s κ hκ hκ8
        D σ hD (fun i _ => phaseRegulatorSlope_le_one hβ hβ1 _) φ K hfield R he heD he2
        (τ n) (τ (n+1)) (hτ n) (hτ (n+1)) (fun ω => hmono ω (Nat.le_succ n)) H
        (fun ω => (localizedStage_le l H χ (n+1) ω).trans (hχbound ω))
        (switchPatternEvent_measurable _ Finset.univ ρ (τ n) (fun i _ => hρstop i) (hτ n) A)
        (fun ω _ u hu hu' => hnorm ω u ((τ n ω).coe_nonneg.trans hu)
          (hu'.trans (by exact_mod_cast localizedStage_le l H χ (n+1) ω)))
        (fun ω hω u hu hu' => by
          have hh := hδ ω u.toNNReal (huχ ω u hu hu')
          rw [hphase ω hω u hu hu'] at hh
          simpa only [Real.coe_toNNReal u ((τ n ω).coe_nonneg.trans hu)] using hh)
        (fun ω hω u hu hu' => by
          have hh := hV ω u.toNNReal (huχ ω u hu hu')
          rw [hphase ω hω u hu hu'] at hh
          simpa only [Real.coe_toNNReal u ((τ n ω).coe_nonneg.trans hu)] using hh)
        (fun ω hω u hu hu' => by
          have hh := hr ω u.toNNReal (huχ ω u hu hu')
          rw [hphase ω hω u hu hu'] at hh
          simpa only [Real.coe_toNNReal u ((τ n ω).coe_nonneg.trans hu)] using hh)
      refine ⟨?_,?_,?_⟩
      · simpa only [F,discountedPatternProduct_eq,s,D,σ,IntegrableOn] using hb.1.const_mul (patternWeight κ a U (phaseOfPattern A))
      · simpa only [G,discountedPatternProduct_eq,s,D,σ,IntegrableOn] using hb.2.1.const_mul (patternWeight κ a U (phaseOfPattern A))
      · simpa only [F,G,discountedPatternProduct_eq,integral_const_mul,s,D,σ] using
          mul_le_mul_of_nonneg_left hb.2.2 (patternWeight_pos κ a U (phaseOfPattern A)).le
    apply switchPattern_integral_le P Finset.univ ρ (τ n)
      (fun A _ => (hτ n).measurableSpace_le _
        (switchPatternEvent_measurable _ Finset.univ ρ (τ n) (fun i _ => hρstop i) (hτ n) A)) F G (Y n) (X n)
      (fun A _ => (hb A).1) (fun A _ => (hb A).2.1)
    · intro A _ ω hω
      change discountedPatternProduct κ β a U (phaseOfPattern A) _ _ =
        discountedPatternProduct κ β a U (phaseAt ρ (τ n ω) ω) _ _
      rw [phaseAt_of_pattern ρ (τ n) A hω]
    · intro A _ ω hω
      change discountedPatternProduct κ β a U (phaseOfPattern A) _ _ =
        discountedPatternProduct κ β a U (phaseAt ρ (τ n ω) ω) _ _
      rw [phaseAt_of_pattern ρ (τ n) A hω]
    · exact fun A _ => (hb A).2.2
  have hjump (n : ℕ) (ω : Ω) : X (n+1) ω ≤ Y n ω := by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply patternProduct_switch_le κ β hκ hκ8 a U hU _ _ _ _
      (fun i => phaseAt_monotone ρ ω i (hmono ω (Nat.le_succ n)))
    · intro i hbefore hafter
      have hc := phaseAt_crossed_localized_switch ρ l H χ hlbound hρmem n ω i
        (0: Fin 3) (hρorder ω i) hbefore hafter
      have hh := hclock ω i (0: Fin 3) (hc ▸ localizedStage_le l H χ (n+1) ω)
      rw [hc] at hh
      simpa only [ite_true, ite_false, Fin.isValue, Fin.reduceEq] using hh
    · intro i hbefore hafter
      have hc := phaseAt_crossed_localized_switch ρ l H χ hlbound hρmem n ω i
        (1: Fin 3) (hρorder ω i) hbefore hafter
      have hh := hclock ω i (1: Fin 3) (hc ▸ localizedStage_le l H χ (n+1) ω)
      rw [hc] at hh
      simpa only [ite_true, ite_false, Fin.isValue, Fin.reduceEq] using hh
    · intro i hbefore hafter
      have hc := phaseAt_crossed_localized_switch ρ l H χ hlbound hρmem n ω i
        (2: Fin 3) (hρorder ω i) hbefore hafter
      have hh := hclock ω i (2: Fin 3) (hc ▸ localizedStage_le l H χ (n+1) ω)
      rw [hc] at hh
      simpa only [ite_true, ite_false, Fin.isValue, Fin.reduceEq] using hh
  have hout := finite_switched_product_expectation_le P l.length X Y
    (fun n _ => (hstep n).2.1) (fun n _ => (hstep n).1)
    (fun n _ => (hstep n).2.2) (fun n _ => hjump n)
  have hlast : ∀ ω, τ l.length ω = χ ω := localizedStage_last l H χ hχbound
  have hfirst : ∀ ω, τ 0 ω = 0 := localizedStage_zero l H χ hlbound hzero
  refine ⟨?_,?_⟩
  · simpa only [X,j,hlast] using (hstep l.length).2.1
  · simpa only [X,j,hlast,hfirst,NNReal.coe_zero] using hout

end SLEExactGauge.Multipoint

end

end OAI
