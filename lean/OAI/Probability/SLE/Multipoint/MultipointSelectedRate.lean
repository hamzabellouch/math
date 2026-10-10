import OAI.Probability.SLE.Multipoint.MultipointDiscountProcess
import OAI.Probability.SLE.Multipoint.MultipointStagedRate
import OAI.Probability.SLE.Multipoint.MultipointLocalizedStages

namespace OAI

/-! A bounded progressive discount rate that agrees with the actual
four-phase product cost before localization. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SLEExactGauge.Multipoint

theorem exists_localized_discount_rate
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (Q : ℝ → Ω → ι → ℂ × ℝ)
    (hQm : Measurable (fun p : ℝ × Ω => Q p.1 p.2))
    (hQa : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t : ℝ≥0 => Q t)) (hQc : ∀ ω, Continuous (fun t => Q t ω))
    (κ β : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) (a U : ι → ℝ)
    (ρ : (ι × Fin 3) → Ω → ℝ≥0) (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (hlstop : ∀ σ ∈ l, IsStoppingTime
      (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hlbound : ∀ σ ∈ l, ∀ ω, σ ω ≤ H+1) (hρmem : ∀ k, ρ k ∈ l)
    (hzero : (fun _ : Ω => (0 : ℝ≥0)) ∈ l)
    (χ : Ω → ℝ≥0)
    (hχstop : IsStoppingTime
      (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (χ ω : WithTop ℝ≥0))) (hχbound : ∀ ω, χ ω ≤ H)
    (R : ℝ) (hR : 0 ≤ R)
    (hnorm : ∀ ω t, t ≤ χ ω → ‖(Q t ω,B t ω)‖ ≤ R) :
    ∃ (r : ℝ≥0 → Ω → ℝ) (C : ℝ≥0),
      Measurable (Function.uncurry r) ∧
      IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) r ∧
      (∀ t ω, 0 ≤ r t ω ∧ |r t ω| ≤ C) ∧
      (∀ ω t, t < χ ω → r t ω =
        productDriftCost (patternActiveSet (phaseAt ρ t ω)) κ
          (fun i => phaseRegulatorScale β (a i) (U i) (phaseAt ρ t ω i))
          (fun i => phaseRegulatorSlope β (phaseAt ρ t ω i)) (Q t ω) (B t ω)) := by
  classical
  have hex (A : Finset (ι × Fin 3)) := exists_bounded_discount_cost_process B hm hBm hBc
    Q hQm hQa hQc (patternActiveSet (phaseOfPattern A)) κ hκ hκ8
    (fun i => phaseRegulatorScale β (a i) (U i) (phaseOfPattern A i))
    (fun i => phaseRegulatorSlope β (phaseOfPattern A i))
    (fun i _ => phaseRegulatorScale_pos _ _ _ _) R hR
  choose g C hgm hgp hgc hgb hge using hex
  let τ := localizedStage l H χ
  have hτ (n : ℕ) := localizedStage_stopping _ l hlstop H χ hχstop n
  have hρstop (k : ι × Fin 3) := hlstop (ρ k) (hρmem k)
  let r := stagedPatternRate l.length Finset.univ ρ τ g
  let C₀ : ℝ≥0 := ∑ k ∈ (Finset.range l.length).product (Finset.univ : Finset (ι × Fin 3)).powerset, C k.2
  refine ⟨r,C₀,?_,?_,?_,?_⟩
  · exact stagedPatternRate_measurable _ l.length Finset.univ ρ τ
      (fun i _ => hρstop i) hτ g (fun A _ => hgm A)
  · exact stagedPatternRate_progressive _ l.length Finset.univ ρ τ
      (fun i _ => hρstop i) hτ g (fun A _ => hgp A)
  · intro t ω
    exact ⟨stagedPatternRate_nonneg l.length Finset.univ ρ τ g
      (fun A _ u ω => (hgb A u ω).1) t ω,
      stagedPatternRate_bound l.length Finset.univ ρ τ g C
        (fun A _ u ω => (hgb A u ω).2) t ω⟩
  · intro ω t htχ
    obtain ⟨n,hn,hnt,htn⟩ := exists_finite_stage (fun n => τ n ω) l.length t
      (by rw [show τ 0 ω = 0 from localizedStage_zero l H χ hlbound hzero ω]; exact bot_le)
      (by rwa [show τ l.length ω = χ ω from localizedStage_last l H χ hχbound ω])
    obtain ⟨A,hA,hω⟩ := switchPatternEvent_cover Finset.univ ρ (τ n) ω
    have hphase : phaseAt ρ t ω = phaseOfPattern A :=
      (phaseAt_const_localized_interval ρ l H χ hlbound hρmem n ω t hnt htn).trans
        (phaseAt_of_pattern ρ (τ n) A hω)
    change stagedPatternRate l.length Finset.univ ρ τ g t ω = _
    rw [stagedPatternRate_eq l.length Finset.univ ρ τ g
      (localizedStage_monotone l H χ hlbound) n hn A hA t ω hω hnt htn,
      hge A t ω (hnorm ω t htχ.le), hphase]

end SLEExactGauge.Multipoint

end

end OAI
