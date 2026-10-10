import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationCompiledBudget

namespace OAI

noncomputable section
open scoped BigOperators SchwartzMap
namespace Ostmann.Characters.TemplateOneSidedCancellation
open Filter
attribute [local instance] Classical.propDecidable

theorem eventually_compiled_oneSided_scale_gap
    {τ : Type*} [Fintype τ] (C z : ℝ) (d : ℕ)
    {α β γ c : ℝ} (hC : 0 ≤ C) (hz : 0 ≤ z) (hα : 0 < α)
    (hαβ : α ≤ β) (hβγ : β < γ) (hc : 0 < c) :
    ∃ δ : ℝ,0 < δ ∧ ∀ᶠ L : ℝ in atTop,
    ∀ {η κ σ : Type} [Fintype η] [Fintype κ] [Fintype σ],
    ∀ (ρ : 𝓢(ℝ,ℂ)) (q : κ → ℕ) (_hq : ∀ j,(q j).Prime) (_hinj : Function.Injective q)
      (χ : ∀ j,MulChar (ZMod (q j)) ℂ) (_hχ : ∀ j,χ j ≠ 1)
      (Q N : ℕ) (a : η → ℕ) (_hQ : ∀ j,Q.Coprime (q j))
      (μ : η × Fin N → ℝ) (ν : κ → ℝ)
      (U : η × Fin N → ℂ) (V : κ → ℂ)
      (E b₀ : ℝ) (_hE : 0 ≤ E) (_hb : 0 < b₀)
      (_hN : (N : ℝ) ≤ 3*b₀)
      (_hμ : ∀ x,0 ≤ μ x) (_hmass : ∑ x,μ x ≤ 1)
      (_hmajorant : ∀ x : η × Fin N,μ x ≤ longProgressionMajorant E b₀ Q (a x.1) x.2)
      (_hν : ∀ j,0 ≤ ν j) (_hνmass : ∑ j,ν j ≤ 1)
      (_hU : ∀ x,‖U x‖ ≤ 1) (_hV : ∀ j,‖V j‖ ≤ 1)
      (data : η → κ → HistoryPolynomialData σ τ)
      (A B : τ → ℝ) (M : ℝ),
    (∀ r j,(data r j).Ranges ρ A B M) →
    Fintype.card η ≤ Q → (Q : ℝ) ≤ Real.exp (historyPolynomialCost C z d L) →
    E ≤ Real.exp (historyPolynomialCost C z d L) →
    (∀ r j,((data r j).degreeCost : ℝ) ≤ Real.exp (historyPolynomialCost C z d L)) →
    M ≤ Real.exp (historyPolynomialCost C z d L) →
    3+(∑i : τ,(B i-A i)) ≤ Real.exp (historyPolynomialCost C z d L) →
    priorMaxAtom ν ≤ Real.exp (-c*Real.exp (α*L)) →
    (∀ j,Real.log (q j : ℝ) ≤ Real.exp (β*L)) →
    Real.exp (γ*L) ≤ Real.log b₀ →
    ‖oneSidedMean μ ν U V (rowCharacterKernel q χ Q N a
      (fun r n j => (data r j).weight ρ ((Q*n+a r:ℕ):ℝ)))‖ ≤
        Real.exp (-δ*Real.exp (α*L)) := by
  obtain ⟨δ,hδ,hdecay⟩ := eventually_oneSided_bilinear_scale_gap
    (τ:=Unit ⊕ (τ ⊕ τ)) (compiledConstant C (Fintype.card τ)) z d
    (compiledConstant_nonneg hC _) hz hα hαβ hβγ hc
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hdecay] with L hL
  intro η κ σ _ _ _ ρ q hq hinj χ hχ Q N a hQ μ ν U V E b₀ hE hb hN
    hμ hmass hmajorant hν hνmass hU hV data A B M hdata hrows hQsize hEsize hdegree hM hwidth
    hatom hshort hlong
  have hcost := compiledCost_bounds C z L d (Fintype.card τ) hC
  have hcostExp := Real.exp_le_exp.mpr hcost.2.1
  have hexp : 1 ≤ Real.exp (historyPolynomialCost C z d L) := Real.one_le_exp_iff.mpr hcost.1
  have hseven := compiledCost_seven_exp C z L d (Fintype.card τ) hC
  apply hL ρ q hq hinj χ hχ Q N a hQ μ ν U V
    (fun r n j => (data r j).weight ρ ((Q*n+a r:ℕ):ℝ)) E b₀ hE hb hN
    hμ hmass hmajorant hν hνmass hU hV
    (fun r j k => crossHistoryData b₀ (data r j) (data r k))
    (Sum.elim (fun _ => -Real.log 2) (Sum.elim A A))
    (Sum.elim (fun _ => 0) (Sum.elim B B)) (max 1 M)
  · intro r j k _
    exact crossHistoryData_ranges ρ hb _ _ (hdata r j) (hdata r k)
  · intro r j k _ n _
    exact crossHistoryData_weight ρ hb E _ _ Q (a r) n
  · exact hrows
  · exact hQsize.trans hcostExp
  · exact hEsize.trans hcostExp
  · intro r n j
    calc
      _ ≤ M^(Fintype.card τ) := data_weight_norm_le _ ρ (hdata r j) _
      _ ≤ (Real.exp (historyPolynomialCost C z d L))^(Fintype.card τ) := by
        gcongr
        exact (hdata r j).nonneg
      _ = Real.exp ((Fintype.card τ:ℝ)*historyPolynomialCost C z d L) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hcost.2.2.1
  · intro r j k _
    calc
      _ ≤ ((data r j).degreeCost:ℝ)+((data r k).degreeCost:ℝ)+5 := by
        exact_mod_cast crossHistoryData_degreeCost b₀ (data r j) (data r k)
      _ ≤ 2*Real.exp (historyPolynomialCost C z d L)+5 := by linarith [hdegree r j,hdegree r k]
      _ ≤ 7*Real.exp (historyPolynomialCost C z d L) := by linarith
      _ ≤ _ := hseven
  · exact max_le (hexp.trans hcostExp) (hM.trans hcostExp)
  · rw [crossLogWidth_eq]
    have hlog : Real.log 2 ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      linarith
    apply le_trans _ hseven
    linarith
  · exact hatom
  · exact hshort
  · exact hlong

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
