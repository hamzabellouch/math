import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationPrimePriorsRows

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap
namespace Ostmann.Characters.TemplateOneSidedCancellation
open Construction Preliminaries PrimeDyadicCover TemplateOneSidedPrior Filter
open Template.OneSidedPhase TemplateOneSidedNumericInputs
attribute [local instance] Classical.propDecidable

theorem eventually_original_prime_priors_scale_gap
    {τ : Type} [Fintype τ] (C z c : ℝ) (d : ℕ)
    {α β γ γLong βLong : ℝ}
    (hC : 0 ≤ C) (hz : 0 < z) (hc : 0 ≤ c) (hα : 0 < α)
    (hαβ : α ≤ β) (hβγ : β < γ) (hγLong : γ < γLong) (hβLong : 0 ≤ βLong) :
    ∃ δ : ℝ,0 < δ ∧ ∀ᶠ L : ℝ in atTop,
    ∀ {A : ℕ} {σ : Type} [Fintype σ],
    ∀ (Elong Eshort : Finset (PrimeUpTo A))
      (hElong : 0 < primeShellMass Elong) (hEshort : 0 < primeShellMass Eshort)
      (ρ : 𝓢(ℝ,ℂ)) (Q : ℕ) (_hQ : 0 < Q)
      (χ : ∀j:↥Eshort,MulChar (ZMod j.val.val) ℂ) (_hχ : ∀j,χ j ≠ 1)
      (U : PrimeUpTo A → ℂ) (V : ↥Eshort → ℂ)
      (F : PrimeUpTo A → ↥Eshort → ℂ)
      (data : Index (sourceUpper βLong L) → Fin Q → ↥Eshort → HistoryPolynomialData σ τ)
      (lo hi : Index (sourceUpper βLong L) → τ → ℝ)
      (M : Index (sourceUpper βLong L) → ℝ),
    Real.exp (-c*L) ≤ primeShellMass Elong →
    Real.exp (-c*L) ≤ primeShellMass Eshort →
    (∀p∈Eshort,Real.exp (α*L) ≤ Real.log p.val) →
    (∀p∈Eshort,Real.log p.val ≤ Real.exp (β*L)) →
    (∀p∈Elong,Real.exp (γLong*L) ≤ Real.log p.val) →
    (∀p∈Elong,Real.log p.val ≤ Real.exp (βLong*L)) →
    (∀p∈Elong,‖U p‖ ≤ 1) → (∀j,‖V j‖ ≤ 1) →
    (Q:ℝ) ≤ Real.exp (historyPolynomialCost C z d L) →
    (∀i,(block Q (sourceUpper βLong L) (sourceNaturals Elong) i).Nonempty →
      (∀r j,(data i r j).Ranges ρ (lo i) (hi i) (M i)) ∧
      (∀r j,((data i r j).degreeCost:ℝ) ≤ Real.exp (historyPolynomialCost C z d L)) ∧
      M i ≤ Real.exp (historyPolynomialCost C z d L) ∧
      3+(∑t:τ,(hi i t-lo i t)) ≤ Real.exp (historyPolynomialCost C z d L)) →
    (∀i,∀p∈Elong,p.val∈block Q (sourceUpper βLong L) (sourceNaturals Elong) i →
      ∀r:Fin Q,∀n:ℕ,Q*n+r.val=p.val → ∀j:↥Eshort,
        (data i r j).weight ρ ((Q*n+r.val:ℕ):ℝ)=F p j) →
    ‖(primeShellPrior Elong hElong).cmean (fun p=>U p*
      ∑j:↥Eshort,((primeShellPrior Eshort hEshort).mass j.val:ℂ)*V j*
        χ j (p.val:ZMod j.val.val)*F p j)‖ ≤ Real.exp (-δ*Real.exp (α*L)) := by
  let C' := primePriorConstant C z c βLong
  have hC' : 0 < C' := primePriorConstant_pos hC hz hc hβLong
  have hγ : 0 ≤ γ := by linarith
  have hγL : 0 < γLong := by linarith
  obtain ⟨δ,hδ,hcompiled⟩ := eventually_compiled_oneSided_scale_gap (τ:=τ) C' z (d+1)
    hC'.le hz.le hα hαβ hβγ (by norm_num : (0:ℝ)<1/2)
  refine ⟨δ/2,half_pos hδ,?_⟩
  filter_upwards [hcompiled,eventually_scale_gap_finite_sum C' z (d+1) hz.le hα hδ,
    eventually_primeShellPrior_mass_le hα hc,
    eventually_budget_modulus_lt_prime C z d hz.le hα,
    eventually_budget_modulus_lt_prime C z d hz.le hγL,
    eventually_occupied_lower_scale hγ hγLong,eventually_ge_atTop (0:ℝ)]
    with L hcompiledL hsum hatom hprimeS hprimeL hoccupied hL
  intro A σ _ Elong Eshort hElong hEshort ρ Q hQ χ hχ U V F data lo hi M
    hZlong hZshort hshortlo hshorthi hlonglo hlonghi hU hV hQcost hdata hrepr
  have hmin : ∀p∈Elong,Q ≤ p.val := fun p hp=>(hprimeL Q p.val hQcost (hlonglo p hp)).le
  have hcop : ∀j:↥Eshort,Q.Coprime j.val.val := fun j=>
    (prime_coprime_of_lt hQ (primeUpTo_prime j.val)
      (hprimeS Q j.val.val hQcost (hshortlo j.val j.property))).symm
  have hcost := primePriorCost_bounds C z c βLong L d hC hz hc hβLong hL
  have hexpcost : Real.exp (historyPolynomialCost C z d L) ≤
      Real.exp (historyPolynomialCost C' z (d+1) L) := Real.exp_le_exp.mpr hcost.1
  have hZcost : 1/primeShellMass Elong ≤ Real.exp (historyPolynomialCost C' z (d+1) L) :=
    (source_normalization_le Elong hZlong).trans (Real.exp_le_exp.mpr hcost.2.1)
  have hmaxatom : priorMaxAtom (sourceShortMass Eshort hEshort) ≤
      Real.exp (-(1/2:ℝ)*Real.exp (α*L)) :=
    sourceShortMass_max_le Eshort hEshort (Real.exp_pos _).le
      (hatom Eshort hEshort hZshort hshortlo)
  have hcard : (Fintype.card (Index (sourceUpper βLong L)):ℝ) ≤
      Real.exp (historyPolynomialCost C' z (d+1) L) := by
    have hb := card_le_exp hβLong hL (log_sourceUpper_le βLong L)
    have hconst : 0 < 1/Real.log 2+1 := by
      have hh : 0 < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    apply hb.trans
    calc
      _ = Real.exp (Real.log (1/Real.log 2+1)+βLong*L) := by
        rw [Real.exp_add,Real.exp_log hconst]
      _ ≤ _ := Real.exp_le_exp.mpr hcost.2.2
  rw [source_prime_bilinear_cmean_eq_rows_of_log Q hQ Elong Eshort hElong hEshort
    hmin hlonghi χ U V F]
  apply hsum _ hcard
  intro i
  by_cases hoc : (block Q (sourceUpper βLong L) (sourceNaturals Elong) i).Nonempty
  · rw [original_block_eq_compiled Q (sourceUpper βLong L) Elong Eshort hEshort i ρ
      χ U V F (data i) (hrepr i)]
    obtain ⟨hranges,hdegree,hM,hwidth⟩ := hdata i hoc
    obtain ⟨hrows,hb,hN,hμ,hmass,hmajorant⟩ := source_row_parameters Q (sourceUpper βLong L)
      hQ Elong hElong hmin i
    apply hcompiledL ρ (fun j:↥Eshort=>j.val.val)
      (fun j=>primeUpTo_prime j.val) (fun i j hh=>Subtype.ext (Subtype.ext hh)) χ hχ
      Q (2*lower Q (sourceUpper βLong L) i+1) (fun r:Fin Q=>r.val) hcop
      (sourceRowMass Q (sourceUpper βLong L) Elong i) (sourceShortMass Eshort hEshort)
      (fun x=>sourceTest (boundedSourceUnary Elong U)
        (rowValue Q (2*lower Q (sourceUpper βLong L) i+1) x)) V
      (1/primeShellMass Elong) (lower Q (sourceUpper βLong L) i) (by positivity) hb hN
      hμ hmass hmajorant (sourceShortMass_nonneg Eshort hEshort)
      (sourceShortMass_total Eshort hEshort).le
      (fun x=>sourceTest_boundedSourceUnary_norm_le_one Elong U hU _) hV
      (data i) (lo i) (hi i) (M i) hranges hrows (hQcost.trans hexpcost) hZcost
      (fun r j=>(hdegree r j).trans hexpcost) (hM.trans hexpcost) (hwidth.trans hexpcost)
      hmaxatom (fun j=>hshorthi j.val j.property)
    exact hoccupied Q (sourceUpper βLong L) hQ Elong hmin hlonglo i hoc
  · have he := Finset.not_nonempty_iff_eq_empty.mp hoc
    simp only [oneSidedMean,sourceRowMass_zero_of_empty Q (sourceUpper βLong L) Elong i he,
      Complex.ofReal_zero,zero_mul,Finset.sum_const_zero,norm_zero]
    exact (Real.exp_pos _).le

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
