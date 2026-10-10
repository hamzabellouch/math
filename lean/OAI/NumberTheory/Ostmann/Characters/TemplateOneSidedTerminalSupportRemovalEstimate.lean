import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedTerminalSupportRemovalFrequency
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedTerminalSupportRemovalPhase

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.TemplateOneSidedTerminalSupportRemoval
open Template SymbolicHistory Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open ParityActions
open InitialCharacterScale HistoryFrequencyLabels HistoryFrequencyBudget HigherBiasSourceRoleBounds
open TemplateOneSidedSupportTelescoping TemplateOneSidedRelabel TemplateOneSidedSupportTransport
open TemplateSupportRemoval TemplateOneSidedBudget DiagonalEstimate Filter
attribute [local instance] Classical.propDecidable

theorem exists_eventually_terminal_support_removal (n : ℕ)
    {α β ρ γ c₀ c BD : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hc₀ : 0 < c₀) (hc : 0 < c) (hBD : 0 ≤ BD) :
    ∃K : ℝ,0 < K ∧ ∀ᶠL : ℝ in atTop,
    ∀(d : Decomposition)(E : Finset ℕ)(δ : ℝ),(∀p∈E,p.Prime) →
      (∀p∈E,α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
      ∀s : SelectedWordSource d E δ L (n+1) α β ρ γ c₀,∀w : FixedConfigurationWitness s c BD,
      ∀(B V : (l:ℕ)→State (n+1) (l+1)→ℤ)
        (σ τ : Reassignments (n+1) n (wordSize (n+1) L))
        (h h' : SourceHistory (k:=n+1) (L:=L) (BD:=BD) (n+1)),h.val.1=h'.val.1 →
      ‖fullProductMean (terminalSourceIntegerSupport w n) (terminalSourceIntegerWeight w n)
          (terminalStartKernel w n B V σ τ h h')-terminalCoreMean w n B V σ τ h h'‖ ≤
        Real.exp (K*L^2-(1/4:ℝ)*Real.exp (α*L)) := by
  let k := n+1
  have hβ : 0 < β := hα.trans hαβ
  let Z := 6*obstructionSizeFactor k k
  let A := fixedPairBound k (configurationProductWidth k c) 0
  obtain ⟨C,hC,hAC,hcost⟩ := exists_source_support_cost k β A Z
  obtain ⟨K,hK,herror⟩ := exists_source_support_error_cost k (2*Fintype.card (schedule k k).Slot)
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_reindexed_weight_pair_outside_enlargement C (depthScale k) 2 k
      (configurationProductWidth k c) 0 hAC hC.le (depthScale_pos k).le hα
      (by norm_num : (0:ℝ) < 1/2),
    eventually_terminalSourceIntegerWeight_le k hα hαβ hρ hγ hc₀ hc,
    eventually_terminalIntegerPhase_norm k BD c α hBD hα,
    eventually_terminalFamilies_syntax k,eventually_terminalFamilies_fixedLog k β BD (by linarith) hBD,
    eventually_terminalFamilies_divisorsBelow k hBD hα,
    TemplateOneSidedCancellation.eventually_terminal_sourceWidth_le k,eventually_ge_atTop (1:ℝ)]
    with L htel hatoms hphase hsyntax hfixed hdiv hwidth hL
  intro d E δ hE hband s w B V σ τ h h' hroot
  let width := sourceWidth w.configuration (wordSize k L)
  let π := terminalPermutations w n σ τ
  let refExpr := sampledExpressions k k width
  have hL0 : 0 ≤ L := by linarith
  have hH : Real.log 2 ≤ Real.exp ((β+1)*L) := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    have he : 1 ≤ Real.exp ((β+1)*L) := Real.one_le_exp_iff.mpr (by positivity)
    linarith
  have hΔ : 0 ≤ initialGap BD k L := by
    exact mul_nonneg (add_nonneg hBD (mul_nonneg (by norm_num)
      (Real.log_nonneg (one_le_depthScale k)))) (Nat.cast_nonneg _)
  have hs (r : Bool) (i : terminalSourceIndex w n) (q : Expr (terminalSourceIndex w n))
      (hq : q∈actualFamilies k (fun u=>width ((schedule k k).role u)) k
        (SampleOrigins.root k k) (terminalRoots n h h' r) refExpr (terminalTrees n h h' r) i) :
      q.syntaxSize ≤ Z*(wordSize k L+1) :=
    hsyntax d E δ α β ρ γ c₀ c BD s w k _ _ i q hq
  have hf (r : Bool) (i : terminalSourceIndex w n) (q : Expr (terminalSourceIndex w n))
      (hq : q∈actualFamilies k (fun u=>width ((schedule k k).role u)) k
        (SampleOrigins.root k k) (terminalRoots n h h' r) refExpr (terminalTrees n h h' r) i) :
      q.FixedLogBound (Real.exp ((β+1)*L)) := by
    cases r
    · exact hfixed d E δ α ρ γ c₀ c s w h' i q hq
    · exact hfixed d E δ α ρ γ c₀ c s w h i q hq
  have hd (r : Bool) (i : terminalSourceIndex w n) (q : Expr (terminalSourceIndex w n))
      (hq : q∈actualFamilies k (fun u=>width ((schedule k k).role u)) k
        (SampleOrigins.root k k) (terminalRoots n h h' r) refExpr (terminalTrees n h h' r) i)
      (x : terminalSourceIndex w n→ℤ) (hx : ∀u,x u∈terminalSourceIntegerSupport w n (π r u)) :
      q.DivisorsBelow (x i).toNat := by
    cases r
    · exact hdiv d E δ β ρ γ c₀ c hband s w n (le_refl _) h' i q hq (π false i) (x i) (hx i)
    · exact hdiv d E δ β ρ γ c₀ c hband s w n (le_refl _) h i q hq (π true i) (x i) (hx i)
  have hvars (i : terminalSourceIndex w n) (a : ℤ) (ha : a∈terminalSourceIntegerSupport w n i) :
      |(a:ℝ)| ≤ Real.exp (Real.exp ((β+1)*L)) :=
    (terminalSourceIntegerSupport_abs_le w n hband i ha).trans
      (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith)))
  have hcostL := hcost L hL
  have hZ : (Z*(wordSize k L+1):ℕ) ≤ Real.exp (historyPolynomialCost C (depthScale k) 2 L) := by
    exact_mod_cast hcostL.2.1
  have hv := htel (fun u=>width ((schedule k k).role u)) k B V
    (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w))
    (fun _=>SampleOrigins.root k k) (terminalRoots n h h') (fun _=>refExpr) (terminalTrees n h h')
    (terminalSourceIntegerSupport w n) (terminalSourceIntegerWeight w n) (terminalSourceNaturalSupport w n)
    (terminalSourceIntegerSupport_eq_nat_image w n) π (Real.exp ((β+1)*L)) hH
    (fun i a _=>terminalSourceIntegerWeight_nonneg w n i a) (terminalSourceIntegerWeight_sum w n)
    (fun i a _=>hatoms d E δ BD hE hband s w n i a)
    (fun i p hp=>terminalSourceNaturalSupport_prime w n i hp)
    (Z*(wordSize k L+1)) hs hf hvars (fun _=>true)
    (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
      (initialGap BD k L) (configurationProductWidth k c)))
    s.locations.X (initialGap BD k L) 0 (fixedConfiguration_X_pos w) hΔ (fun _=>1)
    (terminalIntegerPhase w n σ τ h h')
    (hphase d E δ β ρ γ c₀ hband s w n (le_refl _) σ τ h h' hroot)
    (fun r x hx i=>sampledExpressions_good k k width x i)
    (fun r i q hq x hx _=>hd r i q hq x hx) hcostL.1 hZ hcostL.2.2
  have hactual : ‖fullProductMean (terminalSourceIntegerSupport w n) (terminalSourceIntegerWeight w n)
        (terminalStartKernel w n B V σ τ h h')-terminalCoreMean w n B V σ τ h h'‖ ≤
      (2*(Fintype.card (terminalSourceIndex w n)):ℝ)*Real.exp (-(1/4:ℝ)*Real.exp (α*L)) := by
    simp only [terminalCoreMean]
    change ‖(fullProductMean (terminalSourceIntegerSupport w n) (terminalSourceIntegerWeight w n)
      (fun x=>terminalStartKernel w n B V σ τ h h' x))-
      fullProductMean (terminalSourceIntegerSupport w n) (terminalSourceIntegerWeight w n)
        (fun x=>terminalEndKernel w n B V σ τ h h' x)‖ ≤ _
    simp only [terminalStartKernel,terminalEndKernel,terminalMultiplier,
      terminalExpressions,terminalPolynomialGate,decide_eq_true_eq,true_and,
      refExpr,π,width,k,show (1/2:ℝ)/2=1/4 by norm_num] at hv ⊢
    convert hv using 1
    rfl
  have hcount : Fintype.card (terminalSourceIndex w n) ≤
      (2*Fintype.card (schedule k k).Slot)*(wordSize k L+1) := by
    change Fintype.card ((u:(schedule k k).Slot)×Fin (width ((schedule k k).role u))) ≤ _
    simp only [Fintype.card_sigma,Fintype.card_fin]
    calc
      _ ≤ ∑_u:(schedule k k).Slot,(wordSize k L+1) :=
        Finset.sum_le_sum (fun u _=>hwidth d E δ α β ρ γ c₀ c BD s w ((schedule k k).role u))
      _ ≤ _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; nlinarith
  apply hactual.trans
  apply le_trans _ (herror L α hL)
  have hh : (Fintype.card (terminalSourceIndex w n):ℝ) ≤
      (2*Fintype.card (schedule k k).Slot:ℝ)*((wordSize k L:ℝ)+1) := by exact_mod_cast hcount
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  simp only [Nat.cast_mul,Nat.cast_ofNat]
  nlinarith

end Ostmann.Characters.TemplateOneSidedTerminalSupportRemoval

end

end OAI
