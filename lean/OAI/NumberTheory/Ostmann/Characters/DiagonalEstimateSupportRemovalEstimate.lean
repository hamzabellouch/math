import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateMarginalScales
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalKernels
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalNumerics
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalPhase
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportSurvivingBudget
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTelescopingPairReindexedActual

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template SymbolicHistory Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale HistoryFrequencyLabels HistoryFrequencyBudget HigherBiasSourceRoleBounds
open TemplateOneSidedSupportSurviving TemplateOneSidedSupportTelescoping TemplateOneSidedRelabel
open TemplateOneSidedSupportTransport TemplateSupportRemoval TemplateOneSidedSourceSyntax Filter
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

theorem exists_eventually_sourcePair_support_removal (k : ℕ)
    {α β ρ γ c₀ c BD : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hc₀ : 0 < c₀) (hc : 0 < c) (hBD : 0 ≤ BD) :
    ∃K : ℝ,0 < K ∧ ∀ᶠ L : ℝ in atTop,
    ∀(d : Decomposition)(E : Finset ℕ)(δ : ℝ),(∀p∈E,p.Prime) →
      (∀p∈E,α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
      ∀s : SelectedWordSource d E δ L k α β ρ γ c₀,∀w : FixedConfigurationWitness s c BD,
      ∀j (hj : j < k) (B V : (l:ℕ) → State k (l+1) → ℤ),
      ∀P∈DiagonalEstimate.sourcePivotRanges w j,
      ∀(e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
        (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j),
      ‖fullProductMean (groupedSourceIntegerSupport w j) (groupedSourceIntegerWeight w j)
          (sourcePairStartKernel w j hj B V P e h h')-
        fullProductMean (groupedSourceIntegerSupport w j) (groupedSourceIntegerWeight w j)
          (sourcePairEndKernel w j hj B V P e h h')‖  ≤ 
        Real.exp (K*L^2-(1/4:ℝ)*Real.exp (α*L)) := by
  have hβ : 0 < β := hα.trans hαβ
  let A : ℝ := ∑j:Fin k,fixedPairBound j.val (configurationProductWidth k c) (sourceCopiedWidth k c)
  obtain ⟨C,hC,hAC,hcost⟩ := exists_source_support_cost k β A (sourceFamilySyntaxConstant k)
  have hpairC (j : Fin k) : fixedPairBound j.val (configurationProductWidth k c) (sourceCopiedWidth k c) ≤ C := by
    exact (Finset.single_le_sum (fun i _=>fixedPairBound_nonneg i.val _ _) (Finset.mem_univ j)).trans hAC
  have htels := Filter.eventually_all.mpr (fun j : Fin k=>
    eventually_reindexed_weight_pair_outside_enlargement C (depthScale k) 2 j.val
      (configurationProductWidth k c) (sourceCopiedWidth k c) (hpairC j)
      hC.le (depthScale_pos k).le hα (by norm_num : (0:ℝ) < 1/2))
  obtain ⟨K,hK,herror⟩ := exists_source_support_error_cost k (sourceSurvivingConstant k)
  refine ⟨K,hK,?_⟩
  filter_upwards [htels,eventually_sourceSurvivor_marginal_bounds k hα hαβ hρ hγ hc₀ hc,
    eventually_sourceSurvivorPairPhase_norm_le k hBD hα,
    eventually_actualFamilies_fixedLog k c β BD (by linarith) hBD,
    eventually_actualFamilies_divisorsBelow k hBD hα,eventually_ge_atTop (1:ℝ)]
    with L htel hmass hphase hfixed hdiv hL
  intro d E δ hE hband s w j hj B V P hP e h h'
  let width := sourceWidth w.configuration (wordSize k L)
  let π := fun r=>groupedPermutation k j width (sourcePairPermutations w j e r)
  let refExpr := groupedExpressions k j width P (Equiv.refl _)
  have hL0 : 0 ≤ L := by linarith
  have hH : Real.log 2 ≤ Real.exp ((β+1)*L) := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    have he : 1 ≤ Real.exp ((β+1)*L) := Real.one_le_exp_iff.mpr (by positivity)
    linarith
  have hΔ : 0 ≤ initialGap BD k L := by
    exact mul_nonneg (add_nonneg hBD (mul_nonneg (by norm_num)
      (Real.log_nonneg (one_le_depthScale k)))) (Nat.cast_nonneg _)
  have hatom (i : GroupedSourceIndex w j) (n : ℤ) (_hn : n∈groupedSourceIntegerSupport w j i) :
      groupedSourceIntegerWeight w j i n ≤ Real.exp (-(1/2:ℝ)*Real.exp (α*L)) :=
    (hmass d E δ BD hE hband s w j
      (survivingPrimeEquiv k j width i)).2.2 n
  have hpbound (x : GroupedSourceIndex w j → ℤ) (hx : ∀i,x i∈groupedSourceIntegerSupport w j i) :
      ‖sourceGroupedPairPhase w j hj P e h h' x‖ ≤ 1 := by
    obtain ⟨p,hp,rfl⟩ := groupedSource_support_exists_prime w j x hx
    rw [sourceGroupedPairPhase,integerPrimeTest_groupedPrimeAssignment]
    exact hphase d E δ β ρ γ c₀ c hband s w j hj P e h h' p hp
  have hsyntax (r : Bool) (i : GroupedSourceIndex w j) (q : Expr (GroupedSourceIndex w j))
      (hq : q∈actualFamilies k (survivingWidth k j width) j (origins k j)
        (sourcePairRoots j h h' r) refExpr (sourcePairTrees j h h' r) i) :
      q.syntaxSize ≤ sourceFamilySyntaxConstant k*(wordSize k L+1) :=
    actual_sourceFamilies_syntax w j hj.le P _ (Equiv.refl _) _ i q hq
  have hfixed' (r : Bool) (i : GroupedSourceIndex w j) (q : Expr (GroupedSourceIndex w j))
      (hq : q∈actualFamilies k (survivingWidth k j width) j (origins k j)
        (sourcePairRoots j h h' r) refExpr (sourcePairTrees j h h' r) i) :
      q.FixedLogBound (Real.exp ((β+1)*L)) := by
    cases r
    · exact hfixed d E δ α ρ γ c₀ s w j hj P hP (Equiv.refl _) h i q hq
    · exact hfixed d E δ α ρ γ c₀ s w j hj P hP (Equiv.refl _) h' i q hq
  have hfreq (r : Bool) (i : GroupedSourceIndex w j) (q : Expr (GroupedSourceIndex w j))
      (hq : q∈actualFamilies k (survivingWidth k j width) j (origins k j)
        (sourcePairRoots j h h' r) refExpr (sourcePairTrees j h h' r) i)
      (x : GroupedSourceIndex w j → ℤ) (hx : ∀u,x u∈groupedSourceIntegerSupport w j (π r u)) :
      q.DivisorsBelow (x i).toNat := by
    cases r
    · exact hdiv d E δ β ρ γ c₀ c hband s w j hj.le P (Equiv.refl _) h i q hq (π false i) (x i) (hx i)
    · exact hdiv d E δ β ρ γ c₀ c hband s w j hj.le P (Equiv.refl _) h' i q hq (π true i) (x i) (hx i)
  have hvars (i : GroupedSourceIndex w j) (n : ℤ) (hn : n∈groupedSourceIntegerSupport w j i) :
      |(n:ℝ)| ≤ Real.exp (Real.exp ((β+1)*L)) :=
    (groupedSourceIntegerSupport_abs_le w j hband i hn).trans
      (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith)))
  have hcostL := hcost L hL
  have htree : (2^(j+1):ℝ) ≤ Real.exp (historyPolynomialCost C (depthScale k) 2 L) :=
    (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : j+1 ≤ k+1)).trans hcostL.1
  have hZ : (sourceFamilySyntaxConstant k*(wordSize k L+1):ℕ) ≤ 
      Real.exp (historyPolynomialCost C (depthScale k) 2 L) := by
    exact_mod_cast hcostL.2.1
  have hv := htel ⟨j,hj⟩ (survivingWidth k j width) k B V
    (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w))
    (fun _=>origins k j) (sourcePairRoots j h h') (fun _=>refExpr) (sourcePairTrees j h h')
    (groupedSourceIntegerSupport w j) (groupedSourceIntegerWeight w j) (groupedSourceNaturalSupport w j)
    (groupedSourceIntegerSupport_eq_nat_image w j) π (Real.exp ((β+1)*L)) hH
    (fun i n _=>groupedSourceIntegerWeight_nonneg w j i n) (groupedSourceIntegerWeight_sum w j)
    hatom (fun i p hp=>groupedSourceNaturalSupport_prime w j i hp)
    (sourceFamilySyntaxConstant k*(wordSize k L+1)) hsyntax hfixed' hvars (fun _=>true)
    (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
      (initialGap BD k L) (configurationProductWidth k c)))
    s.locations.X (initialGap BD k L)
    (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+gapSchedule BD k L (j+1))
    (fixedConfiguration_X_pos w) hΔ (sourceGroupedCopiedProduct w j)
    (sourceGroupedPairPhase w j hj P e h h') hpbound
    (fun r x hx i=>groupedExpressions_good k j width P (Equiv.refl _) x i)
    (fun r i q hq x hx _=>hfreq r i q hq x hx) htree hZ hcostL.2.2
  have hactual : ‖fullProductMean (groupedSourceIntegerSupport w j) (groupedSourceIntegerWeight w j)
        (sourcePairStartKernel w j hj B V P e h h')-
      fullProductMean (groupedSourceIntegerSupport w j) (groupedSourceIntegerWeight w j)
        (sourcePairEndKernel w j hj B V P e h h')‖  ≤ 
      (2*(Fintype.card (GroupedSourceIndex w j)):ℝ)*Real.exp (-(1/4:ℝ)*Real.exp (α*L)) := by
    change ‖(fullProductMean (groupedSourceIntegerSupport w j) (groupedSourceIntegerWeight w j)
        (fun x=>sourcePairStartKernel w j hj B V P e h h' x))-
      fullProductMean (groupedSourceIntegerSupport w j) (groupedSourceIntegerWeight w j)
        (fun x=>sourcePairEndKernel w j hj B V P e h h' x)‖ ≤ _
    simp only [sourcePairStartKernel,sourcePairEndKernel,sourcePairExpressions,sourcePairPolynomialGate,
      decide_eq_true_eq,true_and,refExpr,π,width,show (1/2:ℝ)/2=1/4 by norm_num] at hv ⊢
    convert hv using 1
    rfl
  apply hactual.trans
  have hcount : (Fintype.card (GroupedSourceIndex w j):ℝ) ≤ 
      (sourceSurvivingConstant k:ℝ)*((wordSize k L:ℝ)+1) := by
    exact_mod_cast actual_sourceSurviving_card_le w (wordSize k L) j hj.le
  apply le_trans _ (herror L α hL)
  exact mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_pos _).le

end Ostmann.Characters.DiagonalEstimate

end

end OAI
