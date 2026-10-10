import OAI.NumberTheory.Jacobsthal.Analysis.SourceCompactErrorMass
import OAI.NumberTheory.Jacobsthal.Paths.StoppedErrorReduction

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SourceRootErrorLower
open _root_.Filter FinitePathGeometry PrimeHistories PrimeBinMembership SourceStopPredicate
open SourceRootReference SourceCompactErrorMass StoppedErrorReduction CountErrorClassification
open StoppedCountVertex StoppedCountAdapters StoppedVertexHistory StoppedTraceSets
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInverseBoxHeight ErdosCorrectionLimit ErdosSourceReferenceMargin
open ErdosPrimeInputs.PrimePrefixMass
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem source_root_lower_with_stopped_correction (Cmin : ℝ) :
    ∃ c Clen Cs xi₀ : ℝ,0 < c ∧ 1 ≤ Clen ∧ 0 < Cs ∧ Cmin ≤ Cs ∧ 0 < xi₀ ∧ xi₀ ≤ 1 ∧
    ∀ eta : ℝ,0 < eta → eta < 1/2 → ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ xi₀ →
    ∃ rho : ℝ,10 < rho ∧ ∀ Kstop : ℝ,0 < Kstop →
    ∀ᶠ top : ℝ in atTop,∃ hw : 1 < sourceW top,∃ htop : sourceW top < top,
      ∀ a : ℕ → ℕ,
      let w := sourceW top
      let B := sourceB top
      let Y := sourceY top
      let small := LargePrimeDeletion.cutoffPrimes ⌊w⌋₊
      let V0 := SmallSieveFinite.smallEuler ⌊w⌋₊
      let z := sourceRootNode (1/100) top
      let P := sourcePrimeSet w top
      let v := rootVertex z ∅ P ((Y:ℝ)*V0)
      let stop := stopCandidate Y w Cs eta Clen B xi (Kstop*(Real.log w)^2) (rho*Kstop*(Real.log w)^2)
        (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi) a z
      c*((Y:ℝ)*V0/B^2)+
        (∑ ps∈stopped w stop P.card v,(countSurvivors Y small a (after w v ps)-referenceValue w (after w v ps))) ≤
        countSurvivors Y small a v := by
  obtain ⟨c_L,hc_L,hRef⟩ := source_root_polynomial_margin
  have heighth : 0 < c_L/8 := by positivity
  obtain ⟨Cbad,K,hCbad,hK,hError⟩ := stopped_error_reduction (1/100) 2 (c_L/8) (by norm_num) (by norm_num) heighth
  obtain ⟨Csmall,B₀,W,hCsmall,hB₀,hW,hError⟩ := hError K (le_refl _)
  let eps := c_L/(8*Csmall)
  let budget := c_L/(8*Cbad)
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hbudget : 0 < budget := by dsimp [budget]; positivity
  obtain ⟨Clen,Cs,xi₀,hClen,hCs,hCsMin,hxi₀,hxi₀1,hCompact⟩ :=
    source_compact_error_mass K eps budget (1/100) Cmin hK heps hbudget (by norm_num) (by norm_num)
  refine ⟨c_L/2,Clen,Cs,xi₀,by positivity,hClen,hCs,hCsMin,hxi₀,hxi₀1,?_⟩
  intro eta heta0 heta xi hxi hx
  obtain ⟨rho,hrho,hCompact⟩ := hCompact eta heta0 heta xi hxi hx
  refine ⟨rho,hrho,?_⟩
  intro Kstop hKstop
  filter_upwards [hCompact Kstop hKstop,source_root_eventually_data,hRef,
    rootB_tendsto.eventually_ge_atTop B₀,rootW_tendsto.eventually_ge_atTop (max W 2)]
    with top hCompact hData hRef hB hwBound
  obtain ⟨hw,htop,hCompact⟩ := hCompact
  obtain ⟨hY,_hB3,_hw,_hwt,hcomp,h199,h23,hcons,hpower⟩ := hData
  refine ⟨hw,htop,?_⟩
  intro a
  dsimp only
  let w := sourceW top
  let B := sourceB top
  let Y := sourceY top
  let small := LargePrimeDeletion.cutoffPrimes ⌊w⌋₊
  let V0 := SmallSieveFinite.smallEuler ⌊w⌋₊
  let z := sourceRootNode (1/100) top
  let P := sourcePrimeSet w top
  let mu := (Y:ℝ)*V0
  let v := rootVertex z ∅ P mu
  let stop := stopCandidate Y w Cs eta Clen B xi (Kstop*(Real.log w)^2) (rho*Kstop*(Real.log w)^2)
    (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi) a z
  have hw2 : 2 ≤ w := (le_max_right _ _).trans hwBound
  have hV0 : 0 < V0 := (inv_pos.mpr (zero_lt_one.trans hw)).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv w hw2)
  have hmu : 0 < mu := mul_pos (by exact_mod_cast hY) hV0
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num : (0:ℝ)<3) (hB₀.trans hB)
  have hRoot : z.gap=Real.log (Y:ℝ)/Real.log w-(1:ℝ)/100+2 := rfl
  have hErr := hError B w top hB ((le_max_left _ _).trans hwBound) htop hcomp Y hY z hRoot
    rfl h199 h23 hcons rfl rfl hpower a eps heps.le stop
  have hBad := hCompact z a rfl h199 h23 hcons rfl rfl hRoot
  dsimp only at hErr hBad
  have hSmallPay : Csmall*eps=c_L/8 := by dsimp [eps]; field_simp [hCsmall.ne']
  have hBadPay : Cbad*budget=c_L/8 := by dsimp [budget]; field_simp [hCbad.ne']
  have hBadScaled := mul_le_mul_of_nonneg_left hBad hCbad.le
  rw [hBadPay] at hBadScaled
  rw [hSmallPay] at hErr
  let correction := ∑ ps∈stopped w stop P.card v,(countSurvivors Y small a (after w v ps)-referenceValue w (after w v ps))
  have hScaled : c_L/2+(B^2/mu)*correction ≤ (B^2/mu)*countSurvivors Y small a v := by
    dsimp only [correction,mu,v,P,small,V0,z,Y,w,B,stop] at *
    nlinarith
  have hf : 0 < B^2/mu := div_pos (sq_pos_of_pos hBpos) hmu
  apply (mul_le_mul_iff_right₀ hf).mp
  calc
    _ = c_L/2+(B^2/mu)*correction := by
      change (B^2/mu)*(c_L/2*(mu/B^2)+correction)=_
      field_simp [hmu.ne',hBpos.ne']
    _ ≤ _ := hScaled
end NumberTheoryLean.SourceRootErrorLower


end Erdos970

end OAI
