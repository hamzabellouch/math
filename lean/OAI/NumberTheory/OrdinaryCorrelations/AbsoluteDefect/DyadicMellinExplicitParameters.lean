import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.InverseBinGeometric
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.HalfGeometricIdentity
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ActualTerminalEnergyExplicit

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction

namespace OrdinaryChainScales
open OrdinaryCorrelations SourcePrimeFactor OrdinaryNarrowGrid OrdinaryDirichletMeanSquare
open OrdinaryFrequencyChain Finset Filter
attribute [local irreducible] E F mesh binQ binStart binWidth binLog amplifier

theorem dyadic_mellin_explicit_parameters :
    ∃ C CT : ℝ, 0≤C ∧ 0≤CT ∧
    ∀ {ε : ℝ}, 0<ε → ∀ s J M H Kr K B : ℕ, 0<J →
      6*C*(1/2:ℝ)^s<ε/4 →
      2120/(J:ℝ)≤(ε/8)/(1+(CT+(s:ℝ)*Real.log 2)^2) →
      2*(firstSampleConstant+2)*(1/2:ℝ)^M<ε/4 →
      let r := 16*(576*J^2+96*J+4)
      16*(4*r)≤2^H → 64*(4*r)≤2^Kr →
      16*((4*r:ℕ):ℝ)*(1+momentCoefficient)≤(2:ℝ)^K →
      transitionConstant+Real.exp 1+10≤(2:ℝ)^K →
      H+4*s+2*Kr+K+70≤B → 2*H+s+30≤B →
      H+s+20≤B → H+10+M≤B →
      ∀ {f : ℕ→ℂ}, OneBounded f → Multiplicative f → UniformlyNonpretentious f →
      ∀ {d : ℕ}, 0<d → ∀χ : DirichletCharacter ℂ d,
      ∀D : ℕ,4*2^(F B s 0)≤D →
      ∀ᶠ X : ℕ in atTop,∀S : Finset ℝ,
        (S : Set ℝ).Pairwise (fun t u=>1≤|t-u|) →
        (∀t∈S,|t|≤(X:ℝ)/(D:ℝ)) →
        (∑t∈S,‖dyadicCharacterPolynomial f χ X t‖^2)<ε := by
  classical
  obtain ⟨C,hC,hError⟩ := actual_stage_error
  obtain ⟨CT,hCT,hTerm⟩ := actual_terminal_energy_explicit
  refine ⟨C,CT,hC,hCT,?_⟩
  intro ε hε s J M H Kr K B hJ hs hRate hM
  dsimp only
  intro hH hKr hKterm hKtrans hB1 hB2 hB3 hB4 f hf hm hNP d hd χ D hD0
  let r := 16*(576*J^2+96*J+4)
  have hr : 0<r := by dsimp [r]; positivity
  have hDp' : 0<D := lt_of_lt_of_le (by positivity : 0<4*2^(F B s 0)) hD0
  have hTerminal := hTerm hf hm hNP hd χ (by positivity : 0<ε/8) s J hJ hRate
  have he := hTerminal H Kr K B hH hKr hKterm hB1 hB2 D hD0
  filter_upwards [he] with X hT
  obtain ⟨J,hlo,hhi,hterminal⟩ := hT
  have hcut := all_previous_power_cutoffs (by omega : 1≤4*r) hlo
  intro S hsep hheight
  have hheightX : ∀t∈S,|t|≤(X:ℝ) := fun t ht=>(hheight t ht).trans
    (div_le_self (Nat.cast_nonneg X) (by exact_mod_cast hDp'))
  let good := allBinsGood (fun j=>grid (binQ B H s j) (binStart B H s j) (binWidth B s j))
    (fun j i=>primeMellin f χ (primeBin i)) (fun j i=>threshold H j (binLog B H s j i))
  let stage := fun j=>binnedStage f χ (binQ B H s j) (binStart B H s j) (binWidth B s j) X
  let F0 := dyadicCharacterPolynomial f χ X
  have hchain := first_good_energy S good (J+1) F0 stage
  have hgood := all_good_energy hf χ hKtrans (by omega : H+4*s+K+70≤B) hB2 hD0
    (fun i hi=>dyadic_cutoff_of_power (hcut i hi)) S hsep hheight
  change (∑j∈range (J+1),∑t∈firstGood S good j,‖stage j t‖^2)≤
    (firstSampleConstant+2)*Real.exp (-(mesh B H s 0:ℝ)) at hgood
  have hggeom := mesh_zero_exp (s:=s) hB4
  have hgoodsmall : 2*(∑j∈range (J+1),∑t∈firstGood S good j,‖stage j t‖^2)<ε/4 := by
    have hh := mul_le_mul_of_nonneg_left hggeom
      (show 0≤2*(firstSampleConstant+2) by have := firstSampleConstant_nonneg; positivity)
    nlinarith only [hgood,hh,hM]
  have herr (i : ℕ) (hi : i≤J) : (∑t∈S,‖F0 t-stage i t‖^2)≤C*(1/2:ℝ)^(s+i) := by
    have hh := hError f hf hm χ B H s i X hB3 (hcut i hi) S hsep hheightX
    simpa only [F0,stage,norm_sub_rev] using hh
  have herrs : (∑i∈range (J+1),∑t∈S,‖F0 t-stage i t‖^2)≤2*C*(1/2:ℝ)^s := by
    apply le_trans _ (geometric_error_sum hC s (J+1))
    exact sum_le_sum (fun i hi=>herr i (by have := mem_range.mp hi; omega))
  have herr0 := herr 0 (by omega)
  simp only [Nat.add_zero] at herr0
  have herrsmall : 2*(∑i∈range (J+1),∑t∈S,‖F0 t-stage i t‖^2)+
      2*(∑t∈S,‖F0 t-stage 0 t‖^2)<ε/4 := by nlinarith only [herrs,herr0,hs]
  have hter := hterminal S hsep hheight
  change (∑t∈surviving S good (J+1),‖stage 0 t‖^2)<ε/8 at hter
  change (∑t∈S,‖F0 t‖^2)<ε
  linarith only [hchain,hgoodsmall,herrsmall,hter,hε]

end OrdinaryChainScales

end

end OAI
