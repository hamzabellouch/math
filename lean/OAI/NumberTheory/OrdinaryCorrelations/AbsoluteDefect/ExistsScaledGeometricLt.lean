import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.InverseBinGeometric
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.HalfGeometricIdentity

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

lemma exists_scaled_geometric_lt {A ε : ℝ} (hA : 0≤A) (hε : 0<ε) :
    ∃n : ℕ,A*(1/2:ℝ)^n<ε := by
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one
    (by positivity : 0<ε/(A+1)) (by norm_num : (1/2:ℝ)<1)
  refine ⟨n,?_⟩
  have hh := (lt_div_iff₀ (by positivity : 0<A+1)).mp hn
  have hp := pow_nonneg (by norm_num : (0:ℝ)≤1/2) n
  nlinarith only [hh,hp]

theorem dyadic_mellin_small {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {d : ℕ} (hd : 0<d) (χ : DirichletCharacter ℂ d) {ε : ℝ} (hε : 0<ε) :
    ∃D0 : ℕ,0<D0 ∧ ∀D : ℕ,D0≤D →
      ∀ᶠ X : ℕ in atTop,∀S : Finset ℝ,
        (S : Set ℝ).Pairwise (fun t u=>1≤|t-u|) →
        (∀t∈S,|t|≤(X:ℝ)/(D:ℝ)) →
        (∑t∈S,‖dyadicCharacterPolynomial f χ X t‖^2)<ε := by
  classical
  obtain ⟨C,hC,hError⟩ := actual_stage_error
  obtain ⟨s,hs⟩ := exists_scaled_geometric_lt
    (mul_nonneg (by norm_num : (0:ℝ)≤6) hC) (by positivity : 0<ε/4)
  obtain ⟨r,hr,hTerminal⟩ := actual_terminal_energy hf hm hNP hd χ (by positivity : 0<ε/8) s
  let H := 16*(4*r)
  let Kr := 64*(4*r)
  have hH : 16*(4*r)≤2^H := Nat.le_of_lt Nat.lt_two_pow_self
  have hKr : 64*(4*r)≤2^Kr := Nat.le_of_lt Nat.lt_two_pow_self
  obtain ⟨K,hK⟩ := exists_nat_gt
    (max (transitionConstant+Real.exp 1+10) (16*((4*r:ℕ):ℝ)*(1+momentCoefficient)))
  have hKpow : (K:ℝ)≤(2:ℝ)^K := by exact_mod_cast Nat.le_of_lt (Nat.lt_two_pow_self (n:=K))
  have hKtrans : transitionConstant+Real.exp 1+10≤(2:ℝ)^K :=
    (le_max_left _ _).trans (hK.le.trans hKpow)
  have hKterm : 16*((4*r:ℕ):ℝ)*(1+momentCoefficient)≤(2:ℝ)^K :=
    (le_max_right _ _).trans (hK.le.trans hKpow)
  obtain ⟨M,hM⟩ := exists_scaled_geometric_lt
    (show 0≤2*(firstSampleConstant+2) by have := firstSampleConstant_nonneg; positivity)
    (by positivity : 0<ε/4)
  let B := (H+4*s+2*Kr+K+70)+(2*H+s+30)+(H+s+20)+(H+10+M)
  have hB1 : H+4*s+2*Kr+K+70≤B := by dsimp [B]; omega
  have hB2 : 2*H+s+30≤B := by dsimp [B]; omega
  have hB3 : H+s+20≤B := by dsimp [B]; omega
  have hB4 : H+10+M≤B := by dsimp [B]; omega
  let D0 := 4*2^(F B s 0)
  have hDp : 0<D0 := by dsimp [D0]; positivity
  refine ⟨D0,hDp,?_⟩
  intro D hD
  have hD0 : 4*2^(F B s 0)≤D := hD
  have hDp' : 0<D := hDp.trans_le hD
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
