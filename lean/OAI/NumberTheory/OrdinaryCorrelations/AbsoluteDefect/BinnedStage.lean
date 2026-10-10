import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicCofactorMellin
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeWindow
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.WeightedSquare
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SquareDivGe

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

namespace SourcePrimeFactor
open OrdinaryCorrelations OrdinaryNarrowGrid OrdinaryDirichletMeanSquare
open Finset Filter

def binnedStage (f : ℕ → ℂ) {d : ℕ} (χ : DirichletCharacter ℂ d)
    (q r R X : ℕ) (t : ℝ) : ℂ :=
  ∑i∈grid q r R,primeMellin f χ (primeBin i) t*
    dyadicCofactorMellin f χ (primeWindow q r R) (evenBinLength X i) t

lemma prime_window_harmonic (q r R : ℕ) (hq : 0<q) :
    (∑i∈grid q r R,∑p∈primeBin i,(p:ℝ)⁻¹)=∑p∈primeWindow q r R,(p:ℝ)⁻¹ := by
  rw [prime_window_bins]
  exact (sum_biUnion (prime_bins_disjoint q r R hq)).symm

theorem terminal_binned_sparse {f : ℕ → ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {d : ℕ} (hd : 0<d) (χ : DirichletCharacter ℂ d)
    {ε L : ℝ} (hε : 0<ε) (hL : 0≤L) :
    ∃ r : ℕ,0<r ∧ ∀ q a R : ℕ,0<q →
      (∑p∈primeWindow q a R,(p:ℝ)⁻¹)≤L →
      ∀ D : ℕ,4*(q*2^(a+R))≤D →
      ∀ᶠ X : ℕ in atTop,∀ S : Finset ℝ,
        (S : Set ℝ).Pairwise (fun t u => 1≤|t-u|) →
        (∀t∈S,|t|≤(X:ℝ)/(D:ℝ)) → S.card^(2*r)≤X →
        (∑t∈S,‖binnedStage f χ q a R X t‖^2)<ε := by
  classical
  let η : ℝ := ε/(1+L^2)
  have hη : 0<η := by dsimp [η]; positivity
  obtain ⟨b,r,hb,hr,hall⟩ := OrdinarySparseShell.sparse_cofactor_all_lengths
    (characterModulation_bound hf χ) (characterModulation_multiplicative hm χ)
    (characterModulation_nonpretentious hNP hd χ) hη
  refine ⟨r,hr,?_⟩
  intro q a R hq hmass D hD
  let P := primeWindow q a R
  let I := grid q a R
  have hbin (i : ℕ×ℕ) (hi : i∈I) :
      ∀ᶠ X : ℕ in atTop, ∀ S : Finset ℝ,
        (S : Set ℝ).Pairwise (fun t u => 1≤|t-u|) →
        (∀t∈S,|t|≤(X:ℝ)/(D:ℝ)) → S.card^(2*r)≤X →
        (∑t∈S,‖dyadicCofactorMellin f χ P (evenBinLength X i) t‖^2)<η := by
    have hu : 0<upper i := (grid_lower_pos q a R hq hi).trans_le (lower_le_upper i)
    have hK : 0<2*upper i := by omega
    have hD' : 2*(2*upper i)≤D := by
      have hh := upper_le_endpoint q a R hi
      omega
    have hlim := Nat.tendsto_div_const_atTop hK.ne'
    have hprimes : ∀ᶠ X : ℕ in atTop, ∀p∈P,p^r≤(X/(2*upper i))^b := by
      apply (eventually_all_finset P).mpr
      intro p hp
      filter_upwards [hlim.eventually (eventually_ge_atTop (p^r))] with X hX
      exact hX.trans (Nat.le_self_pow (by omega) _)
    filter_upwards [hlim.eventually hall,hprimes,
      eventually_ge_atTop (4*(2*upper i)^2),eventually_ge_atTop (2*upper i)] with X hX hp hsq hXK
    intro S hsep hheight hcard
    have hh := hX P
      (fun p hpm => ⟨(mem_filter.mp hpm).2,hp p hpm⟩) S hsep
      (fun t ht => (hheight t ht).trans (OrdinaryDivisionHeight.div_height hK hXK hD'))
      (OrdinaryDivisionHeight.power_card_div hK hsq hcard)
    simpa only [OrdinarySmoothRough.cofactorEnergy,←dyadicCofactorMellin_eq,evenBinLength]
      using hh
  filter_upwards [(eventually_all_finset I).mpr hbin] with X hX
  intro S hsep hheight hcard
  have he := OrdinaryWeightedBinEnergy.energy_uniform I S
    (fun i => primeMellin f χ (primeBin i))
    (fun i => dyadicCofactorMellin f χ P (evenBinLength X i))
    (fun i => ∑p∈primeBin i,(p:ℝ)⁻¹)
    (fun i hi => sum_nonneg (fun p hp => by positivity))
    (fun i hi t ht => norm_primeMellin hf χ (primeBin i) t) hη.le hL
    (by rw [prime_window_harmonic q a R hq]; exact hmass)
    (fun i hi => (hX i hi S hsep hheight hcard).le)
  change (∑t∈S,‖binnedStage f χ q a R X t‖^2)≤L^2*η at he
  apply he.trans_lt
  dsimp [η]
  have hden : 0<1+L^2 := by positivity
  rw [←mul_div_assoc]
  apply (div_lt_iff₀ hden).mpr
  nlinarith

end SourcePrimeFactor

end

end OAI
