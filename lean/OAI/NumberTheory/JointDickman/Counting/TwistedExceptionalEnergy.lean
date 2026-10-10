import OAI.NumberTheory.JointDickman.Counting.AuxiliaryPowerEnergy
import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryBandChoice
import OAI.NumberTheory.JointDickman.Amplification.TwistedAuxiliaryCofactor

namespace OAI

/-! # Vanishing exceptional energy for nonprincipal bin interpolants -/
namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical Topology

theorem twisted_exceptional_energy (P₀ Q₀ : ℝ)
    (hP₀ : 2*Real.exp 1 ≤ P₀) (hPQ : P₀ ≤ Q₀)
    (hlogP : 1 ≤ Real.log P₀) (hQ₀ : 1 ≤ Real.log Q₀)
    (hH₀ : 2 ≤ mrtBaseResolution P₀ Q₀ (1/12))
    {ι : Type*} [Fintype ι] {J : ℕ} (hJ : 0 < J) (j : ι → ℕ) (hj : ∀ i, 1 ≤ j i)
    (E₀ : Finset ℕ) (hE₀ : ∀ p ∈ E₀, p.Prime)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      let B := canonicalMellinBands P₀ Q₀ (1/12)
      let L := mellinBandCount Q₀ (Real.sqrt (Real.log (N:ℝ))) hQ₀
      ∀ x : ℝ, (N:ℝ)/A ≤ x → ∀ (m : ℕ) (a : ι → Fin m) (w : ℕ → ℝ),
      (∀ p ∈ E₀, 0 ≤ w p ∧ w p ≤ 1) →
      let F := twistedWeightedBinInterpolant (fun i => primeBin x J (j i))
        (finitePrimeWeight E₀ w) a χ
      ∀ S : Set ℝ, MeasurableSet S → S ⊆ Set.Ioc (-(N:ℝ)) N →
      S ⊆ mrtNoSmallBand B.bins (B.polynomial F) B.threshold L →
      (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤ ε := by
  let H := max 2 (90112*Real.exp 1/ε)
  have hH : 2 ≤ H := le_max_left _ _
  have hHpos : 0 < H := by linarith
  have hwidth : 22528*Real.exp 1/H ≤ ε/4 := by
    apply (div_le_iff₀ hHpos).mpr
    have hh := (div_le_iff₀ hε).mp (show 90112*Real.exp 1/ε ≤ H from le_max_right _ _)
    nlinarith only [hh]
  have hd : 0 < min (1/12:ℝ) ((1:ℝ)/J) := lt_min (by norm_num) (by positivity)
  obtain ⟨α,β,hα,hαβ,hβsmall,hdensity⟩ :=
    exists_auxiliary_power_band (show 0<ε/(192*Real.exp 1) by positivity) hd
  have hβ : β < 1/12 := hβsmall.trans_le (min_le_left _ _)
  have hαJ : α ≤ (1:ℝ)/J := hαβ.trans (hβsmall.le.trans (min_le_right _ _))
  obtain ⟨D,hD,henergy⟩ := auxiliary_power_energy P₀ Q₀ H hP₀ hPQ hlogP hQ₀ hH₀ hH hα hαβ hβ
  let b := min 1 (ε/(4*D))
  have hb : 0 < b := lt_min (by norm_num) (by positivity)
  have hb1 : b ≤ 1 := min_le_left _ _
  have hbcost : D*b^2 ≤ ε/4 := by
    have hh := (le_div_iff₀ (by positivity : 0<4*D)).mp
      (show b ≤ ε/(4*D) from min_le_right _ _)
    have hb2 : b^2 ≤ b := by nlinarith only [hb,hb1]
    nlinarith only [hh,mul_le_mul_of_nonneg_left hb2 hD.le]
  filter_upwards [henergy (ε/4) (by positivity),
    twisted_auxiliary_cofactor hJ j hj E₀ hE₀ hA hH hα hαβ hαJ hβ χ hχ hb,
    hdensity,eventually_ge_atTop (1:ℕ)] with N henergy hcofactor hdensity hN
  dsimp only at henergy ⊢
  intro x hx m a w hw S hSm hSN hSres
  let F := twistedWeightedBinInterpolant (fun i => primeBin x J (j i))
    (finitePrimeWeight E₀ w) a χ
  have hmult : F.IsMultiplicative := twistedWeightedBinInterpolant_multiplicative _ _
    (finitePrimeWeight_multiplicative hE₀ w) a χ
  have hnorm : ∀ n, ‖F n‖ ≤ 1 := by
    intro n
    apply twistedWeightedBinInterpolant_norm_le _ _ _ a χ n
    intro v
    rw [abs_of_nonneg (finitePrimeWeight_bounds hw v).1]
    exact (finitePrimeWeight_bounds hw v).2
  have he := henergy F (fun _ _ _ _ hcop => hmult.2 hcop) hnorm
    S N b hSm (by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<1) hN) le_rfl hSN hSres
    (by
      intro k hk t ht
      apply hcofactor x hx m a w hw k hk t
      obtain ⟨hlo,hhi⟩ := hSN ht
      exact abs_le.mpr ⟨hlo.le,hhi⟩)
  have hdensity' : 48*Real.exp 1*
      (((Ioc N (2*N)).filter (mrtPrimeAvoids (mrtPrimeBand ((N:ℝ)^α) ((N:ℝ)^β)))).card:ℝ)/N ≤ ε/4 := by
    have hh := mul_le_mul_of_nonneg_left hdensity (by positivity : 0 ≤ 48*Real.exp 1)
    convert hh using 1 <;> field_simp
    norm_num
  change (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤ ε
  linarith only [he,hwidth,hbcost,hdensity']

end JointDickman

end OAI
