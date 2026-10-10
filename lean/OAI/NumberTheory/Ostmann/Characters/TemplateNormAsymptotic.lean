import OAI.NumberTheory.Ostmann.Characters.PrimeDyadicCoverSource
import OAI.NumberTheory.Ostmann.Characters.TemplateNormAsymptoticNormalization
import OAI.NumberTheory.Ostmann.Characters.TemplateNormAsymptoticPrecision

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.TemplateNormAsymptotic
open Filter Construction Preliminaries BinaryExposure FrequencyExposure BinaryPriorExposure Arithmetic
open HistoryFrequencyLabels HistoryFrequencyBudget Template
attribute [local instance] Classical.propDecidable

theorem retained_square_sum_eventually (j K : ℕ) (hj : j ≤ K)
    {z a α β c δ : ℝ} (hz : 0 < z) (ha : 0 < a) (hα : 0 < α)
    (hβ : 0 ≤ β) (_hc : 0 ≤ c) (hδ : 0 < δ) (W : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ N : ℕ,
      ∀ E : List Bool → Finset (PrimeUpTo N),
      ∀ hE : ∀ q, 0 < primeShellMass (E q),
      (∀ q, Real.exp (-c*L) ≤ primeShellMass (E q)) →
      (∀ q, ∀ p ∈ E q, Real.exp (α*L) ≤ Real.log p.val) →
      (∀ q, ∀ p ∈ E q, Real.log p.val ≤ Real.exp (β*L)) →
      ∀ k : ℕ, ∀ C : State k j,
      ∀ B V : (l : ℕ) → State k (l+1) → ℤ,
      ∀ extra : (l : ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop,
      ∀ mask : (l : ℕ) → ℤ → State k l → Prop, ∀ X : ℝ, 0 < X →
      BinaryPriorExposure.mean (fun q => primeShellPrior (E q) (hE q)) j []
        (fun x => ∑ h : SupportedHistory (ranges a (⌊z*L⌋₊ : ℝ) j) j [],
          ‖retainedHistoryWeight k B V extra mask X (a*(⌊z*L⌋₊ : ℝ)) W j h.val.1
            (installWords k j C (chosenPrimeWords k j x)) h.val.2‖^2) ≤
      Real.exp ((β+c+1)*(2:ℝ)^j*L+δ*(⌊z*L⌋₊ : ℝ)) := by
  obtain ⟨ε,hε,hcancel⟩ := normalized_retained_factor_eventually j ha hδ
  obtain ⟨A,hA,hbound⟩ := actual_retained_square_sum_bound ε hε
  filter_upwards [precision_lt_prime_eventually hz hα ha.le j K,
    (word_tendsto hz).eventually (hcancel A W),
    eventually_ge_atTop (0 : ℝ),eventually_ge_atTop (Real.log PrimeDyadicCover.costConstant)]
    with L hprec hcancel hL hlarge
  intro N E hE hZ hmin hmax k C B V extra mask X hX
  let S := ranges a (⌊z*L⌋₊ : ℝ) j
  let U := PrimeDyadicCover.sourceUpper β L
  let precision : SupportedHistory S j [] → ℕ :=
    fun h => (modulus j [] h.val.1 h.val.2)^(K+2)
  have hS : ∀ q s, s ∈ S q → s ≠ 0 := by
    intro q s hs
    exact (mem_signedRange _ _).mp hs |>.1
  have hpos (h : SupportedHistory S j []) : 0 < precision h :=
    pow_pos (modulus_pos S hS h.property) _
  have hlt (h : SupportedHistory S j []) (q : List Bool) (p : PrimeUpTo N) (hp : p ∈ E q) :
      precision h < p.val := hprec _ _ h.property _ (primeUpTo_prime p) (hmin q p hp)
  let cover : SupportedHistory S j [] → List Bool → PrimeDyadicCover.Index U → ℕ :=
    fun h _ i => PrimeDyadicCover.lower (precision h) U i
  have hcover (h : SupportedHistory S j []) (q : List Bool) (p : PrimeUpTo N) (hp : p ∈ E q) :
      ∃ i, cover h q i ≤ p.val ∧ p.val ≤ 2*cover h q i :=
    PrimeDyadicCover.source_shell_covers (hpos h) (E q)
      (fun p hp => (hlt h q p hp).le) (hmax q) p hp
  have hcop (h : SupportedHistory S j []) (q : List Bool) (p : PrimeUpTo N) (hp : p ∈ E q) :
      p.val.Coprime (precision h) :=
    PrimeDyadicCover.prime_coprime_of_lt (hpos h) (primeUpTo_prime p) (hlt h q p hp)
  have hh := hbound k K j hj [] S hS N (PrimeDyadicCover.Index U) E hE cover
    (fun h _ i => PrimeDyadicCover.lower_ge (precision h) U i) hcover hcop
    C B V extra mask X (a*(⌊z*L⌋₊ : ℝ)) W hX
  have hcost := PrimeDyadicCover.source_shell_binary_cost_le_exp E hE hβ hL hZ hlarge j []
  have hhist : 0 ≤ historyTotal S (ReducedFrequencyTree.factor ε A) j [] := by
    apply Finset.sum_nonneg
    intro h _
    exact reduced_literalWeight_nonneg ε A j [] h.val.1 h.val.2
  have hleaf : 0 ≤ (leafFourierBound*Real.exp ((-(a*(⌊z*L⌋₊ : ℝ))+W)/2))^((2^j)*2) := by
    exact pow_nonneg (mul_nonneg leafFourierBound_pos.le (Real.exp_pos _).le) _
  calc
    _ ≤ (leafFourierBound*Real.exp ((-(a*(⌊z*L⌋₊ : ℝ))+W)/2))^((2^j)*2)*
        ((BinaryPriorExposure.cost
          (fun q => shellResidueCost (J:=PrimeDyadicCover.Index U) (E q) (hE q)) j []:ℝ)*
            historyTotal S (ReducedFrequencyTree.factor ε A) j []) := hh
    _ ≤ (leafFourierBound*Real.exp ((-(a*(⌊z*L⌋₊ : ℝ))+W)/2))^((2^j)*2)*
        (Real.exp ((β+c+1)*(2:ℝ)^j*L)*
          historyTotal S (ReducedFrequencyTree.factor ε A) j []) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcost hhist) hleaf
    _ = Real.exp ((β+c+1)*(2:ℝ)^j*L)*
        ((leafFourierBound*Real.exp ((-a*(⌊z*L⌋₊ : ℝ)+W)/2))^((2^j)*2)*
          historyTotal S (ReducedFrequencyTree.factor ε A) j []) := by
      simp only [neg_mul]
      ring
    _ ≤ Real.exp ((β+c+1)*(2:ℝ)^j*L)*Real.exp (δ*(⌊z*L⌋₊ : ℝ)) :=
      mul_le_mul_of_nonneg_left hcancel (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

end Ostmann.Characters.TemplateNormAsymptotic

end

end OAI
