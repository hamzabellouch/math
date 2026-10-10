import OAI.NumberTheory.JointDickman.Analysis.CanonicalCharacterPairs
import OAI.NumberTheory.JointDickman.Analysis.BinCharacterPairsDischarge

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem canonical_character_pair_limit_proved
    (hKMT : CharacterDistanceDivergence) (hFord : FordUpperSieveInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hM : PrimeReciprocalMertensInput) (hMP : PrimeProductMertensInput)
    (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    {J : ℕ} (hJ : 0 < J) (ν : BinCountState J → ℝ)
    (hν : ∀ r, 0 ≤ ν r) (hνone : ∑ r, ν r = 1)
    (hνmean : ∀ A : ℝ, 0 < A → ∀ r,
      Tendsto (fun x : ℝ => binStateDensity J A x r) atTop (𝓝 (ν r)))
    (χ ψ : AddChar (BinCountState J) ℂ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N,
      χ (canonicalBinVector J (N : ℝ) n)*ψ (canonicalBinVector J (N : ℝ) (n+1)))/(N : ℂ))
      atTop (𝓝 ((∑ r, (ν r : ℂ)*χ r)*(∑ r, (ν r : ℂ)*ψ r))) := by
  have hl := bin_character_pair_limit_proved hKMT hFord hSD hSW hM hMP hMC hJ ν hν hνone hνmean χ ψ
  have hsmall := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℂ) (1 : ℂ)
  have hfull := hl.add hsmall
  rw [add_zero] at hfull
  apply hfull.congr'
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (canonicalBinVector_val hJ 2),
    eventually_gt_atTop 0] with N hcounts hN
  have hp (n : ℕ) (hn : n ∈ range N) :
      χ (canonicalBinVector J (N : ℝ) n)*ψ (canonicalBinVector J (N : ℝ) (n+1)) =
      binLabel (fun i : Fin (J-1) => primeBin (N : ℝ) J (i.val+1)) (binCharacterNodes χ) n *
        binLabel (fun i : Fin (J-1) => primeBin (N : ℝ) J (i.val+1)) (binCharacterNodes ψ) (n+1)+
      (if n = 0 then (1 : ℂ) else 0) := by
    have hnN := mem_range.mp hn
    by_cases hn0 : n = 0
    · subst n
      simp [canonicalBinVector_zero,canonicalBinVector_one]
    · have hle : (n : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast (by omega : n ≤ 2*N)
      have hle' : (n+1 : ℕ) ≤ 2*N := by have := mem_range.mp hn; omega
      rw [binCharacter_canonical χ hn0 (hcounts n (by omega) hle),
        binCharacter_canonical ψ (by omega) (hcounts (n+1) (by omega) (by exact_mod_cast hle')),
        ite_eq_right hn0,add_zero]
  have he := sum_congr rfl hp
  rw [sum_add_distrib,sum_ite_eq',ite_eq_left (mem_range.mpr hN)] at he
  rw [he,add_div]

end JointDickman

end OAI
