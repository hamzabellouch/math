import OAI.NumberTheory.JointDickman.Amplification.BinPrefixMeans

namespace OAI

/-! # Pair limits for the unit bin labels attached to finite characters -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem star_binLabel_star {ι : Type*} [Fintype ι] (E : ι → Finset ℕ) (z : ι → ℂ) (n : ℕ) :
    star (binLabel E (fun i => star (z i)) n) = binLabel E z n := by
  by_cases hn : n = 0
  · simp [hn]
  · simp only [binLabel_apply hn,star_prod,star_pow,star_star]

theorem bin_character_pair_limit
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
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
      binLabel (fun i : Fin (J-1) => primeBin (N : ℝ) J (i.val+1)) (binCharacterNodes χ) n *
      binLabel (fun i : Fin (J-1) => primeBin (N : ℝ) J (i.val+1)) (binCharacterNodes ψ) (n+1))/(N : ℂ))
      atTop (𝓝 ((∑ r, (ν r : ℂ)*χ r)*(∑ r, (ν r : ℂ)*ψ r))) := by
  let μ := binDistributionMean ν (binCharacterNodes ψ)
  have hμ : ‖μ‖ ≤ 1 := binDistributionMean_norm_le_one ν hν hνone _ (binCharacterNodes_norm ψ)
  have hcenter (A : ℝ) (hA : 0 < A) := centeredBinPrefix_tendsto hJ ν hνmean (binCharacterNodes ψ) hA
  have hcor := centeredBinCorrelation_tendsto hMR hMRT hKMT hFord hSD hSW hM hMP hMC
    J hJ (fun i : Fin (J-1) => i.val+1) (fun _ => by omega)
    (fun i => star (binCharacterNodes χ i))
    (fun i => by simpa only [norm_star] using binCharacterNodes_norm χ i)
    hJ (binCharacterNodes ψ) (binCharacterNodes_norm ψ) μ hμ hcenter
  have hfirst := binLabel_prefix_mean hJ ν hνmean (binCharacterNodes χ) (binCharacterNodes_norm χ)
  have hh := hcor.add (hfirst.mul_const μ)
  convert hh using 1
  · funext N
    simp only [centeredBinCorrelation,movingBinLabel,star_binLabel_star]
    rw [div_mul_eq_mul_div,sum_mul,← add_div,← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro n _
    ring
  · simp only [zero_add,μ,binCharacter_mean]

end JointDickman

end OAI
