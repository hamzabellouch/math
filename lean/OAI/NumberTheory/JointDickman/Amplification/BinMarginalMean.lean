import OAI.NumberTheory.JointDickman.Amplification.BinMarginalInput

namespace OAI

/-! # Centered prefix means supplied by the one-variable distribution -/
namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def binDistributionMean {J : ℕ} (ν : BinCountState J → ℝ)
    (ζ : Fin (J-1) → ℂ) : ℂ := ∑ r, (ν r : ℂ)*∏ i, ζ i^(r i).val

noncomputable def centeredBinPrefix (J : ℕ) (ζ : Fin (J-1) → ℂ) (μ : ℂ)
    (A x : ℝ) : ℂ :=
  (∑ n ∈ Ioc 0 ⌊A*x⌋₊,
    (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ n-μ))/(A*x : ℂ)

theorem binDistributionMean_norm_le_one {J : ℕ} (ν : BinCountState J → ℝ)
    (hν : ∀ r, 0 ≤ ν r) (hνone : ∑ r, ν r = 1)
    (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1) :
    ‖binDistributionMean ν ζ‖ ≤ 1 := by
  unfold binDistributionMean
  calc
    _ ≤ ∑ r : BinCountState J, ‖(ν r : ℂ)*∏ i, ζ i^(r i).val‖ := norm_sum_le _ _
    _ = ∑ r : BinCountState J, ν r := by
      apply sum_congr rfl
      intro r _
      simp [norm_prod,norm_pow,hζ,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hν r)]
    _ = 1 := hνone

theorem centeredBinPrefix_tendsto {J : ℕ} (hJ : 0 < J)
    (ν : BinCountState J → ℝ)
    (hν : ∀ A : ℝ, 0 < A → ∀ r,
      Tendsto (fun x : ℝ => binStateDensity J A x r) atTop (𝓝 (ν r)))
    (ζ : Fin (J-1) → ℂ) {A : ℝ} (hA : 0 < A) :
    Tendsto (centeredBinPrefix J ζ (binDistributionMean ν ζ) A) atTop (𝓝 0) := by
  have hmean := canonical_binLabel_mean hJ ν hν ζ hA
  have hfloor := (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp
    ((tendsto_nat_floor_div_atTop (R := ℝ)).comp (tendsto_id.const_mul_atTop hA))
  have hh := hmean.sub (hfloor.const_mul (binDistributionMean ν ζ))
  convert hh using 1
  · funext x
    simp only [centeredBinPrefix,binDistributionMean,sum_sub_distrib,sum_const,
      nsmul_eq_mul,Nat.card_Ioc,Nat.sub_zero,sub_div,Complex.ofReal_div,Complex.ofReal_natCast,
      Complex.ofReal_mul,Function.comp_apply,id_eq]
    ring
  · simp [binDistributionMean]

theorem centeredBinPrefix_of_published
    (hBill : PublishedInputs.FiniteBinDistributionInput)
    {J : ℕ} (hJ : 2 ≤ J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1) :
    ∃ μ : ℂ, ‖μ‖ ≤ 1 ∧ ∀ A : ℝ, 0 < A →
      Tendsto (centeredBinPrefix J ζ μ A) atTop (𝓝 0) := by
  obtain ⟨ν,hν,hνone,hmeans,_⟩ := hBill J hJ
  exact ⟨binDistributionMean ν ζ,binDistributionMean_norm_le_one ν hν hνone ζ hζ,
    fun A hA => centeredBinPrefix_tendsto (by omega) ν hmeans ζ hA⟩

end JointDickman

end OAI
