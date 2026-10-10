import OAI.NumberTheory.JointDickman.Counting.FiniteCountingMean
import OAI.NumberTheory.JointDickman.Counting.ArithmeticBlockPrefix

namespace OAI

/-! # Cancellation of the original arithmetic block average -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem arithmetic_block_centered_mean
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceDivergence) (hFord : FordUpperSieveInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hM : PrimeReciprocalMertensInput) (hMP : PrimeProductMertensInput)
    (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    {A L : ℕ} {cap : ℝ} (hA : 0 < A) (hL : 10000 ≤ L) (hcap : 0 < cap) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧
    ∀ ε : ℝ, 0 < ε → ∃ Cmin : ℝ, 0 ≤ Cmin ∧ ∀ C : ℝ, Cmin ≤ C →
    ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      let T := amplificationMultiplier B
      |arithmeticBlockAverage B L τ C T N (T/A) (A*T)
        (fun n => binLabel (fun j : Fin (J-1) => primeBin (N : ℝ) J (j.val+1)) ζ n-μ)| < ε := by
  obtain ⟨τ,hτ,hτcap,hτsmall,hfinite⟩ := finite_graph_centered_mean hMR hMRT hKMT hFord hSD hSW hM hMP hMC
    hJ ζ hζ μ hμ hmean hA hL hcap
  refine ⟨τ,hτ,hτcap,hτsmall,?_⟩
  intro ε hε
  obtain ⟨Cmin,hCmin,hbound⟩ := hfinite (ε/2) (half_pos hε)
  refine ⟨Cmin,hCmin,?_⟩
  intro C hC
  filter_upwards [hbound C hC,rawArithmeticGraphKernel_uniform_bound (by omega : 1 ≤ L) hτ.le hτsmall,
    amplificationMultiplier_comparable,eventually_gt_atTop 0] with B hb hraw hT hB
  let T := amplificationMultiplier B
  let M := A*T
  let R : ℝ := (arithmeticGraphTriples B T).card
  have hM0 : 0 < M := Nat.mul_pos hA hT.1
  have hbd := (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (16*(M : ℝ)^2*R/(T : ℝ))).eventually
    (Iio_mem_nhds (half_pos hε))
  filter_upwards [hb,hbd] with N hN hboundary
  let z := fun n => binLabel (fun j : Fin (J-1) => primeBin (N : ℝ) J (j.val+1)) ζ n-μ
  have hz : ∀ n, ‖z n‖ ≤ 2 := fun n => norm_centered_binLabel_le_two _ ζ hζ μ hμ n
  have hp := arithmeticBlockAverage_prefix_bound (H := T/A) hB hT.1 hM0 (show 0 ≤ R from Nat.cast_nonneg _)
    (hraw C T N) z hz
  have hsub : (∑ u ∈ range (2*T*N), |(complexEnergy (finiteGraphKernel B L T (T/A) M N u τ C)
      (fun i => z (u+(i.val+1)))).re|/(M : ℝ))/((T : ℝ)*N) ≤
      (∑ u ∈ range (4*T*N), |(complexEnergy (finiteGraphKernel B L T (T/A) M N u τ C)
      (fun i => z (u+(i.val+1)))).re|/(M : ℝ))/((T : ℝ)*N) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply sum_le_sum_of_subset_of_nonneg (range_mono (Nat.mul_le_mul_right N (Nat.mul_le_mul_right T (by decide : 2 ≤ 4))))
    intro u _ _
    positivity
  have he : 16*(M : ℝ)^2*R/((T : ℝ)*N) = (16*(M : ℝ)^2*R/(T : ℝ))/(N : ℝ) := by ring
  rw [he] at hp
  change _ < ε/2 at hN
  change _ < ε/2 at hboundary
  change _ < ε
  linarith

end JointDickman

end OAI
