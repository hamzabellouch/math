import OAI.NumberTheory.CubicMoment.Estimates.SmallBCoreOrdinary
import OAI.NumberTheory.CubicMoment.Estimates.CoreHybridScale

namespace OAI

/-! Uniform core bounds with an explicit logarithmic cutoff parameter.
Ordinary character duality handles moderately small conductors and the
cubic sieve handles the remaining ones. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem smallB_core_hybrid_sieve (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (N B V : ℝ) (i j : ℕ), 65536 ≤ N → 0 ≤ B → 0 < V →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ N) →
      V/5832 ≤ coreDyadicConductor i j → 8*coreDyadicConductor i j ≤ N^(3/4:ℝ) →
      H ⊆ coreDyadicBlock B i j →
      (∑ h ∈ H, ‖∑ b ∈ S, β b*cubicSymbol b h‖^2) ≤
        K*B^(1/3:ℝ)*(N*(V/5832)^(-(1/4:ℝ))+N^(1-1/20000:ℝ))*
          ∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨Co,hCo,ho⟩ := smallB_core_ordinary_sieve hHuxley
  obtain ⟨Ch,hCh,hh⟩ := smallB_core_block_sieve hHuxley
    (by norm_num : (0:ℝ) < 1/10000)
  refine ⟨max Co (2*Ch),lt_of_lt_of_le hCo (le_max_left _ _),?_⟩
  intro S H β N B V i j hN hB hV hS hcut hsize hH
  have hN1 : 1 ≤ N := by linarith
  have hNp : 0 < N := by linarith
  have hE : 0 ≤ ∑ b ∈ S, ‖β b‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hD : 0 < coreDyadicConductor i j := coreDyadicConductor_pos i j
  by_cases hd : coreDyadicConductor i j ≤ N^(1/1000:ℝ)
  · have hb := ho S H β N B i j hN1 hB hS (core_ordinary_range hN hD.le hd) hH
    have hp := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < V/5832) hcut
      (by norm_num : -(1/4:ℝ) ≤ 0)
    apply hb.trans
    calc
      _ ≤ Co*B^(1/3:ℝ)*(V/5832)^(-(1/4:ℝ))*N*∑ b ∈ S, ‖β b‖^2 := by gcongr
      _ = Co*B^(1/3:ℝ)*(N*(V/5832)^(-(1/4:ℝ)))*∑ b ∈ S, ‖β b‖^2 := by ring
      _ ≤ _ := by
        gcongr
        · exact le_max_left _ _
        · exact le_add_of_nonneg_right (Real.rpow_nonneg hNp.le _)
  · have hb := hh S H β N B i j hN1 hB hS hsize hH
    have hp := core_large_range hN1 (le_of_not_ge hd)
    calc
      _ ≤ Ch*B^(1/3:ℝ)*(N^(2*(1/10000):ℝ)*
          (N/(coreDyadicConductor i j)^(1/3:ℝ)+N^(23/24:ℝ)))*∑ b ∈ S, ‖β b‖^2 := by
        convert hb using 1; ring
      _ ≤ Ch*B^(1/3:ℝ)*(2*N^(1-1/20000:ℝ))*∑ b ∈ S, ‖β b‖^2 := by gcongr
      _ = (2*Ch)*B^(1/3:ℝ)*N^(1-1/20000:ℝ)*∑ b ∈ S, ‖β b‖^2 := by ring
      _ ≤ _ := by
        gcongr
        · exact le_max_right _ _
        · exact le_add_of_nonneg_left (by positivity)

end CubicFirstMoment

end

end OAI
