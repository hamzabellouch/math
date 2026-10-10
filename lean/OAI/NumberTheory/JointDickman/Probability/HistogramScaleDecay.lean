import OAI.NumberTheory.JointDickman.Amplification.CoarseGrid
import OAI.NumberTheory.JointDickman.Probability.KernelDenominatorSum

namespace OAI

/-! # Uniform decay of the histogram and residue denominator losses -/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem channelMesh_scale_bound {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    (B : ℝ)*channelMesh (channelFineCount m B) ≤ (B : ℝ)^(-(1/10 : ℝ)) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hn := channelFineCount_pos hm hB
  have hn0 : (0 : ℝ) < channelFineCount m B := by exact_mod_cast hn
  have hp := Real.rpow_pos_of_pos hB0 (11/10 : ℝ)
  have hmesh : channelMesh (channelFineCount m B) ≤ 1/(B : ℝ)^(11/10 : ℝ) := by
    unfold channelMesh
    apply (div_le_div_iff₀ hn0 hp).mpr
    simpa only [one_mul] using channelFineCount_lower (B := B) hm
  calc
    _ ≤ (B : ℝ)*(1/(B : ℝ)^(11/10 : ℝ)) := mul_le_mul_of_nonneg_left hmesh hB0.le
    _ = _ := by
      rw [mul_one_div]
      calc
        (B : ℝ)/(B : ℝ)^(11/10 : ℝ) = (B : ℝ)^(1 : ℝ)/(B : ℝ)^(11/10 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_sub hB0]; norm_num

/-- After summing denominators, both actual small losses still tend to zero,
uniformly for eta*T <= j and the required polynomial modulus range. -/
theorem histogram_residue_denominator_decay
    (hMP : PublishedInputs.PrimeProductMertensInput) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ (j Q : ℕ) (T : ℝ), 0 < j → 0 < Q → 0 ≤ T → η*T ≤ j → j*Q ≤ B^15 →
      (T/j)*kernelDenominatorSum j Q*
        ((B : ℝ)*channelMesh (channelFineCount m B)+(B : ℝ)^(-(1/200 : ℝ))) ≤ ε B := by
  let ε := fun B : ℕ => (1/η)*((B : ℝ)^(-(1/20 : ℝ))+(B : ℝ)^(-(1/400 : ℝ)))
  refine ⟨ε, ?_, ?_⟩
  · have h₁ := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/20)).comp tendsto_natCast_atTop_atTop
    have h₂ := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/400)).comp tendsto_natCast_atTop_atTop
    simpa only [ε,Function.comp_def,add_zero,mul_zero] using (h₁.add h₂).const_mul (1/η)
  · intro m hm
    filter_upwards [kernelDenominatorSum_subpower hMP (by norm_num : (0 : ℝ) < 1/400),
      eventually_ge_atTop 1] with B hden hB
    intro j Q T hj hQ hT hlag hscale
    have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
    have hB0 : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    have hratio : T/(j : ℝ) ≤ 1/η := by
      apply (div_le_div_iff₀ hj0 hη).mpr
      nlinarith
    have hloss : (B : ℝ)^(1/400 : ℝ)*
        ((B : ℝ)*channelMesh (channelFineCount m B)+(B : ℝ)^(-(1/200 : ℝ))) ≤
        (B : ℝ)^(-(1/20 : ℝ))+(B : ℝ)^(-(1/400 : ℝ)) := by
      calc
        _ ≤ (B : ℝ)^(1/400 : ℝ)*
            ((B : ℝ)^(-(1/10 : ℝ))+(B : ℝ)^(-(1/200 : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hB0.le _)
          exact add_le_add (channelMesh_scale_bound (B := B) hm (by omega)) (le_refl _)
        _ = (B : ℝ)^(-(39/400 : ℝ))+(B : ℝ)^(-(1/400 : ℝ)) := by
          rw [mul_add,← Real.rpow_add hB0,← Real.rpow_add hB0]
          norm_num
        _ ≤ _ := add_le_add (Real.rpow_le_rpow_of_exponent_le hB1
          (by norm_num : (-(39/400 : ℝ)) ≤ -(1/20))) (le_refl _)
    have hden0 : 0 ≤ kernelDenominatorSum j Q := by
      unfold kernelDenominatorSum
      positivity
    have hmesh0 : 0 ≤ (B : ℝ)*channelMesh (channelFineCount m B)+(B : ℝ)^(-(1/200 : ℝ)) := by
      unfold channelMesh
      positivity
    calc
      _ ≤ (1/η)*(B : ℝ)^(1/400 : ℝ)*
          ((B : ℝ)*channelMesh (channelFineCount m B)+(B : ℝ)^(-(1/200 : ℝ))) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hratio (hden j Q hj hQ hscale) hden0 (by positivity)) hmesh0
      _ ≤ ε B := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hloss (by positivity)

end JointDickman

end OAI
