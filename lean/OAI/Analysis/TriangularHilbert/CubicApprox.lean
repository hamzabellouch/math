import OAI.Analysis.TriangularHilbert.CyclicCompact

namespace OAI

universe uα

section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
noncomputable section

lemma lintegral_enorm_cube {α : Type uα} [MeasurableSpace α] (f : α → ℂ) (μ : Measure α)
    (hf : AEStronglyMeasurable f μ) :
    (∫⁻ x, ‖f x‖ₑ^3 ∂μ) = eLpNorm f 3 μ ^ (3:ℕ) := by
  simpa only [ENNReal.rpow_ofNat,NNReal.coe_ofNat,ENNReal.coe_ofNat] using
    (eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := (3:ℝ≥0)) (by norm_num) hf).symm

lemma norm_cube_le_four_sub (u v : ℂ) : ‖u‖^3 ≤ 4*(‖v‖^3+‖u-v‖^3) := by
  have ht : ‖u‖ ≤ ‖v‖+‖u-v‖ := by
    calc
      ‖u‖ = ‖(u-v)+v‖ := by rw [sub_add_cancel]
      _ ≤ ‖u-v‖+‖v‖ := norm_add_le _ _
      _ = ‖v‖+‖u-v‖ := add_comm _ _
  have hp := pow_le_pow_left₀ (norm_nonneg u) ht 3
  have hn := mul_nonneg (sq_nonneg (‖v‖-‖u-v‖)) (add_nonneg (norm_nonneg v) (norm_nonneg (u-v)))
  nlinarith

lemma tendsto_of_enorm_cube {α : Type uα} {l : Filter α} {f : α → ℂ} {z : ℂ}
    (h : Tendsto (fun n => ‖f n-z‖ₑ^3) l (𝓝 0)) : Tendsto f l (𝓝 z) := by
  have he : Tendsto (fun n => ‖f n-z‖ₑ) l (𝓝 0) := by
    have ht := ((ENNReal.continuous_rpow_const (y := (1:ℝ)/3)).tendsto (0:ℝ≥0∞)).comp h
    have hp (x : ℝ≥0∞) : (x^(3:ℕ))^((1:ℝ)/3) = x := by
      rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
      norm_num
    simpa only [Function.comp_def,hp,ENNReal.zero_rpow_of_pos (by norm_num : 0 < (1:ℝ)/3)] using ht
  have hr := (ENNReal.continuousAt_toReal (by simp : (0:ℝ≥0∞) ≠ ⊤)).tendsto.comp he
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def,ENNReal.toReal_zero,enorm_eq_nnnorm,ENNReal.coe_toReal,coe_nnnorm] using hr

lemma exists_cubic_approximation (f : ℝ×ℝ → ℂ) (hf : MemLp f 3 volume) :
    ∃ g : ℕ → ℝ×ℝ → ℂ, (∀ n, Continuous (g n) ∧ HasCompactSupport (g n) ∧ MemLp (g n) 3 volume) ∧
      ∃ D : ℝ×ℝ → ℝ, Integrable D ∧ (∀ z, 0 ≤ D z) ∧
        (∀ᵐ z : ℝ×ℝ, (∀ n, ‖g n z‖^3 ≤ D z) ∧ Tendsto (fun n => g n z) atTop (𝓝 (f z))) := by
  have hex (n : ℕ) : ∃ g : ℝ×ℝ → ℂ, HasCompactSupport g ∧
      eLpNorm (f-g) 3 volume ≤ (2⁻¹:ℝ≥0∞)^n ∧ Continuous g ∧ MemLp g 3 volume :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) (by simp)
  choose g hgs hge hgc hgm using hex
  let S (z : ℝ×ℝ) : ℝ≥0∞ := ∑' n, ‖f z-g n z‖ₑ^3
  have hm (n : ℕ) : AEMeasurable (fun z => ‖f z-g n z‖ₑ^3) volume :=
    ((hf.aestronglyMeasurable.sub (hgc n).aestronglyMeasurable).enorm).pow_const 3
  have hS : AEMeasurable S volume := AEMeasurable.tsum hm
  have hSint : (∫⁻ z, S z) < ⊤ := by
    rw [show (∫⁻ z, S z) = ∑' n, ∫⁻ z, ‖f z-g n z‖ₑ^3 from lintegral_tsum hm]
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n => ?_))
      ((tsum_geometric_lt_top).mpr (show ((2⁻¹:ℝ≥0∞)^3) < 1 by
        apply pow_lt_one₀ zero_le _ (by norm_num)
        exact ENNReal.inv_lt_one.mpr (show (1:ℝ≥0∞) < 2 by norm_num)))
    rw [lintegral_enorm_cube (fun point => f point - g n point) _
      (hf.aestronglyMeasurable.sub (hgc n).aestronglyMeasurable)]
    exact (ENNReal.pow_le_pow_left (hge n)).trans_eq (by rw [← pow_mul,← pow_mul,Nat.mul_comm])
  have hSfinite : ∀ᵐ z, S z < ⊤ := ae_lt_top' hS hSint.ne
  let D (z : ℝ×ℝ) : ℝ := 4*(‖f z‖^3+(S z).toReal)
  refine ⟨g,fun n => ⟨hgc n,hgs n,hgm n⟩,D,?_,?_,?_⟩
  · exact ((hf.integrable_norm_pow (by norm_num : (3:ℕ) ≠ 0)).add
      (integrable_toReal_of_lintegral_ne_top hS hSint.ne)).const_mul 4
  · intro z; exact mul_nonneg (by norm_num) (add_nonneg (by positivity) ENNReal.toReal_nonneg)
  · filter_upwards [hSfinite] with z hz
    refine ⟨fun n => ?_,?_⟩
    · have he : ‖g n z-f z‖^3 ≤ (S z).toReal := by
        have hh := ENNReal.toReal_mono hz.ne
          (ENNReal.le_tsum (f := fun index => ‖f z-g index z‖ₑ^3) n : ‖f z-g n z‖ₑ^3 ≤ S z)
        simpa only [ENNReal.toReal_pow,enorm_eq_nnnorm,ENNReal.coe_toReal,coe_nnnorm,norm_sub_rev] using hh
      exact (norm_cube_le_four_sub (g n z) (f z)).trans (by dsimp [D]; linarith)
    · apply tendsto_of_enorm_cube
      simpa only [enorm_sub_rev] using ENNReal.tendsto_atTop_zero_of_tsum_ne_top hz.ne
end
end TriangularHilbert
end

end OAI
