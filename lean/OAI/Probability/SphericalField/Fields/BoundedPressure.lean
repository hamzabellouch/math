import Mathlib
import OAI.Probability.SphericalField.Fields.FiniteModels
import OAI.Probability.SphericalField.Fields.Rounding

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

def fieldL1 (f g : Time → ℝ) : ℝ := ∫ u, |f u-g u| ∂timeLaw

lemma fieldL1_nonneg (f g : Time → ℝ) : 0 ≤ fieldL1 f g := integral_nonneg fun _ => abs_nonneg _

lemma fieldL1_symm (f g : Time → ℝ) : fieldL1 f g=fieldL1 g f := by
  unfold fieldL1; simp only [abs_sub_comm]

lemma fieldL1_triangle {f g h : Time → ℝ} (hf : Integrable f timeLaw)
    (hg : Integrable g timeLaw) (hh : Integrable h timeLaw) :
    fieldL1 f h ≤ fieldL1 f g+fieldL1 g h := by
  unfold fieldL1
  erw [← integral_add (hf.sub hg).abs (hg.sub hh).abs]
  exact integral_mono (hf.sub hh).abs ((hf.sub hg).abs.add (hg.sub hh).abs) (fun u => abs_sub_le _ _ _)

lemma BoundedField.round_pair_dist {H : ℝ} (f g : BoundedField H) (N M : ℕ) :
    fieldL1 (f.round N) (g.round M) ≤ fieldL1 f g+1/(N+1:ℕ)+1/(M+1:ℕ) := by
  have h₁ := fieldL1_triangle (f.round N).integrable f.integrable (g.round M).integrable
  have h₂ := fieldL1_triangle f.integrable g.integrable (g.round M).integrable
  have h₃ := f.round_abs_integral N
  have h₄ := g.round_abs_integral M
  change fieldL1 (f.round N) f ≤ _ at h₃
  change fieldL1 (g.round M) g ≤ _ at h₄
  rw [fieldL1_symm (g.round M) g] at h₄
  linarith

lemma BoundedField.round_pressure_cauchy {H : ℝ} (f : BoundedField H) (n : ℕ) :
    CauchySeq (fun N => (f.roundModel N).pressure n) := by
  let C := sphericalContinuityConstant n H
  have hC : 0 ≤ C := sphericalContinuityConstant_nonneg n H
  apply cauchySeq_of_le_tendsto_0' (fun N => C*(2/(N+1:ℕ)))
  · intro N M hNM
    have h := (f.roundModel N).pressure_bound (f.roundModel M) f.bound_nonneg
      (ae_of_all _ fun u => ⟨(f.round N).nonneg u,(f.round N).le_bound u⟩)
      (ae_of_all _ fun u => ⟨(f.round M).nonneg u,(f.round M).le_bound u⟩) n
    have he := f.round_pair_dist f N M
    have hsm : (1:ℝ)/(M+1:ℕ) ≤ 1/(N+1:ℕ) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hNM 1
    have hzero : fieldL1 f f=0 := by simp [fieldL1]
    rw [hzero] at he
    rw [Real.dist_eq]
    exact h.trans (mul_le_mul_of_nonneg_left (by change fieldL1 (f.round N) (f.round M) ≤ _; rw [show (2:ℝ)/(N+1:ℕ) = 1/(N+1:ℕ)+1/(N+1:ℕ) by ring]; linarith) hC)
  · have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2*C)
    convert h using 1
    · ext N; push_cast; ring
    · simp

lemma boundedSphericalFieldValue_tendsto {H : ℝ} (f : BoundedField H) (n : ℕ) :
    Tendsto (fun N => (f.roundModel N).pressure n) atTop (𝓝 (boundedSphericalFieldValue f n)) :=
  (f.round_pressure_cauchy n).tendsto_limUnder

theorem boundedSphericalFieldValue_eq_finite {H : ℝ} (f : BoundedField H)
    (M : FiniteFieldModel f) (n : ℕ) : boundedSphericalFieldValue f n=M.pressure n := by
  have ht : Tendsto (fun N => (f.roundModel N).pressure n) atTop (𝓝 (M.pressure n)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    refine squeeze_zero (g := fun N => sphericalContinuityConstant n H*(1/(N+1:ℕ))) (fun N => dist_nonneg) (fun N => ?_) ?_
    · rw [Real.dist_eq]
      exact ((f.roundModel N).pressure_bound M f.bound_nonneg
        (ae_of_all _ fun u => ⟨(f.round N).nonneg u,(f.round N).le_bound u⟩)
        (ae_of_all _ fun u => ⟨f.nonneg u,f.le_bound u⟩) n).trans
        (mul_le_mul_of_nonneg_left (f.round_abs_integral N) (sphericalContinuityConstant_nonneg n H))
    · convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (sphericalContinuityConstant n H) using 1 <;>
        simp only [Nat.cast_add,Nat.cast_one,mul_zero]
  exact tendsto_nhds_unique (boundedSphericalFieldValue_tendsto f n) ht

theorem boundedSphericalFieldValue_L1_continuous {H : ℝ} (f g : BoundedField H) (n : ℕ) :
    |boundedSphericalFieldValue f n-boundedSphericalFieldValue g n| ≤
      sphericalContinuityConstant n H*fieldL1 f g := by
  have hC := sphericalContinuityConstant_nonneg n H
  have h₁ := ((boundedSphericalFieldValue_tendsto f n).sub (boundedSphericalFieldValue_tendsto g n)).abs
  have h₂ : Tendsto (fun N : ℕ => sphericalContinuityConstant n H*
      (fieldL1 f g+1/(N+1:ℕ)+1/(N+1:ℕ))) atTop (𝓝 (sphericalContinuityConstant n H*fieldL1 f g)) := by
    simpa only [Nat.cast_add,Nat.cast_one,add_zero] using
      (((tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).const_mul (sphericalContinuityConstant n H))
  apply le_of_tendsto_of_tendsto h₁ h₂
  exact Filter.Eventually.of_forall fun N =>
    ((f.roundModel N).pressure_bound (g.roundModel N) f.bound_nonneg
      (ae_of_all _ fun u => ⟨(f.round N).nonneg u,(f.round N).le_bound u⟩)
      (ae_of_all _ fun u => ⟨(g.round N).nonneg u,(g.round N).le_bound u⟩) n).trans
      (mul_le_mul_of_nonneg_left (f.round_pair_dist g N N) hC)

lemma boundedSphericalFieldValue_ae_eq {H : ℝ} (f g : BoundedField H)
    (he : (f : Time → ℝ)=ᵐ[timeLaw] g) (n : ℕ) :
    boundedSphericalFieldValue f n=boundedSphericalFieldValue g n := by
  have h := boundedSphericalFieldValue_L1_continuous f g n
  have hd : fieldL1 f g=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [he] with u hu
    simp [hu]
  rw [hd,mul_zero] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

end SphericalPerceptron
end
end

end OAI
