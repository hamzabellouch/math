import OAI.Geometry.EinsteinFour.Moments
import OAI.Geometry.EinsteinFour.MomentObstruction

namespace OAI

/-! The scalar assembly of the balanced-Weyl-moments argument. The upper
volume estimate and the weighted variance estimate remain separate geometric
obligations; neither is declared to be a published input here. -/

namespace PositiveEinsteinFour

open MeasureTheory Filter MomentObstruction

noncomputable section

private theorem J_nonneg_of_variance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {z : Ω → ℝ}
    (hzi : Integrable z μ) (hz2i : Integrable (fun ω => z ω ^ 2) μ)
    (hHi : Integrable (fun ω => H (z ω) ^ 2) μ)
    (hvar : (∫ ω, H (z ω) ^ 2 ∂μ) - (∫ ω, H (z ω) ∂μ) ^ 2 ≤
      9 / 16 * ((∫ ω, z ω ^ 2 ∂μ) - ∫ ω, z ω ∂μ)) :
    0 ≤ 16 * (∫ ω, H (z ω) ∂μ) ^ 2 - ∫ ω, Phi (z ω) ∂μ := by
  have hid : (fun ω => Phi (z ω)) =
      (fun ω => 16 * H (z ω) ^ 2 + 9 * z ω - 9 * z ω ^ 2) := by
    funext ω
    unfold Phi
    ring
  have hi1 := integral_sub ((hHi.const_mul 16).add (hzi.const_mul 9)) (hz2i.const_mul 9)
  have hi2 := integral_add (hHi.const_mul 16) (hzi.const_mul 9)
  simp only [Pi.add_apply] at hi1
  rw [hid, hi1, hi2]
  simp only [integral_const_mul]
  linarith

/-- In the ordered case, the exact integer and moment constraints force equal
moments once the two-constrained-moments obstruction is applied. -/
theorem ordered_balanced_moments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {v b : Ω → ℝ}
    (n m : ℕ) (volume : ℝ)
    (hbm : AEStronglyMeasurable b μ)
    (hv : ∀ᵐ ω ∂μ, v ω ∈ Set.Icc (0 : ℝ) 2)
    (hb : ∀ᵐ ω ∂μ, b ω ∈ Set.Icc (0 : ℝ) 2)
    (hsum : ∀ᵐ ω ∂μ, v ω + b ω ≤ 2)
    (hbi : Integrable b μ)
    (hv2i : Integrable (fun ω => v ω ^ 2) μ)
    (hb2i : Integrable (fun ω => b ω ^ 2) μ)
    (hHbi : Integrable (fun ω => H (b ω) ^ 2) μ)
    (hvgap : 1 ≤ ∫ ω, v ω ^ 2 ∂μ) (hbgap : 1 ≤ ∫ ω, b ω ^ 2 ∂μ)
    (horder : (∫ ω, b ω ^ 2 ∂μ) ≤ ∫ ω, v ω ^ 2 ∂μ)
    (hmoments : (∫ ω, v ω ^ 2 ∂μ) + (∫ ω, b ω ^ 2 ∂μ) < 4)
    (hvolume : 0 < volume)
    (hupper : volume ≤ 2 * (1 - 3 / 40 *
      ((∫ ω, v ω ^ 2 ∂μ) + ∫ ω, b ω ^ 2 ∂μ)))
    (heuler : 2 + (n : ℝ) + (m : ℝ) = volume *
      (1 + (∫ ω, v ω ^ 2 ∂μ) + ∫ ω, b ω ^ 2 ∂μ))
    (hsignature : (n : ℝ) - (m : ℝ) = 2 / 3 * volume *
      ((∫ ω, v ω ^ 2 ∂μ) - ∫ ω, b ω ^ 2 ∂μ))
    (hvariance : (∫ ω, H (b ω) ^ 2 ∂μ) - (∫ ω, H (b ω) ∂μ) ^ 2 ≤
      9 / 16 * ((∫ ω, b ω ^ 2 ∂μ) - ∫ ω, b ω ∂μ)) :
    (∫ ω, v ω ^ 2 ∂μ) = (∫ ω, b ω ^ 2 ∂μ) := by
  rcases ordered_harmonic_counts n m _ _ volume hvgap hbgap horder hmoments
    hvolume hupper heuler hsignature with hcounts | ⟨hn, hm⟩
  · have hnreal : (n : ℝ) = (m : ℝ) := congrArg Nat.cast hcounts
    have hprod : volume * ((∫ ω, v ω ^ 2 ∂μ) - ∫ ω, b ω ^ 2 ∂μ) = 0 := by
      rw [hnreal] at hsignature
      linarith
    have := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hvolume)
    linarith
  · subst n
    subst m
    norm_num at heuler hsignature
    have hrelation := exceptional_moment_relation _ _ volume heuler hsignature
    have hi : Integrable (fun ω => 4 - 4 * b ω + b ω ^ 2) μ :=
      ((integrable_const 4).sub (hbi.const_mul 4)).add hb2i
    have hbound : (∫ ω, v ω ^ 2 ∂μ) ≤ 4 - 4 * (∫ ω, b ω ∂μ) + ∫ ω, b ω ^ 2 ∂μ := by
      have h := integral_mono_ae hv2i hi (by
        filter_upwards [hv, hb, hsum] with ω hvω hbω hsω
        have hp : 0 ≤ (2 - b ω - v ω) * (2 - b ω + v ω) := by
          apply mul_nonneg <;> linarith [hvω.1, hbω.2]
        nlinarith)
      have hi1 := integral_add ((integrable_const (4 : ℝ)).sub (hbi.const_mul 4)) hb2i
      have hi2 := integral_sub (integrable_const (4 : ℝ)) (hbi.const_mul 4)
      simp only [Pi.sub_apply] at hi1
      rw [hi1, hi2] at h
      simpa only [integral_const_mul, integral_const, probReal_univ, one_smul] using h
    have hconstraint := exceptional_moment_constraint _ _ _ hrelation hbound
    have hconstraint' : (∫ ω, 28 * b ω + 6 * b ω ^ 2 ∂μ) ≤ 25 := by
      rw [integral_add (hbi.const_mul 28) (hb2i.const_mul 6)]
      simpa only [integral_const_mul] using hconstraint
    have hnegative := two_constrained_moments hbm hb hbgap hconstraint'
    have hnonnegative := J_nonneg_of_variance hbi hb2i hHbi hvariance
    linarith

/-- Symmetric scalar form of the balanced-moment conclusion. The geometric
volume and weighted-variance estimates are explicit premises, pending their
independent formalization. -/
theorem balanced_moments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {v b : Ω → ℝ}
    (n m : ℕ) (volume : ℝ)
    (hvm : AEStronglyMeasurable v μ) (hbm : AEStronglyMeasurable b μ)
    (hv : ∀ᵐ ω ∂μ, v ω ∈ Set.Icc (0 : ℝ) 2)
    (hb : ∀ᵐ ω ∂μ, b ω ∈ Set.Icc (0 : ℝ) 2)
    (hsum : ∀ᵐ ω ∂μ, v ω + b ω ≤ 2)
    (hvi : Integrable v μ) (hbi : Integrable b μ)
    (hv2i : Integrable (fun ω => v ω ^ 2) μ)
    (hb2i : Integrable (fun ω => b ω ^ 2) μ)
    (hHvi : Integrable (fun ω => H (v ω) ^ 2) μ)
    (hHbi : Integrable (fun ω => H (b ω) ^ 2) μ)
    (hvgap : 1 ≤ ∫ ω, v ω ^ 2 ∂μ) (hbgap : 1 ≤ ∫ ω, b ω ^ 2 ∂μ)
    (hmoments : (∫ ω, v ω ^ 2 ∂μ) + (∫ ω, b ω ^ 2 ∂μ) < 4)
    (hvolume : 0 < volume)
    (hupper : volume ≤ 2 * (1 - 3 / 40 *
      ((∫ ω, v ω ^ 2 ∂μ) + ∫ ω, b ω ^ 2 ∂μ)))
    (heuler : 2 + (n : ℝ) + (m : ℝ) = volume *
      (1 + (∫ ω, v ω ^ 2 ∂μ) + ∫ ω, b ω ^ 2 ∂μ))
    (hsignature : (n : ℝ) - (m : ℝ) = 2 / 3 * volume *
      ((∫ ω, v ω ^ 2 ∂μ) - ∫ ω, b ω ^ 2 ∂μ))
    (hvvariance : (∫ ω, H (v ω) ^ 2 ∂μ) - (∫ ω, H (v ω) ∂μ) ^ 2 ≤
      9 / 16 * ((∫ ω, v ω ^ 2 ∂μ) - ∫ ω, v ω ∂μ))
    (hbvariance : (∫ ω, H (b ω) ^ 2 ∂μ) - (∫ ω, H (b ω) ∂μ) ^ 2 ≤
      9 / 16 * ((∫ ω, b ω ^ 2 ∂μ) - ∫ ω, b ω ∂μ)) :
    (∫ ω, v ω ^ 2 ∂μ) = (∫ ω, b ω ^ 2 ∂μ) ∧ n = m := by
  have hequal : (∫ ω, v ω ^ 2 ∂μ) = (∫ ω, b ω ^ 2 ∂μ) := by
    rcases le_total (∫ ω, b ω ^ 2 ∂μ) (∫ ω, v ω ^ 2 ∂μ) with horder | horder
    · exact ordered_balanced_moments n m volume hbm hv hb hsum hbi hv2i hb2i hHbi
        hvgap hbgap horder hmoments hvolume hupper heuler hsignature hbvariance
    · symm
      apply ordered_balanced_moments m n volume hvm hb hv
        (hsum.mono fun ω hω => by linarith) hvi hb2i hv2i hHvi hbgap hvgap horder
        (by linarith) hvolume (by convert hupper using 1; ring)
        (by nlinarith [heuler]) (by nlinarith [hsignature]) hvvariance
  refine ⟨hequal, ?_⟩
  rw [hequal] at hsignature
  have hreal : (n : ℝ) = (m : ℝ) := by linarith
  exact_mod_cast hreal

end

end PositiveEinsteinFour

end OAI
