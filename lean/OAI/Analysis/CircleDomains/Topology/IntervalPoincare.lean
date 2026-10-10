import OAI.Analysis.CircleDomains.Modulus.AverageOscillation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! A one-dimensional mean-oscillation bound, keeping the actual
integrable derivative in the right-hand side. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma interval_increment_le_integral {u G : ℝ → ℝ} {a b x y : ℝ}
    (hG : IntegrableOn G (Icc a b) volume) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hftc : (∫ t in x..y, G t) = u y-u x) :
    |u x-u y| ≤ ∫ t in Icc a b, |G t| := by
  calc
    |u x-u y| = |∫ t in x..y, G t| := by rw [hftc, abs_sub_comm]
    _ ≤ ∫ t in uIoc x y, |G t| := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm_uIoc (f := G) (a := x) (b := y))
    _ ≤ ∫ t in Icc a b, |G t| :=
      setIntegral_mono_set hG.abs (Eventually.of_forall fun _ => abs_nonneg _)
        (Eventually.of_forall fun _ ht => uIcc_subset_Icc hx hy (uIoc_subset_uIcc ht))

lemma volume_restrict_Icc_ne_zero {a b : ℝ} (hab : a < b) :
    (volume : Measure ℝ).restrict (Icc a b) ≠ 0 := by
  intro h
  have hh := congrArg (fun μ : Measure ℝ => μ univ) h
  have hv : volume (Icc a b) = 0 := by simpa using hh
  rw [Real.volume_Icc] at hv
  exact (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))) hv

lemma interval_abs_sub_average_le_integral {u G : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hu : ContinuousOn u (Icc a b))
    (hG : IntegrableOn G (Icc a b) volume)
    (hftc : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, (∫ t in x..y, G t) = u y-u x)
    {x : ℝ} (hx : x ∈ Icc a b) :
    |u x-(⨍ t in Icc a b, u t)| ≤ ∫ t in Icc a b, |G t| := by
  have hμ := volume_restrict_Icc_ne_zero hab
  let : NeZero ((volume : Measure ℝ).restrict (Icc a b)) := ⟨hμ⟩
  have hui : IntegrableOn u (Icc a b) volume := hu.integrableOn_compact isCompact_Icc
  apply abs_sub_average_le_of_ae hui (u x)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  exact interval_increment_le_integral hG hx hy (hftc x hx y hy)

end CircleDomainRigidity

end

end OAI
