import OAI.Probability.ClassicalON.SignedSigns

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem rawBond_tilt_defect_nonneg (μ : Measure Amplitude) [IsProbabilityMeasure μ]
    (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    {f g : (V → Amplitude) → (E → Bool) → ℝ}
    (hf : ∀ η,Continuous (fun r => f r η)) (hg : ∀ η,Continuous (fun r => g r η))
    (hfn : ∀ r η,0≤f r η) (hgn : ∀ r η,0≤g r η)
    (hfr : ∀ η,Monotone (fun r => f r η)) (hgr : ∀ η,Monotone (fun r => g r η))
    (hfη : ∀ r,Monotone (f r)) (hgη : ∀ r,Monotone (g r)) :
    0≤∫ r,∑ η,amplitudeBondWeight left right b r η*g r η*
      (f r η-jointBondMean μ left right b f) ∂Measure.pi (fun _ : V => μ) := by
  let c := jointBondMean μ left right b f
  have h := jointBond_associated μ left right b hb hf hg hfn hgn hfr hgr hfη hgη
  change c*jointBondMean μ left right b g≤jointBondMean μ left right b (fun r η => f r η*g r η) at h
  rw [jointBondMean_raw _ _ _ _ hb,jointBondMean_raw _ _ _ _ hb] at h
  have hD : 0<∫ r,∑ η,amplitudeBondWeight left right b r η ∂Measure.pi (fun _ : V => μ) := by
    simp_rw [amplitudeBondWeight_sum]
    exact compact_integral_pos (continuous_amplitudeDensity _ _ _) (amplitudeDensity_pos _ _ _)
  rw [← mul_div_assoc,div_le_div_iff_of_pos_right hD] at h
  have hi1 : Integrable (fun r => ∑ η,amplitudeBondWeight left right b r η*(f r η*g r η))
      (Measure.pi (fun _ : V => μ)) := by
    apply compact_integrable
    exact continuous_finsetSum _ (fun η _ => (continuous_amplitudeBondWeight _ _ _ η).mul ((hf η).mul (hg η)))
  have hi2 : Integrable (fun r => c*∑ η,amplitudeBondWeight left right b r η*g r η)
      (Measure.pi (fun _ : V => μ)) := by
    apply compact_integrable
    exact continuous_const.mul (continuous_finsetSum _ (fun η _ => (continuous_amplitudeBondWeight _ _ _ η).mul (hg η)))
  have he (r : V → Amplitude) :
      (∑ η,amplitudeBondWeight left right b r η*g r η*(f r η-c))=
        (∑ η,amplitudeBondWeight left right b r η*(f r η*g r η))-
          c*∑ η,amplitudeBondWeight left right b r η*g r η := by
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro η _
    ring
  change 0≤∫ r,∑ η,amplitudeBondWeight left right b r η*g r η*(f r η-c) ∂Measure.pi (fun _ : V => μ)
  simp_rw [he]
  rw [integral_sub hi1 hi2,integral_const_mul]
  exact sub_nonneg.mpr h

end ClassicalON

end

end OAI
