import OAI.Probability.SLE.OptionalStopping

namespace OAI

/-! The bounded accumulated drift used as the product's discount state. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace SLEExactGauge.Multipoint

def discountClock {Ω : Type*} (g : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ u in (0 : ℝ)..(t.toNNReal : ℝ), g u.toNNReal ω

lemma discountClock_measurable {Ω : Type*} [MeasurableSpace Ω]
    (g : ℝ≥0 → Ω → ℝ) (hg : Measurable (Function.uncurry g)) :
    Measurable (fun p : ℝ × Ω => discountClock g p.1 p.2) := by
  have hgr : Measurable (fun p : ℝ × Ω => g p.1.toNNReal p.2) :=
    hg.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  exact (cumulative_integral_measurable _ hgr).comp
    ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)

lemma discountClock_initial {Ω : Type*} (g : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    discountClock g 0 ω = 0 := by simp [discountClock]

lemma discountClock_lipschitz {Ω : Type*}
    (g : ℝ≥0 → Ω → ℝ) (hg : ∀ ω, Continuous (fun t => g t ω))
    (C : ℝ≥0) (hC : ∀ t ω, |g t ω| ≤ C) (ω : Ω) :
    LipschitzWith C (fun t => discountClock g t ω) := by
  have hc : Continuous (fun u : ℝ => g u.toNNReal ω) := (hg ω).comp continuous_real_toNNReal
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [Real.dist_eq, ← Real.norm_eq_abs]
  unfold discountClock
  rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (t.toNNReal : ℝ)) (b := (s.toNNReal : ℝ)) (C := (C : ℝ))
    (f := fun u : ℝ => g u.toNNReal ω)
    (fun u _ => by simpa only [Real.norm_eq_abs] using hC u.toNNReal ω)
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
  have ht := Real.lipschitzWith_toNNReal.dist_le_mul s t
  simpa only [NNReal.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] using ht

lemma discountClock_derivative {Ω : Type*}
    (g : ℝ≥0 → Ω → ℝ) (hg : ∀ ω, Continuous (fun t => g t ω))
    (t : ℝ) (ht : 0 ≤ t) (ω : Ω) :
    HasDerivWithinAt (fun u => discountClock g u ω) (g t.toNNReal ω) (Ici 0) t := by
  have hc : Continuous (fun u : ℝ => g u.toNNReal ω) := (hg ω).comp continuous_real_toNNReal
  apply (hc.integral_hasStrictDerivAt 0 t).hasDerivAt.hasDerivWithinAt.congr_of_mem
  · intro u hu
    simp only [discountClock, Real.coe_toNNReal u hu]
  · exact ht

lemma discountClock_nonneg {Ω : Type*}
    (g : ℝ≥0 → Ω → ℝ) (hg : ∀ t ω, 0 ≤ g t ω) (t : ℝ) (ω : Ω) :
    0 ≤ discountClock g t ω := by
  apply intervalIntegral.integral_nonneg_of_forall t.toNNReal.coe_nonneg
  exact fun u => hg u.toNNReal ω

lemma discountClock_adapted {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (f : Filtration ℝ≥0 mΩ) (g : ℝ≥0 → Ω → ℝ)
    (hga : Adapted f g) (hgc : ∀ ω, Continuous (fun t => g t ω)) :
    Adapted f (fun t : ℝ≥0 => discountClock g t) := by
  have hsa : StronglyAdapted f g := fun t => (hga t).stronglyMeasurable
  have hp := hsa.isStronglyProgressive_of_continuous hgc
  intro t
  have hpt := (hp t).measurable
  let : MeasurableSpace Ω := f t
  have htime : Measurable (fun u : ℝ =>
      (⟨min u.toNNReal t, by change min u.toNNReal t ≤ t; exact min_le_right _ _⟩ : Iic t)) :=
    ((continuous_real_toNNReal.min continuous_const).measurable).subtype_mk
  have hgm : Measurable (fun p : ℝ × Ω => g (min p.1.toNNReal t) p.2) :=
    hpt.comp ((htime.comp measurable_fst).prodMk measurable_snd)
  have hm := (cumulative_integral_measurable (fun u ω => g (min u.toNNReal t) ω) hgm).comp
    (measurable_const.prodMk measurable_id : Measurable (fun ω : Ω => (t,ω)))
  convert hm using 1
  funext ω
  simp only [discountClock, Real.toNNReal_coe, Function.comp_def]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le t.coe_nonneg] at hu
  have hut : u.toNNReal ≤ t := by
    simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hu.2
  change g u.toNNReal ω = g (min u.toNNReal t) ω
  rw [min_eq_left hut]

end SLEExactGauge.Multipoint

end

end OAI
