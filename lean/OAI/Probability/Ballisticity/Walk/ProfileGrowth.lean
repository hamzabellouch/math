import Mathlib
import OAI.Probability.Ballisticity.Estimates.TailSampling

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace TailGrowth

noncomputable def normalizedRestriction {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X) : Measure X := (μ s)⁻¹ • μ.restrict s

lemma normalizedRestriction_probability {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (s : Set X) (hpos : μ s ≠ 0) :
    IsProbabilityMeasure (normalizedRestriction μ s) := by
  constructor
  simp only [normalizedRestriction, Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply MeasurableSet.univ,Set.univ_inter]
  exact ENNReal.inv_mul_cancel hpos (measure_ne_top _ _)

lemma normalizedRestriction_supported {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X) (hs : MeasurableSet s) :
    ∀ᵐ x ∂normalizedRestriction μ s, x ∈ s :=
  Measure.ae_smul_measure (ae_restrict_mem hs) _

lemma comp_total_le_one {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (κ : Kernel X Y) (hκ : ∀ x, κ x Set.univ ≤ 1)
    (μ : Measure X) [IsProbabilityMeasure μ] : (κ ∘ₘ μ) Set.univ ≤ 1 := by
  rw [Measure.bind_apply MeasurableSet.univ κ.measurable.aemeasurable]
  calc
    (∫⁻ x, κ x Set.univ ∂μ) ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂μ := lintegral_mono hκ
    _ = 1 := by simp

lemma real_le_one_of_total_le_one {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (hμ : μ Set.univ ≤ 1) (s : Set X) : μ.real s ≤ 1 := by
  exact (ENNReal.toReal_mono (by simp) ((measure_mono (Set.subset_univ s)).trans hμ)).trans_eq (by simp)

noncomputable def outwardMass {X : Type*} [MeasurableSpace X]
    (κ : Kernel X ℤ) (ξ : X → ℤ) (p : X × X) : ℝ :=
  ((κ p.1).prod (κ p.2)).real {y | ξ p.2 - ξ p.1 ≤ y.2-y.1}

lemma ordered_stream_mass_lower {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (κ : Kernel X ℤ) [IsFiniteKernel κ] (hκ : ∀ x, κ x Set.univ ≤ 1)
    (ξ : X → ℤ) (α β : Measure X) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (R : ℤ) (hgap : ∀ᵐ p ∂α.prod β, R ≤ ξ p.2 - ξ p.1) :
    (∫ p, outwardMass κ ξ p ∂α.prod β) ≤
      ((κ ∘ₘ α).prod (κ ∘ₘ β)).real {y | y.1+R ≤ y.2} := by
  have hset : MeasurableSet {y : ℤ × ℤ | y.1+R ≤ y.2} := (Set.to_countable _).measurableSet
  have hfin : ∀ p : X × X, (κ p.1).prod (κ p.2) Set.univ ≤ 1 := by
    intro p
    rw [←Set.univ_prod_univ,Measure.prod_prod]
    exact (mul_le_of_le_one_left (by positivity) (hκ _)).trans (hκ _)
  have hm : Measurable (fun p : X × X =>
      (κ p.1).prod (κ p.2) {y | ξ p.2 - ξ p.1 ≤ y.2-y.1}) := measurable_of_countable _
  rw [Measure.real,prod_comp,
    Measure.bind_apply hset (κ ∥ₖ κ).measurable.aemeasurable]
  unfold outwardMass Measure.real
  rw [integral_toReal hm.aemeasurable (Eventually.of_forall fun p =>
    ((measure_mono (Set.subset_univ _)).trans (hfin p)).trans_lt (by simp))]
  apply ENNReal.toReal_mono
  · have hb : (∫⁻ p, (κ ∥ₖ κ) p {y | y.1+R ≤ y.2} ∂α.prod β) ≤ 1 := by
      calc
        _ ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂α.prod β := by
          apply lintegral_mono
          intro p
          dsimp only
          rw [Kernel.parallelComp_apply]
          exact (measure_mono (Set.subset_univ _)).trans (hfin p)
        _ = 1 := by simp
    exact ne_of_lt (hb.trans_lt (by simp))
  · apply lintegral_mono_ae
    filter_upwards [hgap] with p hp
    rw [Kernel.parallelComp_apply]
    apply measure_mono
    intro y hy
    simp only [Set.mem_ofPred_eq] at hy ⊢
    omega

theorem profile_tail_growth {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X]
    (w : Measure X) [IsFiniteMeasure w] (w' : Measure ℤ) [IsFiniteMeasure w']
    (ξ : X → ℤ) (hsurj : Function.Surjective ξ) (hfull : ∀ x, 0 < w.real {x})
    (κ : Kernel X ℤ) [IsFiniteKernel κ] (hκ : ∀ x, κ x Set.univ ≤ 1)
    (R j : ℤ) (hj : ∀ k, TailCuts.score (TailCuts.lower (w.map ξ))
      (TailCuts.upper (w.map ξ)) R k ≤
      TailCuts.score (TailCuts.lower (w.map ξ)) (TailCuts.upper (w.map ξ)) R j)
    (C a : ℝ) (hupdate : ENNReal.ofReal (Real.exp C) • (κ ∘ₘ w) ≤ w')
    (Z : X × X → ℝ)
    (hZi : Integrable Z ((normalizedRestriction w (ξ ⁻¹' Set.Iic j)).prod
      (normalizedRestriction w (ξ ⁻¹' Set.Ici (j+R)))))
    (hZ0 : ∀ p, 0 ≤ Z p)
    (hp0 : ∀ᵐ p ∂((normalizedRestriction w (ξ ⁻¹' Set.Iic j)).prod
      (normalizedRestriction w (ξ ⁻¹' Set.Ici (j+R)))), 0 < outwardMass κ ξ p)
    (hp : ∀ᵐ p ∂((normalizedRestriction w (ξ ⁻¹' Set.Iic j)).prod
      (normalizedRestriction w (ξ ⁻¹' Set.Ici (j+R)))),
      -a-Z p ≤ Real.log (outwardMass κ ξ p)) :
    C-a-(∫ p, Z p ∂((normalizedRestriction w (ξ ⁻¹' Set.Iic j)).prod
      (normalizedRestriction w (ξ ⁻¹' Set.Ici (j+R)))))-Real.log 2 ≤
      Real.log (statistic w' R) - Real.log (statistic (w.map ξ) R) := by
  have hξ : Measurable ξ := measurable_of_countable _
  have hwfull := TailSampling.coordinate_atom_pos w ξ hξ hsurj hfull
  have hLp := TailCuts.lower_pos (w.map ξ) hwfull j
  have hUp := TailCuts.upper_pos (w.map ξ) hwfull (j+R)
  rw [TailCuts.lower,Measure.real,Measure.map_apply hξ measurableSet_Iic] at hLp
  rw [TailCuts.upper,Measure.real,Measure.map_apply hξ measurableSet_Ici] at hUp
  have hL : w (ξ ⁻¹' Set.Iic j) ≠ 0 := (ENNReal.toReal_pos_iff.mp hLp).1.ne'
  have hU : w (ξ ⁻¹' Set.Ici (j+R)) ≠ 0 := (ENNReal.toReal_pos_iff.mp hUp).1.ne'
  let α := normalizedRestriction w (ξ ⁻¹' Set.Iic j)
  let β := normalizedRestriction w (ξ ⁻¹' Set.Ici (j+R))
  let : IsProbabilityMeasure α := normalizedRestriction_probability w _ hL
  let : IsProbabilityMeasure β := normalizedRestriction_probability w _ hU
  have hT := statistic_pos (w.map ξ) hwfull R
  have hTls : statistic (w.map ξ) R ≤ w.real (ξ ⁻¹' Set.Iic j) := by
    rw [statistic_eq_max _ R j hj]
    exact (min_le_left _ _).trans_eq (by
      simp only [TailCuts.lower,Measure.real,Measure.map_apply hξ measurableSet_Iic])
  have hTus : statistic (w.map ξ) R ≤ w.real (ξ ⁻¹' Set.Ici (j+R)) := by
    rw [statistic_eq_max _ R j hj]
    exact (min_le_right _ _).trans_eq (by
      simp only [TailCuts.upper,Measure.real,Measure.map_apply hξ measurableSet_Ici])
  have hdl := continued_tail_dominated κ w w' _ hL hTls hupdate
  have hdu := continued_tail_dominated κ w w' _ hU hTus hupdate
  have hgap : ∀ᵐ p ∂α.prod β, R ≤ ξ p.2 - ξ p.1 := by
    apply (Measure.ae_prod_iff_ae_ae ((Set.to_countable _).measurableSet)).mpr
    filter_upwards [normalizedRestriction_supported w _ (hξ measurableSet_Iic)] with x hx
    filter_upwards [normalizedRestriction_supported w _ (hξ measurableSet_Ici)] with y hy
    simp only [Set.mem_preimage,Set.mem_Iic,Set.mem_Ici] at hx hy
    omega
  have hPi : Integrable (outwardMass κ ξ) (α.prod β) := by
    apply (integrable_const (1 : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
    exact Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]
      unfold outwardMass
      rw [abs_of_nonneg measureReal_nonneg]
      apply real_le_one_of_total_le_one
      rw [←Set.univ_prod_univ,Measure.prod_prod]
      exact (mul_le_of_le_one_left (by positivity) (hκ _)).trans (hκ _)
  obtain ⟨hQ,hlog⟩ := log_integral_lower (α.prod β) Z (outwardMass κ ξ) a
    hZi (Eventually.of_forall hZ0) hPi hp0 hp
  exact log_statistic_grows (κ ∘ₘ α) (κ ∘ₘ β) (w.map ξ) w'
    (real_le_one_of_total_le_one _ (comp_total_le_one κ hκ α) _)
    (real_le_one_of_total_le_one _ (comp_total_le_one κ hκ β) _)
    R hT hQ (ordered_stream_mass_lower κ hκ ξ α β R hgap) hlog
    (fun j => stream_real_lower _ w' (mul_pos (Real.exp_pos C) hT).le hdl (Set.Iic j))
    (fun j => stream_real_lower _ w' (mul_pos (Real.exp_pos C) hT).le hdu (Set.Ici j))

end TailGrowth

end

end OAI
