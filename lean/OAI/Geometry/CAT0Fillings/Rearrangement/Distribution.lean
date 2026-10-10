import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.Basic

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Rearrangement

noncomputable def negativeTail (μ : Measure ℝ) [IsFiniteMeasure μ] : StieltjesFunction ℝ where
  toFun t := -μ.real (Ioi t)
  mono' := fun a b hab => neg_le_neg (measureReal_mono (Ioi_subset_Ioi hab))
  right_continuous' t := by
    have h := (integrable_const (μ := μ) (1:ℝ)).integrableOn.continuousWithinAt_Ici_primitive_Ioi
      (a₀ := t)
    have h' : ContinuousWithinAt (fun b => μ.real (Ioi b)) (Ici t) t := by
      simpa only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one] using h
    exact h'.neg

lemma negativeTail_measure (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (negativeTail μ).measure = μ := by
  apply Measure.ext_of_Ioc
  intro a b hab
  rw [StieltjesFunction.measure_Ioc]
  change ENNReal.ofReal (-μ.real (Ioi b) - -μ.real (Ioi a)) = μ (Ioc a b)
  have hsplit : μ.real (Ioi a) = μ.real (Ioc a b) + μ.real (Ioi b) := by
    rw [←measureReal_union (by simp [Set.disjoint_left]) measurableSet_Ioi]
    congr 1
    ext x
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · intro h
      by_cases hx : x ≤ b
      · exact Or.inl ⟨h,hx⟩
      · exact Or.inr (not_le.mp hx)
    · rintro (h|h)
      · exact h.1
      · exact hab.trans h
  rw [hsplit]
  convert ENNReal.ofReal_toReal (measure_ne_top μ (Ioc a b)) using 1
  dsimp only [measureReal_def]
  congr 1
  ring

lemma ae_hasDerivAt_tail (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ᵐ t : ℝ, HasDerivAt (fun s => μ.real (Ioi s))
      (-(μ.rnDeriv volume t).toReal) t := by
  have h := (negativeTail μ).ae_hasDerivAt
  rw [negativeTail_measure] at h
  filter_upwards [h] with t ht
  have hn := ht.neg
  change HasDerivAt (fun s => - -μ.real (Ioi s)) _ t at hn
  simpa only [neg_neg] using hn

lemma stieltjes_secant_lower (f : StieltjesFunction ℝ) {a b c : ℝ}
    (hab : a ≤ b)
    (hc : ∀ᵐ x ∂volume.restrict (Ioc a b), c ≤ deriv f x) :
    c * (b-a) ≤ f b-f a := by
  have hfin : f.measure (Ioc a b) ≠ ∞ := by
    rw [StieltjesFunction.measure_Ioc]
    exact ENNReal.ofReal_ne_top
  have hle : ∀ᵐ x ∂volume.restrict (Ioc a b),
      c ≤ (f.measure.rnDeriv volume x).toReal := by
    filter_upwards [hc, ae_restrict_of_ae f.ae_hasDerivAt] with x hx hd
    simpa only [hd.deriv] using hx
  calc
    c * (b-a) = ∫ x in Ioc a b, c := by
      simp [integral_const, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
        measureReal_def, mul_comm]
    _ ≤ ∫ x in Ioc a b, (f.measure.rnDeriv volume x).toReal :=
      integral_mono_ae (integrable_const c)
        (Measure.integrableOn_toReal_rnDeriv hfin) hle
    _ ≤ f.measure.real (Ioc a b) := Measure.setIntegral_toReal_rnDeriv_le hfin
    _ = f b - f a := by
      rw [measureReal_def, StieltjesFunction.measure_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (f.mono hab))]

end CAT0Fillings.Rearrangement
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Rearrangement

noncomputable def radiusDistribution (μ : Measure ℝ) (ω : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (μ.real (Ioi t)/ω) ^ (1/(n:ℝ))

variable (μ : Measure ℝ) {ω : ℝ} {n : ℕ}

lemma radius_nonneg [IsFiniteMeasure μ] (hω : 0 ≤ ω) (t : ℝ) :
    0 ≤ radiusDistribution μ ω n t :=
  Real.rpow_nonneg (div_nonneg measureReal_nonneg hω) _

lemma radius_pos [IsFiniteMeasure μ] (hω : 0 < ω) {t : ℝ} (ht : 0 < μ.real (Ioi t)) :
    0 < radiusDistribution μ ω n t := Real.rpow_pos_of_pos (div_pos ht hω) _

lemma radius_pow [IsFiniteMeasure μ] (hω : 0 < ω) (hn : 0 < n) (t : ℝ) :
    ω*(radiusDistribution μ ω n t)^n = μ.real (Ioi t) := by
  rw [radiusDistribution,one_div,Real.rpow_inv_natCast_pow
    (div_nonneg measureReal_nonneg hω.le) hn.ne']
  exact mul_div_cancel₀ _ hω.ne'

variable [IsFiniteMeasure μ]

lemma radius_antitone (hω : 0 ≤ ω) : Antitone (radiusDistribution μ ω n) := by
  intro a b hab
  apply Real.rpow_le_rpow (div_nonneg measureReal_nonneg hω)
  · exact div_le_div_of_nonneg_right (measureReal_mono (Ioi_subset_Ioi hab)) hω
  · positivity

lemma radius_right_continuous (hω : 0 < ω) (hn : 0 < n) (t : ℝ) :
    ContinuousWithinAt (radiusDistribution μ ω n) (Ici t) t := by
  have htail : ContinuousWithinAt (fun s => μ.real (Ioi s)) (Ici t) t := by
    have hh := (negativeTail μ).right_continuous' t
    have hh' := hh.neg
    change ContinuousWithinAt (fun s => - -μ.real (Ioi s)) (Ici t) t at hh'
    simpa only [neg_neg] using hh'
  exact (htail.div continuousWithinAt_const hω.ne').rpow_const (Or.inr (by positivity))

noncomputable def negativeRadius (hω : 0 < ω) (hn : 0 < n) : StieltjesFunction ℝ where
  toFun t := -radiusDistribution μ ω n t
  mono' := (radius_antitone μ hω.le).neg
  right_continuous' t := (radius_right_continuous μ hω hn t).neg

lemma ae_radius_derivative (hω : 0 < ω) (hn : 0 < n) :
    ∀ᵐ t : ℝ, HasDerivAt (radiusDistribution μ ω n)
      (deriv (radiusDistribution μ ω n) t) t ∧
      (n:ℝ)*ω*(radiusDistribution μ ω n t)^(n-1)*
        deriv (radiusDistribution μ ω n) t = -(μ.rnDeriv volume t).toReal := by
  filter_upwards [(radius_antitone μ (n := n) hω.le).neg.ae_differentiableAt,
    ae_hasDerivAt_tail μ] with t ht htail
  have ht : DifferentiableAt ℝ (radiusDistribution μ ω n) t := by simpa using ht.neg
  refine ⟨ht.hasDerivAt,?_⟩
  have hpow := (ht.hasDerivAt.pow n).const_mul ω
  have he : (fun s => μ.real (Ioi s)) =ᶠ[𝓝 t]
      (fun s => ω*(radiusDistribution μ ω n s)^n) :=
    Eventually.of_forall (fun s => (radius_pow μ hω hn s).symm)
  have hc := (hpow.congr_of_eventuallyEq he).unique htail
  nlinarith only [hc]

lemma radius_secant_from_coarea (hω : 0 < ω) (hn : 0 < n) {U K η : ℝ}
    (hK : 0 < K) {P : ℝ → ℝ}
    (hpos : ∀ t ∈ Ioo 0 U, 0 < μ.real (Ioi t))
    (hP : ∀ᵐ t ∂volume.restrict (Ioo 0 U),
      (1-η)*((n:ℝ)*ω*(radiusDistribution μ ω n t)^(n-1)) ≤ P t ∧
      P t ≤ K*(μ.rnDeriv volume t).toReal) :
    ∀ s t : ℝ, 0 < s → s < t → t < U →
      ((1-η)/K)*(t-s) ≤ radiusDistribution μ ω n s-radiusDistribution μ ω n t := by
  have hd : ∀ᵐ t ∂volume.restrict (Ioo 0 U),
      (1-η)/K ≤ deriv (negativeRadius μ hω hn) t := by
    filter_upwards [hP,ae_restrict_of_ae (ae_radius_derivative μ hω hn),
      (ae_restrict_mem measurableSet_Ioo : ∀ᵐ t ∂volume.restrict (Ioo 0 U), t ∈ Ioo 0 U)]
      with t hp hdt ht
    have hA : 0 < (n:ℝ)*ω*(radiusDistribution μ ω n t)^(n-1) := by
      exact mul_pos (mul_pos (by exact_mod_cast hn) hω)
        (pow_pos (radius_pos μ hω (hpos t ht)) _)
    have he : deriv (negativeRadius μ hω hn) t =
        -deriv (radiusDistribution μ ω n) t := by
      exact hdt.1.neg.deriv
    rw [he,div_le_iff₀ hK]
    have hle := hp.1.trans hp.2
    have hh := hdt.2
    nlinarith
  intro s t hs hst htU
  have hsub : Ioc s t ⊆ Ioo (0:ℝ) U := fun x hx => ⟨hs.trans hx.1,hx.2.trans_lt htU⟩
  have hdd : ∀ᵐ x ∂volume.restrict (Ioc s t),
      (1-η)/K ≤ deriv (negativeRadius μ hω hn) x :=
    ae_mono (Measure.restrict_mono hsub le_rfl) hd
  have hslope := stieltjes_secant_lower (negativeRadius μ hω hn) hst.le hdd
  change ((1-η)/K)*(t-s) ≤ -radiusDistribution μ ω n t - -radiusDistribution μ ω n s at hslope
  linarith only [hslope]

end CAT0Fillings.Rearrangement
end

end OAI
