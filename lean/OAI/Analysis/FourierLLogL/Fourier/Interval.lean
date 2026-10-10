import OAI.Analysis.FourierLLogL.Fourier.Coordinates

open MeasureTheory Filter Set Function
open scoped ENNReal BigOperators Topology Real

namespace OAI

namespace FourierLLogL.Period
noncomputable section

section segment
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma seg_eq_interval (f : ℝ → E) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in Ico a b, f x) = ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab]
  apply setIntegral_congr_set
  exact Ico_ae_eq_Ioc

lemma seg_translate_scale (f : ℝ → E) (d : ℝ) {a b c : ℝ} (hab : a ≤ b) (hc : 0 < c) :
    (∫ x in Ico a b, f (d + c*x)) = c⁻¹ • ∫ x in Ico (d+c*a) (d+c*b), f x := by
  rw [seg_eq_interval _ hab, intervalIntegral.integral_comp_add_mul f hc.ne',
    seg_eq_interval _ (by gcongr)]

lemma seg_translate_scale_rev (f : ℝ → E) (d : ℝ) {a b c : ℝ} (hab : a ≤ b) (hc : 0 < c) :
    (∫ x in Ico a b, f (d - c*x)) = c⁻¹ • ∫ x in Ico (d-c*b) (d-c*a), f x := by
  simp only [sub_eq_add_neg, ← neg_mul]
  rw [seg_eq_interval _ hab, intervalIntegral.integral_comp_add_mul f (neg_ne_zero.mpr hc.ne'),
    seg_eq_interval _ (by nlinarith : d + (-c)*b ≤ d + (-c)*a),
    intervalIntegral.integral_symm, inv_neg]
  simp

lemma mean_translate_scale (f : ℝ → E) (d : ℝ) {c : ℝ} (hc : 0 < c) :
    (∫ x, f (d + c*x) ∂μ₁) = c⁻¹ • ∫ x in Ico d (d+c), f x := by
  simpa [μ₁, unitInt] using
    seg_translate_scale f d (by norm_num : (0:ℝ) ≤ 1) hc

lemma seg_period_unit (f : ℝ → E) (hf : Periodic f 1) (a : ℝ) :
    (∫ x in Ico a (a+1), f x) = ∫ x, f x ∂μ₁ := by
  rw [seg_eq_interval _ (by linarith), hf.intervalIntegral_add_eq a 0,
    μ₁, unitInt, seg_eq_interval _ (by linarith)]
  simp

lemma seg_period_int (f : ℝ → E) (hf : Periodic f 1)
    (hfi : ∀ a b, IntervalIntegrable f volume a b) (a : ℝ) (k : ℕ) :
    (∫ x in Ico a (a+k), f x) = k • ∫ x, f x ∂μ₁ := by
  rw [seg_eq_interval _ (by simp : a ≤ a+(k:ℝ)), ← seg_period_unit f hf a,
    seg_eq_interval _ (by linarith)]
  simpa using hf.intervalIntegral_add_zsmul_eq (k:ℤ) a hfi

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [NormedSpace ℝ E] in
lemma seg_integrable (f : ℝ → E) (h : Measurable f) (B : ℝ) (a b : ℝ)
    (hB : ∀ x ∈ Ico a b, ‖f x‖ ≤ B) :
    IntegrableOn f (Ico a b) := by
  exact Integrable.of_bound h.aestronglyMeasurable B
    ((ae_restrict_mem measurableSet_Ico).mono hB)

omit [NormedSpace ℝ E] in
lemma interval_integrable (f : ℝ → E) (h : Measurable f) (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B)
    (a b : ℝ) : IntervalIntegrable f volume a b :=
  ⟨Integrable.of_bound h.aestronglyMeasurable B (ae_of_all _ hB),
    Integrable.of_bound h.aestronglyMeasurable B (ae_of_all _ hB)⟩

end segment

lemma density_short (ρ : ℝ → ℝ) (hρ : Measurable ρ) (hp : Periodic ρ 1)
    (h0 : ∀ x, 0 ≤ ρ x) (B : ℝ) (hb : ∀ x, ρ x ≤ B)
    (hm : (∫ x, ρ x ∂μ₁) ≤ 1) (a s : ℝ) (hs : s ≤ 1) :
    (∫ x in Ico a (a+s), ρ x) ≤ 1 := by
  have hsub : Ico a (a+s) ⊆ Ico a (a+1) := Ico_subset_Ico_right (by gcongr)
  apply le_trans (b := ∫ x in Ico a (a+1), ρ x)
  · exact setIntegral_mono_set
      (seg_integrable _ hρ B _ _ (fun x _ => by simpa [Real.norm_eq_abs, abs_of_nonneg (h0 x)] using hb x))
      (ae_of_all _ h0) (ae_of_all _ (fun _ hx => hsub hx))
  · rwa [seg_period_unit _ hp]

/-- One good set works for *all* offsets and dilations of the grids. -/
theorem density_good_set (ρ : ℝ → ℝ) (hρ : Measurable ρ) (hp : Periodic ρ 1)
    (h0 : ∀ x, 0 ≤ ρ x) (B : ℝ) (hb : ∀ x, ρ x ≤ B)
    (hm : (∫ x, ρ x ∂μ₁) ≤ 1) (D : ℝ) (hD : 0 < D) :
    ∃ G : Set ℝ, MeasurableSet G ∧ G ⊆ unitInt ∧
      μ₁ Gᶜ ≤ ENNReal.ofReal (64 / D) ∧
      ∀ x ∈ G, ∀ (a s : ℝ), 0 < s → s ≤ 1 → x ∈ Ico a (a+s) →
        (∫ y in Ico a (a+s), ρ y) ≤ D*s := by
  let W (p : ℝ × ℝ) := Metric.ball p.1 p.2
  let T : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ p.2 ≤ 1 ∧ W p ⊆ Ico (-4) 4 ∧
    D*p.2 < ∫ y in W p, ρ y}
  let A := ⋃ p ∈ T, W p
  have hWo (p) : IsOpen (W p) := Metric.isOpen_ball
  have hAo : IsOpen A := isOpen_iUnion fun p => isOpen_iUnion fun _ => hWo p
  obtain ⟨V,hVT,hdis,hV⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball T Prod.fst Prod.snd
      1 (fun p h => h.2.1) 4 (by norm_num)
  have cnt : V.Countable := PairwiseDisjoint.countable_of_isOpen (s:=W) hdis
    (fun p _ => hWo p) fun p hp => ⟨p.1, Metric.mem_ball_self (hVT hp).1⟩
  have hv (p) : ‖ρ p‖ ≤ B := by simpa [Real.norm_eq_abs, abs_of_nonneg (h0 p)] using hb p
  have hi : IntegrableOn ρ (Ico (-4:ℝ) 4) :=
    seg_integrable _ hρ B _ _ (fun p _ => hv p)
  have hneg : (∫ x in Ico (-4:ℝ) 4, ρ x) ≤ 8 := by
    have HH := seg_period_int ρ hp (interval_integrable ρ hρ B hv) (-4) 8
    norm_num at HH
    rw [HH]
    linarith
  let ρ' (y : ℝ) := ENNReal.ofReal (ρ y)
  have hi' : (∫⁻ x in Ico (-4:ℝ) 4, ρ' x) ≤ ENNReal.ofReal 8 := by
    dsimp only [ρ']
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ h0)]
    exact ENNReal.ofReal_le_ofReal hneg
  have hcov : A ⊆ ⋃ p ∈ V, Metric.ball p.1 (4 * p.2) := by
    refine iUnion₂_subset fun p hp => ?_
    obtain ⟨q,hq,hpq⟩ := hV p hp
    exact fun x hx => mem_iUnion₂.mpr ⟨q,hq,hpq hx⟩
  have hsingle (p : ℝ × ℝ) (hp : p ∈ V) :
      volume (Metric.ball p.1 (4 * p.2)) ≤ ENNReal.ofReal (8 / D) * ∫⁻ x in W p, ρ' x := by
    have hp' := hVT hp
    rw [Real.volume_ball, ← ofReal_integral_eq_lintegral_ofReal (hi.mono_set hp'.2.2.1)
      (ae_of_all _ h0), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hh := hp'.2.2.2
    calc
      _ = 8 / D * (D * p.2) := by field_simp; ring
      _ ≤ _ := by gcongr
  have : Countable V := cnt.to_subtype
  have htot : volume A ≤ ENNReal.ofReal (64 / D) := by
    refine ((measure_mono hcov).trans (measure_biUnion_le volume cnt _)).trans
      ((ENNReal.tsum_le_tsum (fun i : V => hsingle i.val i.property)).trans ?_)
    rw [ENNReal.tsum_mul_left]
    have hlim : (∑' p : V, ∫⁻ x in W p, ρ' x) ≤ ENNReal.ofReal 8 := by
      rw [← lintegral_iUnion]
      · refine le_trans (lintegral_mono_set (iUnion_subset (fun (p : V) => ?_))) hi'
        exact (hVT p.property).2.2.1
      · exact fun p => (hWo p).measurableSet
      · exact fun i j h => hdis i.property j.property (fun e => h (Subtype.ext e))
    refine (mul_le_mul_right hlim _).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 8 / D)]
    ring_nf
  refine ⟨unitInt \ A, measurable_unitInt.diff hAo.measurableSet, sdiff_subset, ?_, ?_⟩
  · rw [μ₁, Measure.restrict_apply (measurable_unitInt.diff hAo.measurableSet).compl]
    exact (measure_mono (by grind : ((unitInt \ A)ᶜ ∩ unitInt) ⊆ A)).trans htot
  · intro x hx a s hs hs' hxs
    by_contra hn
    let p := (a+s/2,s)
    have hsub : Ico a (a+s) ⊆ W p := by
      intro y hy
      rcases hy with ⟨h1,h2⟩
      simp only [W, p, Real.ball_eq_Ioo, mem_Ioo]
      constructor <;> linarith
    have hsub' : W p ⊆ Ico (-4:ℝ) 4 := by
      intro y hy
      simp only [W,p,Real.ball_eq_Ioo, mem_Ioo] at hy
      rcases hx.1 with ⟨h1,h2⟩
      rcases hxs with ⟨h3,h4⟩
      constructor <;> linarith [hy.1, hy.2]
    have hp : p ∈ T := ⟨hs, hs', hsub', lt_of_lt_of_le (lt_of_not_ge hn)
      (setIntegral_mono_set (hi.mono_set hsub') (ae_of_all _ h0)
       (ae_of_all _ (fun _ h => hsub h)))⟩
    exact hx.2 (mem_iUnion₂.mpr ⟨p,hp,hsub hxs⟩)

end
end FourierLLogL.Period

end OAI
