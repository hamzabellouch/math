import OAI.MeasureTheory.Falconer.Estimates.UniformSamples
import OAI.MeasureTheory.Falconer.Incidence.IncidenceSampling
import OAI.MeasureTheory.Falconer.Estimates.PointSamples

namespace OAI

/-!
# Uniform sampling with incidence and good point labels

Both sampling stages use original probability laws. In the point stage,
the good labels are selected after sampling, so no measurable selection or
identification of coincident spatial coordinates is required.
-/

namespace Falconer
open Set MeasureTheory Real
attribute [local instance] Classical.propDecidable

theorem exists_uniform_incidence_sample {X W : Type*}
    [MeasurableSpace X] [MeasurableSpace W]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure W)
    (p : W → Space 2) (hp : Measurable p) (hpbound : ∀ w i, |p w i| ≤ 1)
    (F : X → W → ℝ) (hF : Measurable (Function.uncurry F))
    (hF0 : ∀ x w, 0 ≤ F x w) (hF1 : ∀ x w, F x w ≤ 1)
    {n L H : ℕ} (hn : 0 < n) {δ s K B I : ℝ}
    (hδ : 0 < δ) (hs : 0 ≤ s) (hK : 0 ≤ K) (hB : 1 ≤ B)
    (hL : δ⁻¹+1 ≤ L) (hH : δ⁻¹ ≤ H)
    (hsize : 1 ≤ (n : ℝ) * δ^s)
    (hprob : ∀ c r, δ ≤ r →
      (ν : Measure W).real {w | dist (p w) c ≤ r} ≤ K * r^s)
    (hI : 0 < I) (hmean : I ≤ ∫ w, ∫ x, F x w ∂(μ : Measure X) ∂(ν : Measure W))
    (hsmall : (((2*L+1)^2 * H : ℕ) : ℝ) * exp (-B) ≤ I/4) :
    ∃ ω : Fin n → W,
      (∀ c r, δ ≤ r → iidCount {w | dist (p w) c ≤ r} ω ≤
        (((exp 1 - 1)*K+B) * 8^s) * (n : ℝ) * r^s) ∧
      I/4 ≤ (μ : Measure X).real {x | I/4 ≤ iidAverage (F x) ω} := by
  have hFx (w : W) : Measurable (fun x => F x w) :=
    hF.comp (measurable_id.prodMk measurable_const)
  have hFi (w : W) : Integrable (fun x => F x w) (μ : Measure X) := by
    apply Integrable.of_bound (hFx w).aestronglyMeasurable 1
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 x w)] using hF1 x w
  have hIntegral : Measurable (fun w => ∫ x, F x w ∂(μ : Measure X)) :=
    hF.stronglyMeasurable.integral_prod_left.measurable
  have hIntegral0 (w : W) : 0 ≤ ∫ x, F x w ∂(μ : Measure X) :=
    integral_nonneg (fun x => hF0 x w)
  have hIntegral1 (w : W) : (∫ x, F x w ∂(μ : Measure X)) ≤ 1 := by
    simpa using integral_mono (hFi w) (integrable_const (1 : ℝ)) (fun x => hF1 x w)
  have hIntegrable : Integrable (fun w => ∫ x, F x w ∂(μ : Measure X)) (ν : Measure W) := by
    apply Integrable.of_bound hIntegral.aestronglyMeasurable 1
    filter_upwards with w
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hIntegral0 w)] using hIntegral1 w
  obtain ⟨ω, hcounts, hmass⟩ := exists_uniform_ball_sample ν p hp hpbound hn
    hδ hs hK hB hL hH hsize hprob (fun w => ∫ x, F x w ∂(μ : Measure X))
    hIntegrable hIntegral1 hI hmean hsmall
  refine ⟨ω, hcounts, ?_⟩
  apply high_value_set_mass (μ : Measure X) (fun x => iidAverage (F x) ω)
  · unfold iidAverage
    exact measurable_const.mul (Finset.measurable_sum _ (fun i _ => hFx (ω i)))
  · unfold iidAverage
    exact (integrable_finsetSum _ (fun i _ => hFi (ω i))).const_mul _
  · intro x
    exact iidAverage_le_one (F x) (hF1 x) hn ω
  · exact hI
  · simpa only [integral_empirical_kernel (μ : Measure X) F hFi ω] using hmass

/-- Sample from the original point law, retain the labels in a positive
mass set, and extract a separated point set. Repeated coordinates cost only
the proved ball-count factor. -/
theorem exists_good_separated_point_sample {X : Type*} [MeasurableSpace X]
    (μ : ProbabilityMeasure X) (p : X → Space 2) (hp : Measurable p)
    (hpbound : ∀ x i, |p x i| ≤ 1)
    (G : Set X) (hG : MeasurableSet G) {J : ℝ} (hJ : 0 < J)
    (hGmass : J ≤ (μ : Measure X).real G)
    {n L H : ℕ} (hn : 0 < n) {δ s K B : ℝ}
    (hδ : 0 < δ) (hs : 0 ≤ s) (hK : 0 ≤ K) (hB : 1 ≤ B)
    (hL : δ⁻¹+1 ≤ L) (hH : δ⁻¹ ≤ H)
    (hsize : 1 ≤ (n : ℝ) * δ^s) (hsize' : (n : ℝ) * δ^s ≤ 2)
    (hprob : ∀ c r, δ ≤ r →
      (μ : Measure X).real {x | dist (p x) c ≤ r} ≤ K * r^s)
    (hsmall : (((2*L+1)^2 * H : ℕ) : ℝ) * exp (-B) ≤ J/4) :
    ∃ (ω : Fin n → X) (D : Finset (Fin n)) (P : Finset (Space 2)),
      D.Nonempty ∧ (∀ i ∈ D, ω i ∈ G) ∧ P.Nonempty ∧ P ⊆ D.image (p ∘ ω) ∧
      FiniteSeparatedAt δ P ∧
      NormalizedFiniteBallBound δ s
        (2 * (2 * (((exp 1-1)*K+B) * 8^s) / J)^2) P := by
  classical
  let f := G.indicator (fun _ => (1 : ℝ))
  have hf : Integrable f (μ : Measure X) := (integrable_const 1).indicator hG
  have hf1 (x : X) : f x ≤ 1 := by
    by_cases hx : x ∈ G <;> simp [f, hx]
  have hmean : J ≤ ∫ x, f x ∂(μ : Measure X) := by
    simpa only [f, integral_indicator_const (1 : ℝ) hG, smul_eq_mul, mul_one] using hGmass
  obtain ⟨ω, hcount, havg⟩ := exists_uniform_ball_sample μ p hp hpbound hn
    hδ hs hK hB hL hH hsize hprob f hf hf1 hJ hmean hsmall
  let D := Finset.univ.filter (fun i => ω i ∈ G)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hDlow : J / 2 * n ≤ (D.card : ℝ) := by
    have he : iidAverage f ω = (n : ℝ)⁻¹ * (D.card : ℝ) := by
      change (n : ℝ)⁻¹ * iidCount G ω = _
      rw [iidCount_eq_card_filter]
    rw [he] at havg
    have hh := mul_le_mul_of_nonneg_left havg hnR.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hnR.ne', one_mul, mul_comm] using hh
  have hDn : D.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (mul_pos (div_pos hJ (by norm_num)) hnR).trans_le hDlow
  let T : ℝ := ((exp 1-1)*K+B)*8^s
  have hT : 0 < T := by
    have he : 0 ≤ exp 1 - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by norm_num))
    have hh : 0 < (exp 1-1)*K+B := lt_of_lt_of_le zero_lt_one
      (hB.trans (le_add_of_nonneg_left (mul_nonneg he hK)))
    exact mul_pos hh (Real.rpow_pos_of_pos (by norm_num) _)
  have hcoef : T * n ≤ (2*T/J) * (D.card : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hJ).mpr
    have hh := mul_le_mul_of_nonneg_left hDlow (by positivity : 0 ≤ 2*T)
    nlinarith
  have hDC (c : Space 2) (r : ℝ) (hr : δ ≤ r) :
      ((D.filter (fun i => dist ((p ∘ ω) i) c ≤ r)).card : ℝ) ≤
        (2*T/J) * (D.card : ℝ) * r^s := by
    have hsub : D.filter (fun i => dist ((p ∘ ω) i) c ≤ r) ⊆
        Finset.univ.filter (fun i => dist (p (ω i)) c ≤ r) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    calc
      _ ≤ iidCount {x | dist (p x) c ≤ r} ω := by
        rw [iidCount_eq_card_filter]
        exact_mod_cast Finset.card_le_card hsub
      _ ≤ T * (n : ℝ) * r^s := hcount c r hr
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (hδ.le.trans hr) _)
  have hDs : (D.card : ℝ) * δ^s ≤ 2 := by
    have hcard : (D.card : ℝ) ≤ n := by
      have hh := Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => ω i ∈ G)
      have hh' : D.card ≤ n := by simpa only [Finset.card_univ, Fintype.card_fin] using hh
      exact_mod_cast hh'
    exact (mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hδ.le _)).trans hsize'
  obtain ⟨P, hPn, hPD, hsep, hballs⟩ := exists_separated_point_sample D (p ∘ ω)
    hδ (div_pos (mul_pos (by norm_num) hT) hJ) hDn hDs hDC
  exact ⟨ω, D, P, hDn, fun i hi => (Finset.mem_filter.mp hi).2, hPn, hPD, hsep, hballs⟩

end Falconer

end OAI
