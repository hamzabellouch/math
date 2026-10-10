import Mathlib
import OAI.Analysis.BiholderTransport.Duality.CompactDual
import OAI.Analysis.BiholderTransport.Regularity.ContinuousClosedRelationSelector

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

namespace WeakMTWTransport

section CompactAE
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

omit [Nonempty M] in

lemma contact_gap_control_at (u v : M →ᵇ ℝ) (x y : M)
    (hsingle : ∀ z, contactGap u v x z = 0 → z = y)
    (hgap : ∀ z, 0 ≤ contactGap u v x z) (f : M →ᵇ ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z, contactGap u v x z ≤ δ → f y - f z ≤ ε := by
  let G : M → ℝ := fun z => contactGap u v x z
  let B : Set M := {z | ε ≤ f y - f z}
  have hG : Continuous G := (continuous_const.add (continuous_cost_right x)).add v.continuous
  have hB : IsCompact B := (isClosed_le continuous_const
    (continuous_const.sub f.continuous)).isCompact
  by_cases hne : B.Nonempty
  · obtain ⟨z,hz,hmin⟩ := hB.exists_isMinOn hne hG.continuousOn
    have hpos : 0 < G z := by
      apply lt_of_le_of_ne (hgap z)
      intro he
      have heq := hsingle z he.symm
      change ε ≤ f y - f z at hz
      rw [heq,sub_self] at hz
      exact (not_le.mpr hε) hz
    refine ⟨G z / 2,half_pos hpos,?_⟩
    intro w hw
    by_contra hn
    have hm := hmin (le_of_lt (lt_of_not_ge hn))
    change G z ≤ contactGap u v x w at hm
    linarith
  · refine ⟨1,by norm_num,?_⟩
    intro z _
    by_contra hn
    exact hne ⟨z,le_of_lt (lt_of_not_ge hn)⟩

lemma transform_perturbation_upper_at (u v : M →ᵇ ℝ) (x y : M)
    (hsingle : ∀ z, contactGap u v x z = 0 → z = y)
    (hgap : ∀ z, 0 ≤ contactGap u v x z) (f : M →ᵇ ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ t : ℝ, 0 < t → t ≤ τ →
      cTransform (fun z => v z + t * f z) x ≤ u x - t * f y + t * ε := by
  obtain ⟨δ,hδ,hcontrol⟩ := contact_gap_control_at u v x y hsingle hgap f hε
  have hden : 0 < 2 * ‖f‖ + 1 := by positivity
  refine ⟨δ / (2 * ‖f‖ + 1),div_pos hδ hden,?_⟩
  intro t ht htτ
  have htd : t * (2 * ‖f‖ + 1) ≤ δ := (le_div_iff₀ hden).mp htτ
  have htbound : t * (2 * ‖f‖) ≤ δ := by nlinarith
  rw [cTransform_le_iff (v := fun z => v z + t * f z)
    (v.continuous.add (continuous_const.mul f.continuous))]
  intro z
  have hg := hgap z
  have hbound : t * (f y - f z) ≤ contactGap u v x z + t * ε := by
    by_cases hs : contactGap u v x z ≤ δ
    · have hh := mul_le_mul_of_nonneg_left (hcontrol z hs) ht.le
      nlinarith
    · have hf1 := BoundedContinuousFunction.norm_coe_le_norm f y
      have hf2 := BoundedContinuousFunction.norm_coe_le_norm f z
      rw [Real.norm_eq_abs,abs_le] at hf1 hf2
      have hw : f y - f z ≤ 2 * ‖f‖ := by linarith [hf1.2,hf2.1]
      have hh := mul_le_mul_of_nonneg_left hw ht.le
      have hte : 0 ≤ t * ε := mul_nonneg ht.le hε.le
      linarith
  dsimp [contactGap] at hbound
  nlinarith

def transformedDifferenceQuotient (v f : M →ᵇ ℝ) (t : ℝ) : M →ᵇ ℝ :=
  t⁻¹ • (boundedCTransform (v + t • f) - boundedCTransform v)

lemma transformedDifferenceQuotient_apply (v f : M →ᵇ ℝ) (t : ℝ) (x : M) :
    transformedDifferenceQuotient v f t x =
      (cTransform (fun z => v z + t * f z) x - cTransform v x) / t := by
  simp only [transformedDifferenceQuotient,BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.sub_apply,boundedCTransform_apply,smul_eq_mul]
  rw [div_eq_mul_inv,mul_comm]
  rfl

lemma transformedDifferenceQuotient_norm_le (v f : M →ᵇ ℝ) {t : ℝ} (ht : 0 < t) (x : M) :
    ‖transformedDifferenceQuotient v f t x‖ ≤ ‖f‖ := by
  have hh := boundedCTransform_nonexpansive (M := M) |>.dist_le_mul (v + t • f) v
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,add_sub_cancel_left,norm_smul,
    Real.norm_eq_abs,abs_of_pos ht] at hh
  have hp := BoundedContinuousFunction.norm_coe_le_norm
    (boundedCTransform (v + t • f) - boundedCTransform v) x
  have hbound := hp.trans hh
  rw [transformedDifferenceQuotient,BoundedContinuousFunction.smul_apply,norm_smul,
    Real.norm_eq_abs,abs_inv,abs_of_pos ht]
  exact (inv_mul_le_iff₀ ht).mpr hbound

lemma transformedDifferenceQuotient_tendsto_at (v f : M →ᵇ ℝ) (x y : M)
    (hcontact : contactGap (cTransform v) v x y = 0)
    (hsingle : ∀ z, contactGap (cTransform v) v x z = 0 → z = y)
    {s : ℕ → ℝ} (hs : ∀ j, 0 < s j) (hlim : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun j => transformedDifferenceQuotient v f (s j) x) atTop (𝓝 (-f y)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨τ,hτ,hup⟩ := transform_perturbation_upper_at (boundedCTransform v) v x y
    hsingle (cTransform_gap_nonneg v.continuous x) f (half_pos hε)
  have hevent : ∀ᶠ j in atTop, s j ≤ τ :=
    (hlim.eventually (eventually_lt_nhds hτ)).mono fun _ h => h.le
  filter_upwards [hevent] with j hj
  rw [transformedDifferenceQuotient_apply,Real.dist_eq,sub_neg_eq_add,abs_lt]
  have hu := hup (s j) (hs j) hj
  have hl := cTransform_gap_nonneg
    (v.continuous.add (continuous_const.mul f.continuous) :
      Continuous (fun z => v z + s j * f z)) x y
  change cTransform (fun z => v z + s j * f z) x ≤
    cTransform v x - s j * f y + s j * (ε/2) at hu
  dsimp only [contactGap] at hcontact
  change 0 ≤ cTransform (fun z => v z + s j * f z) x + cost x y + (v y + s j * f y) at hl
  have hlo : -f y ≤ (cTransform (fun z => v z + s j * f z) x - cTransform v x) / s j := by
    apply (le_div_iff₀ (hs j)).mpr
    nlinarith
  have hhi : (cTransform (fun z => v z + s j * f z) x - cTransform v x) / s j ≤ -f y + ε/2 := by
    apply (div_le_iff₀ (hs j)).mpr
    nlinarith
  constructor <;> linarith

variable [MeasurableSpace M] [BorelSpace M]

lemma dual_minimum_ae_integral_eq (μ ν : Measure M) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (v : M →ᵇ ℝ) (T : M → M)
    (hcontact : ∀ x, contactGap (cTransform v) v x (T x) = 0)
    (hsingle : ∀ᵐ x ∂μ, ∀ y, contactGap (cTransform v) v x y = 0 → y = T x)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective μ ν (boundedCTransform v,v) ≤ dualObjective μ ν (a,b))
    (f : M →ᵇ ℝ) : (∫ x, f (T x) ∂μ) = ∫ y, f y ∂ν := by
  have hle (f : M →ᵇ ℝ) : (∫ x, f (T x) ∂μ) ≤ ∫ y, f y ∂ν := by
    let s : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
    have hs (j : ℕ) : 0 < s j := by dsimp [s]; positivity
    have hslim : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim : Tendsto (fun j => ∫ x, transformedDifferenceQuotient v f (s j) x ∂μ)
        atTop (𝓝 (∫ x, -f (T x) ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
      · intro j
        exact (transformedDifferenceQuotient v f (s j)).continuous.aestronglyMeasurable
      · exact integrable_const _
      · intro j
        exact Eventually.of_forall (transformedDifferenceQuotient_norm_le v f (hs j))
      · filter_upwards [hsingle] with x hx
        exact transformedDifferenceQuotient_tendsto_at v f x (T x) (hcontact x) hx hs hslim
    have hineq (j : ℕ) : -(∫ y, f y ∂ν) ≤
        ∫ x, transformedDifferenceQuotient v f (s j) x ∂μ := by
      let a := boundedCTransform (v + s j • f)
      let b : M →ᵇ ℝ := v + s j • f
      have hi := hmin a b (cTransform_gap_nonneg b.continuous)
      have hb : (∫ y, b y ∂ν) = (∫ y, v y ∂ν) + s j * ∫ y, f y ∂ν := by
        change (∫ y, v y + s j * f y ∂ν) = _
        rw [integral_add (v.integrable ν) ((f.integrable ν).const_mul (s j)),
          integral_const_mul]
      have hq : (∫ x, transformedDifferenceQuotient v f (s j) x ∂μ) =
          ((∫ x, a x ∂μ) - (∫ x, boundedCTransform v x ∂μ)) / s j := by
        change (∫ x, (s j)⁻¹ * (a x - boundedCTransform v x) ∂μ) = _
        rw [integral_const_mul,integral_sub (a.integrable μ) ((boundedCTransform v).integrable μ)]
        rw [div_eq_mul_inv,mul_comm]
      rw [hq]
      apply (le_div_iff₀ (hs j)).mpr
      change (∫ x, boundedCTransform v x ∂μ) + (∫ y, v y ∂ν) ≤
        (∫ x, a x ∂μ) + (∫ y, b y ∂ν) at hi
      rw [hb] at hi
      nlinarith
    have hbound := ge_of_tendsto' hlim hineq
    rw [integral_neg] at hbound
    linarith
  apply le_antisymm (hle f)
  have hneg := hle (-f)
  simp only [BoundedContinuousFunction.neg_apply,integral_neg] at hneg
  linarith

omit [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma cost_contact_relation_isClosed (u v : M →ᵇ ℝ) :
    IsClosed {z : M × M | contactGap u v z.1 z.2 = 0} := by
  apply isClosed_eq _ continuous_const
  exact ((u.continuous.comp continuous_fst).add
    (((continuous_fst.dist continuous_snd).pow 2).div_const 2)).add
    (v.continuous.comp continuous_snd)

lemma dual_minimum_ae_pushforward (μ ν : Measure M) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (v : M →ᵇ ℝ) (T : M → M)
    (hcontact : ∀ x, contactGap (cTransform v) v x (T x) = 0)
    (hsingle : ∀ᵐ x ∂μ, ∀ y, contactGap (cTransform v) v x y = 0 → y = T x)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective μ ν (boundedCTransform v,v) ≤ dualObjective μ ν (a,b)) :
    AEMeasurable T μ ∧ Measure.map T μ = ν := by
  have hT : AEMeasurable T μ := aemeasurable_closed_relation_selector
    (cost_contact_relation_isClosed (boundedCTransform v) v) hcontact hsingle
  refine ⟨hT,?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hT f.continuous.aestronglyMeasurable]
  exact dual_minimum_ae_integral_eq μ ν v T hcontact hsingle hmin f

end CompactAE
end WeakMTWTransport

end

end

end

end OAI
