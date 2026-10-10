import OAI.Probability.SLE.Loewner.CanonicalRadiusKernel
import OAI.Probability.SLE.SpatialMeans
import OAI.Probability.SLE.OccupationBound

namespace OAI

/-! Jointly measurable stopped-angle kernels on continuous driver space.
The uniform good-angle estimate is a consequence of the proved inverse-angle
moment bound under the finite centered law. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance angleDriverMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance angleDriverBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

def canonicalStoppedCenter (κ : ℝ) (q : ℝ × (ℂ × C(ℝ≥0, ℝ))) : ℂ :=
  (canonicalRadiusFamily κ).jointChart ((canonicalRadiusLevel κ q).toNNReal, q.2) -
    ((Real.sqrt κ * q.2.2 (canonicalRadiusLevel κ q).toNNReal : ℝ) : ℂ)

def canonicalStoppedSine (κ : ℝ) (q : ℝ × (ℂ × C(ℝ≥0, ℝ))) : ℝ :=
  if canonicalRadiusLevel κ q < ∞ then Real.sin (canonicalStoppedCenter κ q).arg else 0

def canonicalStoppedAngleSq (κ : ℝ) (q : ℝ × (ℂ × C(ℝ≥0, ℝ))) : ℝ :=
  (canonicalStoppedSine κ q) ^ 2

def canonicalInverseAngle (κ : ℝ) (q : ℝ × (ℂ × C(ℝ≥0, ℝ))) : ℝ :=
  (canonicalStoppedAngleSq κ q) ^ (-greenExponent κ / 2)

lemma canonicalStoppedCenter_measurable (κ : ℝ) : Measurable (canonicalStoppedCenter κ) := by
  have ht := ENNReal.measurable_toNNReal.comp (canonicalRadiusLevel_measurable κ)
  have hp : Measurable (fun q : ℝ × (ℂ × C(ℝ≥0, ℝ)) => q.2.2) :=
    measurable_snd.comp measurable_snd
  have he := continuous_eval.measurable.comp (hp.prodMk ht)
  exact ((canonicalRadiusFamily κ).jointChart_measurable.comp
    (ht.prodMk measurable_snd)).sub (Complex.measurable_ofReal.comp (he.const_mul _))

lemma canonicalStoppedSine_measurable (κ : ℝ) : Measurable (canonicalStoppedSine κ) :=
  Measurable.ite (measurableSet_lt (canonicalRadiusLevel_measurable κ) measurable_const)
    (Real.measurable_sin.comp (Complex.measurable_arg.comp
      (canonicalStoppedCenter_measurable κ))) measurable_const

lemma canonicalStoppedAngleSq_measurable (κ : ℝ) : Measurable (canonicalStoppedAngleSq κ) :=
  (canonicalStoppedSine_measurable κ).pow_const 2

lemma canonicalInverseAngle_measurable (κ : ℝ) : Measurable (canonicalInverseAngle κ) :=
  (canonicalStoppedAngleSq_measurable κ).pow measurable_const

lemma canonicalStoppedAngleSq_nonneg (κ : ℝ) (q : ℝ × (ℂ × C(ℝ≥0, ℝ))) :
    0 ≤ canonicalStoppedAngleSq κ q := sq_nonneg _

lemma canonicalInverseAngle_nonneg (κ : ℝ) (q : ℝ × (ℂ × C(ℝ≥0, ℝ))) :
    0 ≤ canonicalInverseAngle κ q := Real.rpow_nonneg (sq_nonneg _) _

lemma canonicalStoppedCenter_eq (κ : ℝ) (p : C(ℝ≥0, ℝ))
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * p t) γ G F)
    (u : ℝ) (hu : 0 ≤ u) (z : ℂ)
    (hfinite : radiusLevelTime γ G z u < ∞) :
    canonicalStoppedCenter κ (u, z, p) =
      G (radiusLevelTime γ G z u).toNNReal z -
        ((Real.sqrt κ * p (radiusLevelTime γ G z u).toNNReal : ℝ) : ℂ) := by
  obtain ⟨T, hT, hTR⟩ := exists_live_level_of_radiusLevelTime_lt_top γ G z u hfinite
  have he := radiusLevelTime_eq_of_live_level (p.continuous.const_mul _) hw z u T hT hTR
  unfold canonicalStoppedCenter
  rw [canonicalRadiusLevel_eq κ p hw u hu z, he, ENNReal.toNNReal_coe,
    (canonicalRadiusFamily κ).jointChart_eq p (p.continuous.const_mul _) hw T z,
    ite_eq_left hT]

lemma canonicalStoppedSine_eq (κ : ℝ) (p : C(ℝ≥0, ℝ))
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * p t) γ G F)
    (u : ℝ) (hu : 0 ≤ u) (z : ℂ)
    (hfinite : radiusLevelTime γ G z u < ∞) :
    canonicalStoppedSine κ (u, z, p) =
      Real.sin (Complex.arg (G (radiusLevelTime γ G z u).toNNReal z -
        ((Real.sqrt κ * p (radiusLevelTime γ G z u).toNNReal : ℝ) : ℂ))) := by
  rw [canonicalStoppedSine, canonicalRadiusLevel_eq κ p hw u hu z, ite_eq_left hfinite,
    canonicalStoppedCenter_eq κ p hw u hu z hfinite]

lemma canonicalStoppedAngleSq_eq (κ : ℝ) (p : C(ℝ≥0, ℝ))
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * p t) γ G F)
    (u : ℝ) (hu : 0 ≤ u) (z : ℂ) :
    canonicalStoppedAngleSq κ (u, z, p) =
      stoppedAngleSq κ (fun t => p t) γ G z u := by
  unfold canonicalStoppedAngleSq canonicalStoppedSine stoppedAngleSq
  rw [canonicalRadiusLevel_eq κ p hw u hu z]
  split_ifs with hf
  · rw [canonicalStoppedCenter_eq κ p hw u hu z hf]
  · norm_num

lemma canonicalInverseAngle_eq (κ : ℝ) (p : C(ℝ≥0, ℝ))
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * p t) γ G F)
    (u : ℝ) (hu : 0 ≤ u) (z : ℂ) :
    canonicalInverseAngle κ (u, z, p) =
      stoppedInverseAngle κ (fun t => p t) γ G z u (greenExponent κ) := by
  rw [canonicalInverseAngle, stoppedInverseAngle, canonicalStoppedAngleSq_eq κ p hw u hu z]

lemma measurable_canonicalStoppedSine_random_state
    {Ω : Type*} [MeasurableSpace Ω] (κ : ℝ)
    {Y : Ω → C(ℝ≥0, ℝ)} (hY : Measurable Y)
    {u : Ω → ℝ} (hu : Measurable u) {z : Ω → ℂ} (hz : Measurable z) :
    Measurable (fun ω => canonicalStoppedSine κ (u ω, z ω, Y ω)) :=
  (canonicalStoppedSine_measurable κ).comp (hu.prodMk (hz.prodMk hY))

/-- One common measurable event can be used for all random marked states. -/
lemma measurableSet_canonical_good_angle_random_state
    {Ω : Type*} [MeasurableSpace Ω] (κ s : ℝ)
    {Y : Ω → C(ℝ≥0, ℝ)} (hY : Measurable Y)
    {u : Ω → ℝ} (hu : Measurable u) {z : Ω → ℂ} (hz : Measurable z) :
    MeasurableSet {ω | canonicalRadiusLevel κ (u ω, z ω, Y ω) < ∞ ∧
      s ≤ canonicalStoppedSine κ (u ω, z ω, Y ω)} :=
  (measurableSet_lt (measurable_canonicalRadiusLevel_random_state κ hY hu hz)
    measurable_const).inter
    (measurableSet_le measurable_const (measurable_canonicalStoppedSine_random_state κ hY hu hz))

/-- The inverse-angle moment bound, represented by a
single jointly measurable canonical kernel. -/
theorem canonical_uniform_inverse_angle
    (ν : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure ν]
    (hB : IsBrownianReal (fun (t : ℝ≥0) (p : C(ℝ≥0, ℝ)) => p t) ν)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ))
    (Gc Fc : C(ℝ≥0, ℝ) → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ p ∂ν, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * p t) (Φ p) (Gc p) (Fc p))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (v : ℝ≥0) (hv : 1 ≤ (v : ℝ)) :
    Integrable (fun p => canonicalInverseAngle κ ((v : ℝ), z, p))
      (ν.withDensity (fun p => canonicalFiniteDensity κ ((v : ℝ), z, p))) ∧
    (∫ p, canonicalInverseAngle κ ((v : ℝ), z, p)
      ∂ν.withDensity (fun p => canonicalFiniteDensity κ ((v : ℝ), z, p))) ≤
        uniformInverseAngleConstant κ 1 := by
  obtain ⟨hi, hb⟩ := uniform_inverse_angle hB κ hκ hκ8
    (fun p t => Φ p t) Gc Fc hw z hz 1 (by norm_num) v hv
  have heq := canonical_finiteCenteredLaw_eq ν κ Φ Gc Fc hw v v.coe_nonneg z
  rw [heq] at hi hb
  have he : (fun p => stoppedInverseAngle κ (fun t => p t) (Φ p) (Gc p) z v
      (greenExponent κ)) =ᵐ[ν.withDensity (fun p => canonicalFiniteDensity κ ((v : ℝ), z, p))]
      (fun p => canonicalInverseAngle κ ((v : ℝ), z, p)) := by
    filter_upwards [(withDensity_absolutelyContinuous ν _).ae_le hw] with p hp
    exact (canonicalInverseAngle_eq κ p hp v v.coe_nonneg z).symm
  exact ⟨hi.congr he, (integral_congr_ae he).symm.trans_le hb⟩

/-- Under the finite centered law the canonical stopped point is live and
its angle is strictly in the upper half-plane. -/
theorem canonical_finiteCenteredLaw_live_angle
    (ν : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure ν]
    (hB : IsBrownianReal (fun (t : ℝ≥0) (p : C(ℝ≥0, ℝ)) => p t) ν)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ))
    (Gc Fc : C(ℝ≥0, ℝ) → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ p ∂ν, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * p t) (Φ p) (Gc p) (Fc p))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u) :
    ∀ᵐ p ∂ν.withDensity (fun p => canonicalFiniteDensity κ (u, z, p)),
      canonicalRadiusLevel κ (u, z, p) < ∞ ∧ 0 < canonicalStoppedSine κ (u, z, p) := by
  have hl := finiteCenteredLaw_live_compact hB κ hκ hκ8
    (fun p t => Φ p t) Gc Fc hw z hz u hu
  rw [canonical_finiteCenteredLaw_eq ν κ Φ Gc Fc hw u hu z] at hl
  filter_upwards [hl, (withDensity_absolutelyContinuous ν _).ae_le hw] with p hp hwp
  obtain ⟨T, hT, hTR, he, _⟩ := hp
  have hf : radiusLevelTime (Φ p) (Gc p) z u < ∞ := by
    rw [he]
    exact ENNReal.coe_lt_top
  refine ⟨by rwa [canonicalRadiusLevel_eq κ p hwp u hu z], ?_⟩
  rw [canonicalStoppedSine, canonicalRadiusLevel_eq κ p hwp u hu z, ite_eq_left hf,
    canonicalStoppedCenter_eq κ p hwp u hu z hf, he, ENNReal.toNNReal_coe,
    Complex.sin_arg]
  apply div_pos
  · simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hwp.imag_positive T z hT
  · apply norm_pos_iff.mpr
    intro hezero
    have him := hwp.imag_positive T z hT
    have heIm := congrArg Complex.im hezero
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, sub_zero] at heIm
    exact (ne_of_gt him) heIm

/-- A uniform positive fraction of every finite centered law has an angle
bounded away from the real axis. The same threshold works for every marked
point and every radius level at least one. -/
theorem canonical_uniform_good_angle
    (ν : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure ν]
    (hB : IsBrownianReal (fun (t : ℝ≥0) (p : C(ℝ≥0, ℝ)) => p t) ν)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ))
    (Gc Fc : C(ℝ≥0, ℝ) → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ p ∂ν, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * p t) (Φ p) (Gc p) (Fc p)) :
    ∃ s : ℝ, 0 < s ∧ ∀ z ∈ upperHalfPlane, ∀ v : ℝ≥0, 1 ≤ (v : ℝ) →
      ENNReal.ofReal (1 / 2 : ℝ) ≤
        (ν.withDensity (fun p => canonicalFiniteDensity κ ((v : ℝ), z, p)))
          {p | canonicalRadiusLevel κ ((v : ℝ), z, p) < ∞ ∧
            s ≤ canonicalStoppedSine κ ((v : ℝ), z, p)} := by
  let K := uniformInverseAngleConstant κ 1
  have hK : 0 < K := uniformInverseAngleConstant_pos κ 1 hκ hκ8 (by norm_num)
  let M := 2 * K + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let b := -greenExponent κ / 2
  have hb : b < 0 := by dsimp [b]; linarith [greenExponent_pos κ hκ hκ8]
  let d := M ^ b⁻¹
  have hd : 0 < d := Real.rpow_pos_of_pos hM _
  have hdM : d ^ b = M := Real.rpow_inv_rpow hM.le hb.ne
  refine ⟨Real.sqrt d, Real.sqrt_pos.mpr hd, ?_⟩
  intro z hz v hv
  let Q := ν.withDensity (fun p => canonicalFiniteDensity κ ((v : ℝ), z, p))
  have hprob : IsProbabilityMeasure Q := by
    dsimp only [Q]
    rw [← canonical_finiteCenteredLaw_eq ν κ Φ Gc Fc hw v v.coe_nonneg z]
    exact finiteCenteredLaw_probability hB κ hκ hκ8 (fun p t => Φ p t) Gc Fc hw z hz v v.coe_nonneg
  let : IsProbabilityMeasure Q := hprob
  let X := fun p => canonicalInverseAngle κ ((v : ℝ), z, p)
  obtain ⟨hXi, hXb⟩ := canonical_uniform_inverse_angle ν hB κ hκ hκ8 Φ Gc Fc hw z hz v hv
  let A : Set C(ℝ≥0, ℝ) := {p | M ≤ X p}
  let E : Set C(ℝ≥0, ℝ) := {p | canonicalRadiusLevel κ ((v : ℝ), z, p) < ∞ ∧
    Real.sqrt d ≤ canonicalStoppedSine κ ((v : ℝ), z, p)}
  have hA : Q A ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    apply (nonnegative_integral_tail X hXi
      (fun p => canonicalInverseAngle_nonneg κ _) K M hM hXb).trans
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ hM).mpr
    dsimp [M]
    linarith
  have hcover : ∀ᵐ p ∂Q, p ∈ A ∪ E := by
    filter_upwards [canonical_finiteCenteredLaw_live_angle ν hB κ hκ hκ8 Φ Gc Fc hw
      z hz v v.coe_nonneg] with p hp
    by_cases hAp : M ≤ X p
    · exact Or.inl hAp
    right
    refine ⟨hp.1, ?_⟩
    have hx : 0 < canonicalStoppedAngleSq κ ((v : ℝ), z, p) := sq_pos_of_pos hp.2
    have hdx : d ≤ canonicalStoppedAngleSq κ ((v : ℝ), z, p) := by
      apply ((Real.rpow_le_rpow_iff_of_neg hx hd hb)).mp
      rw [hdM]
      exact le_of_lt (lt_of_not_ge hAp)
    exact (Real.sqrt_le_iff).mpr ⟨hp.2.le, by simpa only [canonicalStoppedAngleSq] using hdx⟩
  have htotal : 1 ≤ Q A + Q E := by
    calc
      1 = Q Set.univ := (measure_univ : Q Set.univ = 1).symm
      _ ≤ Q (A ∪ E) := measure_mono_ae (hcover.mono fun _ hp _ => hp)
      _ ≤ Q A + Q E := measure_union_le _ _
  have htotalR := ENNReal.toReal_mono (by finiteness) htotal
  have hAR := ENNReal.toReal_mono (by finiteness) hA
  rw [ENNReal.toReal_one, ENNReal.toReal_add (by finiteness) (by finiteness)] at htotalR
  norm_num only [ENNReal.toReal_ofReal, show (0 : ℝ) ≤ 1 / 2 by norm_num, max_eq_left] at hAR
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num only [ENNReal.toReal_ofReal, show (0 : ℝ) ≤ 1 / 2 by norm_num, max_eq_left]
  linarith

end SLEExactGauge

end

end OAI
