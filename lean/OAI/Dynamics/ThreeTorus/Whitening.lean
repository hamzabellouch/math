import OAI.Dynamics.ThreeTorus.RetainedPackets

namespace OAI

/-! Exact coefficient-space spectral whitening, including the zero-density set. -/

section

/-!
Exact coefficient-space whitening, including the zero
set of the spectral density. The frequency map is arbitrary; for torus packets
it is `(m,u,a) ↦ m φ(u) mod 1`. No nonvanishing of the density is imposed.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical
namespace ThreeTorus

/-- Squared modulus as a nonnegative measure density. -/
def energyWeight {X : Type*} (F : X → ℂ) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal (‖F x‖ ^ 2)

lemma measurable_energyWeight {X : Type*} [MeasurableSpace X] {F : X → ℂ}
    (hF : Measurable F) : Measurable (energyWeight F) :=
  (hF.norm.pow_const 2).ennreal_ofReal

lemma energyWeight_mul {X : Type*} (a F : X → ℂ) :
    energyWeight (fun x => a x * F x) = energyWeight F * energyWeight a := by
  funext x
  simp only [energyWeight, norm_mul, mul_pow, Pi.mul_apply,
    ENNReal.ofReal_mul (sq_nonneg _)]
  exact mul_comm _ _

/-- Spectral multipliers act by multiplying the pushforward energy density. -/
lemma energy_map_multiplier {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {ζ : X → Y} {F : X → ℂ} {p : Y → ℝ≥0∞}
    (hζ : Measurable ζ) (hF : Measurable F) (hp : Measurable p)
    (hpush : (μ.withDensity (energyWeight F)).map ζ = ν.withDensity p)
    {a : Y → ℂ} (ha : Measurable a) :
    (μ.withDensity (energyWeight (fun x => a (ζ x) * F x))).map ζ =
      ν.withDensity (p * energyWeight a) := by
  rw [energyWeight_mul]
  change (μ.withDensity (energyWeight F * (energyWeight a ∘ ζ))).map ζ = _
  rw [withDensity_mul μ (measurable_energyWeight hF)
    ((measurable_energyWeight ha).comp hζ),
    map_withDensity_comp _ hζ (measurable_energyWeight ha), hpush,
    ← withDensity_mul ν hp (measurable_energyWeight ha)]

/-- A coefficient is zero almost everywhere over the zero set of its spectral density. -/
lemma energy_zero_fiber {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {ζ : X → Y} {F : X → ℂ} {p : Y → ℝ}
    (hζ : Measurable ζ) (hF : Measurable F) (hp : Measurable p)
    (hpush : (μ.withDensity (energyWeight F)).map ζ =
      ν.withDensity (fun y => ENNReal.ofReal (p y))) :
    ∀ᵐ x ∂μ, p (ζ x) = 0 → F x = 0 := by
  have hs : MeasurableSet {y | p y = 0} := measurableSet_eq_fun hp measurable_const
  have hz : (μ.withDensity (energyWeight F)) (ζ ⁻¹' {y | p y = 0}) = 0 := by
    rw [← Measure.map_apply hζ hs, hpush, withDensity_apply _ hs]
    apply setLIntegral_eq_zero hs
    intro y hy
    change p y = 0 at hy
    simp [hy]
  rw [withDensity_apply _ (hζ hs), lintegral_eq_zero_iff
    (measurable_energyWeight hF)] at hz
  have hza := (ae_restrict_iff' (hζ hs)).1 hz
  filter_upwards [hza] with x hx hpx
  have h := hx hpx
  have hz' : ‖F x‖ ^ 2 = 0 := (ENNReal.ofReal_eq_zero.mp h).antisymm (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz')

/-- The exact whitening coefficient, filling the density's zero set with a flat vector. -/
def whitenCoefficient {X Y : Type*} (ζ : X → Y) (p : Y → ℝ)
    (F V : X → ℂ) (x : X) : ℂ :=
  if p (ζ x) = 0 then V x else F x / (Real.sqrt (p (ζ x)) : ℂ)

lemma measurable_whitenCoefficient {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ζ : X → Y} {p : Y → ℝ} {F V : X → ℂ}
    (hζ : Measurable ζ) (hp : Measurable p) (hF : Measurable F) (hV : Measurable V) :
    Measurable (whitenCoefficient ζ p F V) := by
  apply Measurable.ite (measurableSet_eq_fun (hp.comp hζ) measurable_const) hV
  exact hF.div (Complex.measurable_ofReal.comp ((hp.comp hζ).sqrt))

lemma whiten_reconstruct {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {ζ : X → Y} {F V : X → ℂ} {p : Y → ℝ}
    (hζ : Measurable ζ) (hF : Measurable F) (hp : Measurable p) (hpn : ∀ y, 0 ≤ p y)
    (hpush : (μ.withDensity (energyWeight F)).map ζ =
      ν.withDensity (fun y => ENNReal.ofReal (p y))) :
    (fun x => (Real.sqrt (p (ζ x)) : ℂ) * whitenCoefficient ζ p F V x) =ᵐ[μ] F := by
  filter_upwards [energy_zero_fiber hζ hF hp hpush] with x hx
  by_cases h : p (ζ x) = 0
  · simp [whitenCoefficient, h, hx h]
  · have hp₀ : 0 < p (ζ x) := lt_of_le_of_ne (hpn _) (Ne.symm h)
    have hs : (Real.sqrt (p (ζ x)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hp₀).ne'
    simp only [whitenCoefficient, ite_eq_right h]
    exact mul_div_cancel₀ _ hs

/-- A piecewise multiplier rule: the two spectral supports can overlap in
angular index; it is their frequency supports that are disjoint. -/
lemma energy_map_piecewise {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {ζ : X → Y} {F V : X → ℂ}
    {p q : Y → ℝ≥0∞} {s : Set Y}
    (hζ : Measurable ζ) (hF : Measurable F) (hV : Measurable V)
    (hp : Measurable p) (hq : Measurable q) (hs : MeasurableSet s)
    (hpushF : (μ.withDensity (energyWeight F)).map ζ = ν.withDensity p)
    (hpushV : (μ.withDensity (energyWeight V)).map ζ = ν.withDensity q)
    {a b : Y → ℂ} (ha : Measurable a) (hb : Measurable b) :
    (μ.withDensity (energyWeight (fun x => if ζ x ∈ s then a (ζ x) * F x
      else b (ζ x) * V x))).map ζ =
      ν.withDensity (fun y => if y ∈ s then p y * energyWeight a y
        else q y * energyWeight b y) := by
  classical
  have henergy : energyWeight (fun x => if ζ x ∈ s then a (ζ x) * F x
      else b (ζ x) * V x) =
      energyWeight (fun x => (s.indicator a) (ζ x) * F x) +
      energyWeight (fun x => (sᶜ.indicator b) (ζ x) * V x) := by
    funext x
    by_cases hx : ζ x ∈ s <;> simp [hx, energyWeight]
  have hm : Measurable (energyWeight (fun x => (s.indicator a) (ζ x) * F x)) :=
    measurable_energyWeight (((ha.indicator hs).comp hζ).mul hF)
  rw [henergy, withDensity_add_left hm,
    Measure.map_add _ _ hζ,
    energy_map_multiplier hζ hF hp hpushF (ha.indicator hs),
    energy_map_multiplier hζ hV hq hpushV (hb.indicator hs.compl),
    ← withDensity_add_left (hp.mul (measurable_energyWeight (ha.indicator hs)))]
  congr 1
  funext y
  by_cases hy : y ∈ s <;> simp [hy, energyWeight]

lemma positive_whitening_weight {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal t * ENNReal.ofReal (‖(Real.sqrt t : ℂ)⁻¹‖ ^ 2) = 1 := by
  have he : ‖(Real.sqrt t : ℂ)⁻¹‖ ^ 2 = t⁻¹ := by
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt ht.le]
  rw [he, ← ENNReal.ofReal_mul ht.le, mul_inv_cancel₀ ht.ne', ENNReal.ofReal_one]

/-- Exact flat output intensity, including the zero set, without requiring
angular supports of the two coefficient families to be disjoint. -/
lemma whiten_energy_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {ζ : X → Y} {F V : X → ℂ} {p : Y → ℝ}
    (hζ : Measurable ζ) (hF : Measurable F) (hV : Measurable V)
    (hp : Measurable p) (hpn : ∀ y, 0 ≤ p y)
    (hpush : (μ.withDensity (energyWeight F)).map ζ =
      ν.withDensity (fun y => ENNReal.ofReal (p y)))
    (hflat : (μ.withDensity (energyWeight V)).map ζ = ν) :
    (μ.withDensity (energyWeight (whitenCoefficient ζ p F V))).map ζ = ν := by
  have hs : MeasurableSet {y | p y = 0} := measurableSet_eq_fun hp measurable_const
  have hflat' : (μ.withDensity (energyWeight V)).map ζ = ν.withDensity (fun _ => 1) := by
    simpa only [withDensity_const, one_smul] using hflat
  have hm := energy_map_piecewise hζ hV hF measurable_const hp.ennreal_ofReal hs hflat' hpush
    (measurable_const (a := (1 : ℂ))) ((Complex.measurable_ofReal.comp hp.sqrt).inv)
  have he : (fun x => if ζ x ∈ {y | p y = 0} then (1 : ℂ) * V x
      else (Real.sqrt (p (ζ x)) : ℂ)⁻¹ * F x) = whitenCoefficient ζ p F V := by
    funext x
    simp only [whitenCoefficient, mem_ofPred_eq, one_mul, div_eq_mul_inv]
    congr 1
    exact mul_comm _ _
  change (μ.withDensity (energyWeight (fun x => if ζ x ∈ {y | p y = 0}
      then (1 : ℂ) * V x else (Real.sqrt (p (ζ x)) : ℂ)⁻¹ * F x))).map ζ =
    ν.withDensity (fun y => if y ∈ {y | p y = 0}
      then (1 : ℝ≥0∞) * energyWeight (fun _ => (1 : ℂ)) y
      else ENNReal.ofReal (p y) * energyWeight (fun y => (Real.sqrt (p y) : ℂ)⁻¹) y) at hm
  rw [he] at hm
  rw [hm]
  have hd : (fun y => if y ∈ {y | p y = 0} then (1 : ℝ≥0∞) * energyWeight (fun _ => (1 : ℂ)) y
      else ENNReal.ofReal (p y) * energyWeight (fun y => (Real.sqrt (p y) : ℂ)⁻¹) y) = 1 := by
    funext y
    by_cases hy : p y = 0
    · simp [hy, energyWeight]
    · simp only [mem_ofPred_eq, ite_eq_right hy, Pi.one_apply, energyWeight]
      exact positive_whitening_weight (lt_of_le_of_ne (hpn _) (Ne.symm hy))
  rw [hd, withDensity_one]

lemma whitening_scalar_distance {t : ℝ} (ht : 0 < t) :
    t * ‖(Real.sqrt t : ℂ)⁻¹ - 1‖ ^ 2 = (Real.sqrt t - 1) ^ 2 := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have hsq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  rw [← Complex.ofReal_inv, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  field_simp
  nlinarith [sq_nonneg (Real.sqrt t - 1)]

/-- The error's entire spectral density, not just its total mass, is exactly
`(√p - 1)²`. This entails the source's whitening-distance identity. -/
lemma whiten_error_energy_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {ζ : X → Y} {F V : X → ℂ} {p : Y → ℝ}
    (hζ : Measurable ζ) (hF : Measurable F) (hV : Measurable V)
    (hp : Measurable p) (hpn : ∀ y, 0 ≤ p y)
    (hpush : (μ.withDensity (energyWeight F)).map ζ =
      ν.withDensity (fun y => ENNReal.ofReal (p y)))
    (hflat : (μ.withDensity (energyWeight V)).map ζ = ν) :
    (μ.withDensity (energyWeight (fun x => whitenCoefficient ζ p F V x - F x))).map ζ =
      ν.withDensity (fun y => ENNReal.ofReal ((Real.sqrt (p y) - 1) ^ 2)) := by
  have hs : MeasurableSet {y | p y = 0} := measurableSet_eq_fun hp measurable_const
  have hflat' : (μ.withDensity (energyWeight V)).map ζ = ν.withDensity (fun _ => 1) := by
    simpa only [withDensity_const, one_smul] using hflat
  have hm := energy_map_piecewise hζ hV hF measurable_const hp.ennreal_ofReal hs hflat' hpush
    (measurable_const (a := (1 : ℂ)))
    (((Complex.measurable_ofReal.comp hp.sqrt).inv).sub (measurable_const (a := (1 : ℂ))))
  change (μ.withDensity (energyWeight (fun x => if ζ x ∈ {y | p y = 0}
      then (1 : ℂ) * V x else ((Real.sqrt (p (ζ x)) : ℂ)⁻¹ - 1) * F x))).map ζ =
    ν.withDensity (fun y => if y ∈ {y | p y = 0}
      then (1 : ℝ≥0∞) * energyWeight (fun _ => (1 : ℂ)) y
      else ENNReal.ofReal (p y) * energyWeight (fun y => (Real.sqrt (p y) : ℂ)⁻¹ - 1) y) at hm
  have hae : energyWeight (fun x => whitenCoefficient ζ p F V x - F x) =ᵐ[μ]
      energyWeight (fun x => if ζ x ∈ {y | p y = 0} then (1 : ℂ) * V x
        else ((Real.sqrt (p (ζ x)) : ℂ)⁻¹ - 1) * F x) := by
    filter_upwards [energy_zero_fiber hζ hF hp hpush] with x hx
    unfold energyWeight
    congr 2
    by_cases h : p (ζ x) = 0
    · simp [whitenCoefficient, h, hx h]
    · simp only [whitenCoefficient, ite_eq_right h]
      ring_nf
  rw [withDensity_congr_ae hae, hm]
  congr 1
  funext y
  by_cases hy : p y = 0
  · simp [hy, energyWeight]
  · simp only [mem_ofPred_eq, ite_eq_right hy, energyWeight]
    rw [← ENNReal.ofReal_mul (hpn y),
      whitening_scalar_distance (lt_of_le_of_ne (hpn _) (Ne.symm hy))]

lemma energy_map_total {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {ζ : X → Y} {F : X → ℂ} {p : Y → ℝ≥0∞}
    (hζ : Measurable ζ)
    (hpush : (μ.withDensity (energyWeight F)).map ζ = ν.withDensity p) :
    (∫⁻ x, energyWeight F x ∂μ) = ∫⁻ y, p y ∂ν := by
  have ht := congrArg (fun η : Measure Y => η univ) hpush
  simpa only [Measure.map_apply hζ MeasurableSet.univ, preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using ht

/-- The whitened coefficient really belongs to L² whenever the spectral reference
measure is finite; its possible singular multiplier does not obstruct this. -/
lemma whiten_memLp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure ν]
    {ζ : X → Y} {F V : X → ℂ} {p : Y → ℝ}
    (hζ : Measurable ζ) (hF : Measurable F) (hV : Measurable V)
    (hp : Measurable p) (hpn : ∀ y, 0 ≤ p y)
    (hpush : (μ.withDensity (energyWeight F)).map ζ =
      ν.withDensity (fun y => ENNReal.ofReal (p y)))
    (hflat : (μ.withDensity (energyWeight V)).map ζ = ν) :
    MemLp (whitenCoefficient ζ p F V) 2 μ := by
  have hw := measurable_whitenCoefficient hζ hp hF hV
  apply (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).2
  refine ⟨(hw.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs, abs_pow, abs_norm]
  change (∫⁻ x, energyWeight (whitenCoefficient ζ p F V) x ∂μ) < ∞
  have ht := whiten_energy_map hζ hF hV hp hpn hpush hflat
  have ht' : (μ.withDensity (energyWeight (whitenCoefficient ζ p F V))).map ζ =
      ν.withDensity (fun _ => 1) := by simpa only [withDensity_const, one_smul] using ht
  rw [energy_map_total hζ ht']
  simp

lemma whiten_distance_integral {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {ζ : X → Y} {F V : X → ℂ} {p : Y → ℝ}
    (hζ : Measurable ζ) (hF : Measurable F) (hV : Measurable V)
    (hp : Measurable p) (hpn : ∀ y, 0 ≤ p y)
    (hpush : (μ.withDensity (energyWeight F)).map ζ =
      ν.withDensity (fun y => ENNReal.ofReal (p y)))
    (hflat : (μ.withDensity (energyWeight V)).map ζ = ν) :
    (∫ x, ‖whitenCoefficient ζ p F V x - F x‖ ^ 2 ∂μ) =
      ∫ y, (Real.sqrt (p y) - 1) ^ 2 ∂ν := by
  have he := integral_eq_lintegral_of_nonneg_ae
    (f := fun x => ‖whitenCoefficient ζ p F V x - F x‖ ^ 2)
    (μ := μ) (Eventually.of_forall (fun _ => sq_nonneg _))
    (((measurable_whitenCoefficient hζ hp hF hV).sub hF).norm.pow_const 2).aestronglyMeasurable
  have hp' := integral_eq_lintegral_of_nonneg_ae
    (f := fun y => (Real.sqrt (p y) - 1) ^ 2)
    (μ := ν) (Eventually.of_forall (fun _ => sq_nonneg _))
    ((hp.sqrt.sub measurable_const).pow_const 2).aestronglyMeasurable
  rw [he, hp']
  exact congrArg ENNReal.toReal (energy_map_total hζ
    (whiten_error_energy_map hζ hF hV hp hpn hpush hflat))

end ThreeTorus
end
end

end OAI
