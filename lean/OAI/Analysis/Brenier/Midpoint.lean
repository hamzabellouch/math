import OAI.Analysis.Brenier.Basic

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Problem358.IntervalMidpoint

/-- Lebesgue probability on the unit interval. -/
def unitLaw : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

instance unitLaw_probability : IsProbabilityMeasure unitLaw := by
  constructor
  norm_num [unitLaw, Real.volume_Icc]

/-- Lebesgue probability on a nondegenerate interval. -/
def intervalLaw (a b : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (b - a))⁻¹ • volume.restrict (Icc a b)

lemma map_volume_affine {a r : ℝ} (hr : 0 < r) :
    Measure.map (fun t : ℝ => a + r * t) volume =
      (ENNReal.ofReal r)⁻¹ • volume := by
  have hcomp : (fun t : ℝ => a + r * t) = (fun t : ℝ => a + t) ∘ (r * ·) := rfl
  rw [hcomp, ← Measure.map_map (measurable_const_add a) (measurable_const_mul r),
    Real.map_volume_mul_left hr.ne', Measure.map_smul _ (measurable_const_add a).aemeasurable,
    map_add_left_eq_self,
    abs_of_pos (inv_pos.mpr hr), ENNReal.ofReal_inv_of_pos hr]

lemma affine_preimage_interval {a b : ℝ} (hab : a < b) :
    (fun t : ℝ => a + (b - a) * t) ⁻¹' Icc a b = Icc (0 : ℝ) 1 := by
  ext t
  change (a ≤ a + (b - a) * t ∧ a + (b - a) * t ≤ b) ↔ (0 ≤ t ∧ t ≤ 1)
  constructor
  · intro h
    constructor <;> nlinarith [h.1, h.2]
  · intro h
    constructor <;> nlinarith [h.1, h.2]

lemma map_unitLaw_affine {a b : ℝ} (hab : a < b) :
    Measure.map (fun t : ℝ => a + (b - a) * t) unitLaw = intervalLaw a b := by
  unfold unitLaw intervalLaw
  rw [← affine_preimage_interval hab,
    ← Measure.restrict_map (by fun_prop) measurableSet_Icc,
    map_volume_affine (sub_pos.mpr hab), Measure.restrict_smul]

/-- The monotone coupling parametrized by the common unit-interval coordinate. -/
def coupling (a b c d : ℝ) : Measure (ℝ × ℝ) :=
  Measure.map (fun t : ℝ => (a + (b - a) * t, c + (d - c) * t)) unitLaw

lemma coupling_fst {a b c d : ℝ} (hab : a < b) :
    Measure.map Prod.fst (coupling a b c d) = intervalLaw a b := by
  unfold coupling
  rw [Measure.map_map measurable_fst (by fun_prop)]
  exact map_unitLaw_affine hab

lemma coupling_snd {a b c d : ℝ} (hcd : c < d) :
    Measure.map Prod.snd (coupling a b c d) = intervalLaw c d := by
  unfold coupling
  rw [Measure.map_map measurable_snd (by fun_prop)]
  exact map_unitLaw_affine hcd

lemma coupling_probability (a b c d : ℝ) : IsProbabilityMeasure (coupling a b c d) := by
  constructor
  rw [coupling, Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp

lemma midpoint_law {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    Measure.map (fun p : ℝ × ℝ => (p.1 + p.2) / 2) (coupling a b c d) =
      intervalLaw ((a + c) / 2) ((b + d) / 2) := by
  unfold coupling
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hfun : (fun p : ℝ × ℝ => (p.1 + p.2) / 2) ∘
      (fun t : ℝ => (a + (b - a) * t, c + (d - c) * t)) =
      (fun t : ℝ => (a + c) / 2 + ((b + d) / 2 - (a + c) / 2) * t) := by
    funext t
    dsimp
    ring
  rw [hfun]
  exact map_unitLaw_affine (by linarith)

lemma sqrt_lengthProduct_le_midpoint_length {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) :
    Real.sqrt ((b - a) * (d - c)) ≤ (b + d) / 2 - (a + c) / 2 := by
  rw [Real.sqrt_le_iff]
  constructor
  · linarith
  · nlinarith [sq_nonneg ((b - a) - (d - c))]

/-- The geometric-mean weighted midpoint law is dominated by Lebesgue measure
on the midpoint interval. This is the genuine one-dimensional midpoint coupling. -/
lemma midpoint_domination {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    ENNReal.ofReal (Real.sqrt ((b - a) * (d - c))) •
      Measure.map (fun p : ℝ × ℝ => (p.1 + p.2) / 2) (coupling a b c d) ≤
        volume.restrict (Icc ((a + c) / 2) ((b + d) / 2)) := by
  rw [midpoint_law hab hcd, intervalLaw, smul_smul]
  have hcoef : ENNReal.ofReal (Real.sqrt ((b - a) * (d - c))) *
      (ENNReal.ofReal ((b + d) / 2 - (a + c) / 2))⁻¹ ≤ 1 := by
    calc
      _ ≤ ENNReal.ofReal ((b + d) / 2 - (a + c) / 2) *
          (ENNReal.ofReal ((b + d) / 2 - (a + c) / 2))⁻¹ := by
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
          (sqrt_lengthProduct_le_midpoint_length hab hcd)) _
      _ ≤ 1 := ENNReal.mul_inv_le_one _
  intro s
  exact (mul_le_mul_left hcoef _).trans_eq (one_mul _)

lemma intervalLaw_probability {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (intervalLaw a b) := by
  rw [← map_unitLaw_affine hab]
  infer_instance

/-- Existence formulation, including both exact marginals and probability. -/
theorem exists_midpoint_coupling {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
      Measure.map Prod.fst π = intervalLaw a b ∧
      Measure.map Prod.snd π = intervalLaw c d ∧
      ENNReal.ofReal (Real.sqrt ((b - a) * (d - c))) •
        Measure.map (fun p : ℝ × ℝ => (p.1 + p.2) / 2) π ≤ volume := by
  refine ⟨coupling a b c d, coupling_probability _ _ _ _,
    coupling_fst hab, coupling_snd hcd, ?_⟩
  exact (midpoint_domination hab hcd).trans Measure.restrict_le_self

end Problem358.IntervalMidpoint

/-! One-dimensional substitution estimates for midpoint-coupling constructions.
These lemmas do not assume or assert existence of a triangular quantile map. -/

namespace Problem358

/-- Injective one-dimensional substitution followed by enlargement of the image.
No measurability assumption on the nonnegative integrand is needed. -/
theorem lintegral_jacobian_comp_le {s : Set ℝ} {f f' : ℝ → ℝ}
    (hs : MeasurableSet s)
    (hderiv : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hinj : InjOn f s) (g : ℝ → ℝ≥0∞) :
    (∫⁻ x in s, ENNReal.ofReal (|f' x|) * g (f x)) ≤ ∫⁻ y, g y := by
  rw [← lintegral_image_eq_lintegral_abs_deriv_mul hs hderiv hinj]
  exact lintegral_mono' Measure.restrict_le_self le_rfl

/-- A lower Jacobian bound controls pushforward integrals. -/
theorem lintegral_comp_le_of_deriv_lower {s : Set ℝ} {f f' : ℝ → ℝ} {c : ℝ}
    (hs : MeasurableSet s)
    (hderiv : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hinj : InjOn f s) (hbound : ∀ x ∈ s, c ≤ |f' x|)
    (g : ℝ → ℝ≥0∞) :
    ENNReal.ofReal c * (∫⁻ x in s, g (f x)) ≤ ∫⁻ y, g y := by
  calc
    ENNReal.ofReal c * (∫⁻ x in s, g (f x)) =
        ∫⁻ x in s, ENNReal.ofReal c * g (f x) :=
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ x in s, ENNReal.ofReal (|f' x|) * g (f x) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hs] with x hx
      exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hbound x hx)) (zero_le)
    _ ≤ ∫⁻ y, g y := lintegral_jacobian_comp_le hs hderiv hinj g

/-- Measure-valued form of the lower-Jacobian substitution bound. -/
theorem map_restrict_volume_smul_le_of_deriv_lower
    {s : Set ℝ} {f f' : ℝ → ℝ} {c : ℝ}
    (hs : MeasurableSet s)
    (hderiv : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hinj : InjOn f s) (hbound : ∀ x ∈ s, c ≤ |f' x|) :
    ENNReal.ofReal c • Measure.map f (volume.restrict s) ≤ volume := by
  have hcont : ContinuousOn f s := fun x hx => (hderiv x hx).continuousWithinAt
  have hmeas := hcont.aemeasurable (μ := volume) hs
  apply Measure.le_iff.mpr
  intro t ht
  rw [Measure.smul_apply, smul_eq_mul]
  calc
    ENNReal.ofReal c * (Measure.map f (volume.restrict s)) t =
        ENNReal.ofReal c * (∫⁻ y, t.indicator 1 y ∂Measure.map f (volume.restrict s)) := by
      rw [lintegral_indicator_one ht]
    _ = ENNReal.ofReal c * (∫⁻ x in s, t.indicator 1 (f x)) := by
      rw [lintegral_map' (f := t.indicator 1)
        (show AEMeasurable (t.indicator (1 : ℝ → ℝ≥0∞)) _ from
          (measurable_one.indicator ht).aemeasurable) hmeas]
    _ ≤ ∫⁻ y, t.indicator 1 y :=
      lintegral_comp_le_of_deriv_lower hs hderiv hinj hbound _
    _ = volume t := lintegral_indicator_one ht

/-- The derivative of the midpoint exceeds the geometric mean of the two
nonnegative derivatives. -/
theorem midpoint_derivative_ge_geometric_mean {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.sqrt (u * v) ≤ (u + v) / 2 := by
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · nlinarith [sq_nonneg (u - v)]

/-- Midpoint substitution with geometric-mean Jacobian weight. This is the
one-dimensional step in the triangular domination argument. -/
theorem lintegral_midpoint_geometric_jacobian_le
    {s : Set ℝ} {f f' g g' : ℝ → ℝ}
    (hs : MeasurableSet s) (hconv : Convex ℝ s)
    (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hg : ∀ x ∈ s, HasDerivWithinAt g (g' x) s x)
    (hfpos : ∀ x ∈ s, 0 < f' x) (hgpos : ∀ x ∈ s, 0 < g' x)
    (w : ℝ → ℝ≥0∞) :
    (∫⁻ x in s, ENNReal.ofReal (Real.sqrt (f' x * g' x)) *
      w ((f x + g x) / 2)) ≤ ∫⁻ y, w y := by
  have hmid (x : ℝ) (hx : x ∈ s) :
      HasDerivWithinAt (fun t => (f t + g t) / 2)
        ((f' x + g' x) / 2) s x :=
    ((hf x hx).add (hg x hx)).div_const 2
  have hmidpos (x : ℝ) (hx : x ∈ s) : 0 < (f' x + g' x) / 2 := by
    have h1 := hfpos x hx
    have h2 := hgpos x hx
    positivity
  have hmono : StrictMonoOn (fun t => (f t + g t) / 2) s := by
    apply strictMonoOn_of_hasDerivWithinAt_pos hconv
      (fun x hx => (hmid x hx).continuousWithinAt)
      (fun x hx => (hmid x (interior_subset hx)).mono interior_subset)
    intro x hx
    exact hmidpos x (interior_subset hx)
  calc
    (∫⁻ x in s, ENNReal.ofReal (Real.sqrt (f' x * g' x)) * w ((f x + g x) / 2)) ≤
        ∫⁻ x in s, ENNReal.ofReal (|(f' x + g' x) / 2|) * w ((f x + g x) / 2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hs] with x hx
      apply mul_le_mul_of_nonneg_right _ zero_le
      apply ENNReal.ofReal_le_ofReal
      rw [abs_of_pos (hmidpos x hx)]
      exact midpoint_derivative_ge_geometric_mean (hfpos x hx).le (hgpos x hx).le
    _ ≤ ∫⁻ y, w y := lintegral_jacobian_comp_le hs hmid hmono.injOn w

end Problem358

end

/-!
# Integral identities for the midpoint cell estimate

The integral estimates assume domination by a midpoint coupling.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem358

/-- Integration commutes with a finite weighted partition of a measure. -/
theorem integral_eq_weighted_sum_of_measure_partition
    {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (ρ : Measure X) (ν : ι → Measure X) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hpart : (∑ i, ENNReal.ofReal (c i) • ν i) = ρ)
    (f : X → ℝ) (hf : Integrable f ρ) :
    (∫ x, f x ∂ρ) = ∑ i, c i * ∫ x, f x ∂ν i := by
  have hi : ∀ i, ENNReal.ofReal (c i) • ν i ≤ ρ := by
    intro i
    rw [← hpart]
    exact Finset.single_le_sum (fun index _ => Measure.zero_le (ENNReal.ofReal (c index) • ν index))
      (Finset.mem_univ i)
  rw [← hpart, integral_finsetSum_measure]
  · simp only [integral_smul_measure, ENNReal.toReal_ofReal (hc _), smul_eq_mul]
  · intro i hi'
    exact hf.mono_measure (hi i)

/-- A finite family of dominated measures can be tested against any integrable
function which is nonnegative almost everywhere for the dominating total. -/
theorem weighted_integral_sum_le_of_measure_domination
    {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (ρ : Measure X) (μ ν : ι → Measure X) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hpart : (∑ i, μ i) = ρ)
    (hdom : ∀ i, ENNReal.ofReal (c i) • ν i ≤ μ i)
    (f : X → ℝ) (hf : Integrable f ρ) (hfn : 0 ≤ᵐ[ρ] f) :
    (∑ i, c i * ∫ x, f x ∂ν i) ≤ ∫ x, f x ∂ρ := by
  have hi : ∀ i, μ i ≤ ρ := by
    intro i
    rw [← hpart]
    exact Finset.single_le_sum (fun j _ => Measure.zero_le _) (Finset.mem_univ i)
  have hfi : ∀ i, Integrable f (μ i) := fun i => hf.mono_measure (hi i)
  calc
    (∑ i, c i * ∫ x, f x ∂ν i) ≤ ∑ i, ∫ x, f x ∂μ i := by
      apply Finset.sum_le_sum
      intro i hi'
      have h := integral_mono_measure (hdom i) (ae_mono (hi i) hfn) (hfi i)
      simpa only [integral_smul_measure, ENNReal.toReal_ofReal (hc i), smul_eq_mul] using h
    _ = ∫ x, f x ∂ρ := by
      rw [← hpart, integral_finsetSum_measure]
      exact fun i _ => hfi i

/-- The parallelogram identity, written for the concave quadratic test function. -/
theorem quadratic_midpoint_identity {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (R : ℝ) (x z : V) :
    R ^ 2 - ‖(1 / 2 : ℝ) • (x + z)‖ ^ 2 =
      ((R ^ 2 - ‖x‖ ^ 2) + (R ^ 2 - ‖z‖ ^ 2)) / 2 + ‖x - z‖ ^ 2 / 4 := by
  rw [norm_smul, mul_pow, norm_add_sq_real, norm_sub_sq_real]
  norm_num
  ring

/-- Integrating the midpoint identity requires only the explicit integrability
of its endpoint and displacement terms. -/
theorem integral_quadratic_midpoint_identity
    {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (μ : Measure Ω) (X Z : Ω → V) (R : ℝ)
    (hX : Integrable (fun ω => R ^ 2 - ‖X ω‖ ^ 2) μ)
    (hZ : Integrable (fun ω => R ^ 2 - ‖Z ω‖ ^ 2) μ)
    (hD : Integrable (fun ω => ‖X ω - Z ω‖ ^ 2) μ) :
    (∫ ω, R ^ 2 - ‖(1 / 2 : ℝ) • (X ω + Z ω)‖ ^ 2 ∂μ) =
      ((∫ ω, R ^ 2 - ‖X ω‖ ^ 2 ∂μ) +
        (∫ ω, R ^ 2 - ‖Z ω‖ ^ 2 ∂μ)) / 2 +
      (∫ ω, ‖X ω - Z ω‖ ^ 2 ∂μ) / 4 := by
  simp_rw [quadratic_midpoint_identity]
  have hXZ : Integrable (fun ω =>
      ((R ^ 2 - ‖X ω‖ ^ 2) + (R ^ 2 - ‖Z ω‖ ^ 2)) / 2) μ := by
    simpa only [Pi.add_apply] using (hX.add hZ).div_const 2
  rw [integral_add hXZ (hD.div_const 4), integral_div, integral_add hX hZ, integral_div]

/-- Actual dominated midpoint laws and endpoint measure partitions supply the
aggregate scalar balance used by `midpoint_aggregate_transport`. -/
theorem midpoint_partition_balance
    {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (ρ : Measure X) (cell minus plus mid : ι → Measure X)
    (α β γ D : ι → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i) (hγ : ∀ i, 0 ≤ γ i)
    (hcells : (∑ i, cell i) = ρ)
    (hminus : (∑ i, ENNReal.ofReal (α i) • minus i) = ρ)
    (hplus : (∑ i, ENNReal.ofReal (β i) • plus i) = ρ)
    (hdom : ∀ i, ENNReal.ofReal (γ i) • mid i ≤ cell i)
    (f : X → ℝ) (hf : Integrable f ρ) (hfn : 0 ≤ᵐ[ρ] f)
    (hmid : ∀ i, (∫ x, f x ∂mid i) =
      ((∫ x, f x ∂minus i) + (∫ x, f x ∂plus i)) / 2 + D i / 4) :
    (∑ i, γ i * (((∫ x, f x ∂minus i) + (∫ x, f x ∂plus i)) / 2 + D i / 4)) ≤
      ∑ i, (α i * (∫ x, f x ∂minus i) + β i * (∫ x, f x ∂plus i)) / 2 := by
  have hm := integral_eq_weighted_sum_of_measure_partition ρ minus α hα hminus f hf
  have hp := integral_eq_weighted_sum_of_measure_partition ρ plus β hβ hplus f hf
  calc
    _ = ∑ i, γ i * ∫ x, f x ∂mid i := by simp_rw [hmid]
    _ ≤ ∫ x, f x ∂ρ :=
      weighted_integral_sum_le_of_measure_domination ρ cell mid γ hγ hcells hdom f hf hfn
    _ = ((∑ i, α i * ∫ x, f x ∂minus i) +
        (∑ i, β i * ∫ x, f x ∂plus i)) / 2 := by rw [← hm, ← hp]; ring
    _ = _ := by rw [← Finset.sum_add_distrib, Finset.sum_div]

end Problem358

end

/-!+# Transfer of midpoint couplings from coordinates to Euclidean space

The construction of a coordinate coupling remains an explicit hypothesis.
The volume-preserving change of representation includes
normalization and the midpoint domination inequality.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Problem358.MidpointCoordinates

abbrev Coordinates (d : ℕ) := Fin d → ℝ

def coordinateUniform {d : ℕ} (K : Set (E d)) : Measure (Coordinates d) :=
  (volume ((WithLp.toLp 2) ⁻¹' K))⁻¹ •
    volume.restrict ((WithLp.toLp 2) ⁻¹' K)

lemma volume_preimage_toLp {d : ℕ} {K : Set (E d)} (hK : MeasurableSet K) :
    volume ((WithLp.toLp 2) ⁻¹' K) = volume K :=
  (PiLp.volume_preserving_toLp (Fin d)).measure_preimage hK.nullMeasurableSet

/-- The ordinary coordinate-space normalization maps to the exact source used
in the challenge, with no additional volume constants. -/
lemma map_coordinateUniform {d : ℕ} {K : Set (E d)} (hK : MeasurableSet K) :
    Measure.map (WithLp.toLp 2) (coordinateUniform K) = uniformMeasure K := by
  unfold coordinateUniform uniformMeasure
  rw [volume_preimage_toLp hK,
    Measure.map_smul _ (PiLp.volume_preserving_toLp (Fin d)).measurable.aemeasurable,
    ← Measure.restrict_map (PiLp.volume_preserving_toLp (Fin d)).measurable hK,
    (PiLp.volume_preserving_toLp (Fin d)).map_eq]

def liftPair {d : ℕ} (p : Coordinates d × Coordinates d) : E d × E d :=
  (WithLp.toLp 2 p.1, WithLp.toLp 2 p.2)

lemma measurable_liftPair (d : ℕ) : Measurable (@liftPair d) :=
  ((PiLp.volume_preserving_toLp (Fin d)).measurable.comp measurable_fst).prodMk
    ((PiLp.volume_preserving_toLp (Fin d)).measurable.comp measurable_snd)

lemma liftPair_midpoint {d : ℕ} (p : Coordinates d × Coordinates d) :
    (1 / 2 : ℝ) • ((liftPair p).1 + (liftPair p).2) =
      WithLp.toLp 2 ((1 / 2 : ℝ) • (p.1 + p.2)) := by
  simp only [liftPair, WithLp.toLp_smul, WithLp.toLp_add]

/-- Pushing both coordinates through `toLp` preserves both exact marginals. -/
lemma lift_coupling {d : ℕ} {K L : Set (E d)}
    (hK : MeasurableSet K) (hL : MeasurableSet L)
    {π : Measure (Coordinates d × Coordinates d)}
    (hπ : IsProbabilityMeasure π)
    (hfst : Measure.map Prod.fst π = coordinateUniform K)
    (hsnd : Measure.map Prod.snd π = coordinateUniform L) :
    IsCoupling (uniformMeasure K) (uniformMeasure L) (Measure.map liftPair π) := by
  let := hπ
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst (measurable_liftPair d)]
    change Measure.map ((WithLp.toLp 2) ∘ Prod.fst) π = uniformMeasure K
    rw [← Measure.map_map (PiLp.volume_preserving_toLp (Fin d)).measurable
      measurable_fst, hfst, map_coordinateUniform hK]
  · rw [Measure.map_map measurable_snd (measurable_liftPair d)]
    change Measure.map ((WithLp.toLp 2) ∘ Prod.snd) π = uniformMeasure L
    rw [← Measure.map_map (PiLp.volume_preserving_toLp (Fin d)).measurable
      measurable_snd, hsnd, map_coordinateUniform hL]

/-- A weighted midpoint domination inequality survives the coordinate change. -/
lemma lift_midpoint_domination {d : ℕ}
    {π : Measure (Coordinates d × Coordinates d)} {c : ℝ≥0∞}
    (hdom : c • Measure.map
      (fun p : Coordinates d × Coordinates d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤
        volume) :
    c • Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2))
      (Measure.map liftPair π) ≤ volume := by
  have h := Measure.map_mono hdom (PiLp.volume_preserving_toLp (Fin d)).measurable
  rw [Measure.map_smul _ (PiLp.volume_preserving_toLp (Fin d)).measurable.aemeasurable,
    Measure.map_map
    (PiLp.volume_preserving_toLp (Fin d)).measurable (by fun_prop),
    (PiLp.volume_preserving_toLp (Fin d)).map_eq] at h
  rw [Measure.map_map (by fun_prop) (measurable_liftPair d)]
  have hfun : (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) ∘ liftPair =
      (WithLp.toLp 2) ∘
        (fun p : Coordinates d × Coordinates d => (1 / 2 : ℝ) • (p.1 + p.2)) := by
    funext p
    exact liftPair_midpoint p
  rw [hfun]
  exact h

/-- Coordinate-space dominated midpoint witnesses give the corresponding
Euclidean-space witnesses. No existence assumption is hidden in the change
of representation. -/
theorem exists_lifted_midpoint_coupling {d : ℕ} {K L : Set (E d)}
    (hK : MeasurableSet K) (hL : MeasurableSet L) (c : ℝ≥0∞)
    (h : ∃ π : Measure (Coordinates d × Coordinates d), IsProbabilityMeasure π ∧
      Measure.map Prod.fst π = coordinateUniform K ∧
      Measure.map Prod.snd π = coordinateUniform L ∧
      c • Measure.map
        (fun p : Coordinates d × Coordinates d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤
        volume) :
    ∃ π : Measure (E d × E d), IsCoupling (uniformMeasure K) (uniformMeasure L) π ∧
      c • Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume := by
  obtain ⟨π, hπ, hfst, hsnd, hdom⟩ := h
  exact ⟨Measure.map liftPair π, lift_coupling hK hL hπ hfst hsnd,
    lift_midpoint_domination hdom⟩

/-- Passing to the interior of a convex body does not change its volume. -/
lemma volume_interior {d : ℕ} {K : Set (E d)} (hK : Convex ℝ K) :
    volume (interior K) = volume K :=
  measure_congr (interior_ae_eq_of_null_frontier (hK.addHaar_frontier volume))

/-- The normalized law is also unchanged, including degenerate convex sets. -/
lemma uniformMeasure_interior {d : ℕ} {K : Set (E d)} (hK : Convex ℝ K) :
    uniformMeasure (interior K) = uniformMeasure K := by
  unfold uniformMeasure
  rw [volume_interior hK, Measure.restrict_congr_set
    (interior_ae_eq_of_null_frontier (hK.addHaar_frontier volume))]

/-- A construction using open convex interiors in ordinary coordinates supplies
the exact closed-body laws required by the Euclidean midpoint argument. -/
theorem exists_lifted_midpoint_coupling_of_interiors {d : ℕ} {K L : Set (E d)}
    (hK : Convex ℝ K) (hL : Convex ℝ L) (c : ℝ≥0∞)
    (h : ∃ π : Measure (Coordinates d × Coordinates d), IsProbabilityMeasure π ∧
      Measure.map Prod.fst π = coordinateUniform (interior K) ∧
      Measure.map Prod.snd π = coordinateUniform (interior L) ∧
      c • Measure.map
        (fun p : Coordinates d × Coordinates d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤
        volume) :
    ∃ π : Measure (E d × E d), IsCoupling (uniformMeasure K) (uniformMeasure L) π ∧
      c • Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume := by
  simpa only [uniformMeasure_interior hK, uniformMeasure_interior hL] using
    exists_lifted_midpoint_coupling measurableSet_interior measurableSet_interior c h

/-- The common-source sampler formulation constructs the joint coupling rather
than requiring it as a separate input. -/
theorem exists_midpoint_coupling_of_coordinate_samplers
    {Ω : Type*} [MeasurableSpace Ω] {ρ : Measure Ω} [IsProbabilityMeasure ρ]
    {d : ℕ} {K L : Set (E d)} (hK : MeasurableSet K) (hL : MeasurableSet L)
    (X Y : Ω → Coordinates d) (hX : Measurable X) (hY : Measurable Y)
    (hXlaw : Measure.map X ρ = coordinateUniform K)
    (hYlaw : Measure.map Y ρ = coordinateUniform L) (c : ℝ≥0∞)
    (hdom : c • Measure.map (fun ω => (1 / 2 : ℝ) • (X ω + Y ω)) ρ ≤ volume) :
    ∃ π : Measure (E d × E d), IsCoupling (uniformMeasure K) (uniformMeasure L) π ∧
      c • Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume := by
  apply exists_lifted_midpoint_coupling hK hL c
  refine ⟨Measure.map (fun ω => (X ω, Y ω)) ρ,
    inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst (hX.prodMk hY)]
    exact hXlaw
  · rw [Measure.map_map measurable_snd (hX.prodMk hY)]
    exact hYlaw
  · rw [Measure.map_map (by fun_prop) (hX.prodMk hY)]
    exact hdom

/-- Open-interior coordinate samplers suffice for the exact original body laws. -/
theorem exists_midpoint_coupling_of_interior_coordinate_samplers
    {Ω : Type*} [MeasurableSpace Ω] {ρ : Measure Ω} [IsProbabilityMeasure ρ]
    {d : ℕ} {K L : Set (E d)} (hK : Convex ℝ K) (hL : Convex ℝ L)
    (X Y : Ω → Coordinates d) (hX : Measurable X) (hY : Measurable Y)
    (hXlaw : Measure.map X ρ = coordinateUniform (interior K))
    (hYlaw : Measure.map Y ρ = coordinateUniform (interior L)) (c : ℝ≥0∞)
    (hdom : c • Measure.map (fun ω => (1 / 2 : ℝ) • (X ω + Y ω)) ρ ≤ volume) :
    ∃ π : Measure (E d × E d), IsCoupling (uniformMeasure K) (uniformMeasure L) π ∧
      c • Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume := by
  simpa only [uniformMeasure_interior hK, uniformMeasure_interior hL] using
    exists_midpoint_coupling_of_coordinate_samplers measurableSet_interior measurableSet_interior
      X Y hX hY hXlaw hYlaw c hdom

end Problem358.MidpointCoordinates

end

end OAI
