import OAI.Analysis.PlaneSpectrum.Characters
import OAI.Analysis.PlaneSpectrum.InvariantMean

namespace OAI

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
namespace PlaneFiveColor.LpMultiplier
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma mul_memLp (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) (v : Lp ℂ 2 μ) :
    MemLp (fun x => h x * v x) 2 μ := by
  apply (Lp.memLp v).of_le (hm.mul (Lp.aestronglyMeasurable v))
  exact Eventually.of_forall (fun x => by simp [hn])

def mul (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) (v : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (mul_memLp h hm hn v).toLp _

lemma mul_ae (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) (v : Lp ℂ 2 μ) :
    mul h hm hn v =ᵐ[μ] (fun x => h x * v x) := MemLp.coeFn_toLp _

lemma mul_norm (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) (v : Lp ℂ 2 μ) :
    ‖mul h hm hn v‖ = ‖v‖ := by
  simp only [Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable (mul h hm hn v))
    (Lp.aestronglyMeasurable v)
  filter_upwards [mul_ae h hm hn v] with x hx
  simp [hx, hn]

def mulIsometry (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) : Lp ℂ 2 μ →ₗᵢ[ℝ] Lp ℂ 2 μ where
  toFun := mul h hm hn
  map_add' v w := by
    apply Lp.ext
    filter_upwards [mul_ae h hm hn (v+w), mul_ae h hm hn v, mul_ae h hm hn w,
      Lp.coeFn_add v w, Lp.coeFn_add (mul h hm hn v) (mul h hm hn w)] with x ha hb hc hd he
    simp only [ha, hd, he, Pi.add_apply, hb, hc, mul_add]
  map_smul' r v := by
    apply Lp.ext
    filter_upwards [mul_ae h hm hn (r • v), mul_ae h hm hn v,
      Lp.coeFn_smul r v, Lp.coeFn_smul r (mul h hm hn v)] with x ha hb hc hd
    simp only [ha, hc, hd, Pi.smul_apply, hb, RingHom.id_apply, mul_smul_comm]
  norm_map' := mul_norm h hm hn

lemma mul_inverse (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) (v : Lp ℂ 2 μ) :
    mul h hm hn (mul (fun x => conj (h x)) (continuous_star.comp_aestronglyMeasurable hm) (fun x => by simp [hn]) v) = v := by
  apply Lp.ext
  filter_upwards [mul_ae h hm hn (mul (fun x => conj (h x)) (continuous_star.comp_aestronglyMeasurable hm) (fun x => by simp [hn]) v),
    mul_ae (fun x => conj (h x)) (continuous_star.comp_aestronglyMeasurable hm) (fun x => by simp [hn]) v] with x hx hy
  rw [hx, hy, ← mul_assoc]
  have hh : h x * conj (h x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    norm_num
  rw [hh, one_mul]

def mulEquiv (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) : Lp ℂ 2 μ ≃ₗᵢ[ℝ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofSurjective (mulIsometry h hm hn) (fun v =>
    ⟨mul (fun x => conj (h x)) (continuous_star.comp_aestronglyMeasurable hm) (fun x => by simp [hn]) v, mul_inverse h hm hn v⟩)

/-- Spectral weighting by a Hilbert vector, exactly |v|² μ. -/
def weight (v : Lp ℂ 2 μ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (‖v x‖^2))

lemma weight_measurable (v : Lp ℂ 2 μ) :
    AEMeasurable (fun x => ENNReal.ofReal (‖v x‖^2)) μ :=
  ((Lp.aestronglyMeasurable v).norm.pow 2).aemeasurable.ennreal_ofReal

instance weight_finite (v : Lp ℂ 2 μ) : IsFiniteMeasure (weight v) := by
  apply isFiniteMeasure_withDensity
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((Lp.aestronglyMeasurable v).norm.pow 2) (Eventually.of_forall (fun x => sq_nonneg ‖v x‖))).mpr
  exact (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)

lemma weight_ac (v : Lp ℂ 2 μ) : weight v ≪ μ :=
  withDensity_absolutelyContinuous _ _

lemma weight_inner (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) (v : Lp ℂ 2 μ) :
    (∫ x, h x ∂weight v) = inner ℂ v (mul h hm hn v) := by
  rw [weight, integral_withDensity_eq_integral_toReal_smul₀ (weight_measurable v)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [mul_ae h hm hn v] with x hx
  rw [hx, ENNReal.toReal_ofReal (sq_nonneg _)]
  simp only [RCLike.inner_apply, Complex.real_smul]
  rw [← Complex.normSq_eq_norm_sq]
  have hh := Complex.mul_conj (v x)
  calc
    _ = (v x * conj (v x)) * h x := by rw [hh]
    _ = _ := by ring

lemma weight_eq_zero_iff (v : Lp ℂ 2 μ) : weight v = 0 ↔ v = 0 := by
  constructor
  · intro hz
    have he := (withDensity_eq_zero_iff (weight_measurable v)).mp hz
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [he] with x hx
    have hsq : ‖v x‖^2 = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (sq_nonneg _)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · intro hv
    apply (withDensity_eq_zero_iff (weight_measurable v)).mpr
    filter_upwards [Lp.eq_zero_iff_ae_eq_zero.mp hv] with x hx
    simp [hx]

lemma norm_mul_sub_sq (z w : ℂ) (hz : ‖z‖ = 1) :
    ‖z*w-w‖^2 = 2 * (‖w‖^2 * (1-z.re)) := by
  have he := Complex.normSq_sub z 1
  simp only [Complex.normSq_eq_norm_sq, hz, one_pow, map_one, mul_one] at he
  rw [show z*w-w = (z-1)*w by ring, norm_mul, mul_pow, he]
  ring

lemma lp_norm_sq_integral (v : Lp ℂ 2 μ) :
    (∫ x, ‖v x‖^2 ∂μ) = ‖v‖^2 := by
  have he := L2.inner_def (𝕜 := ℝ) v v
  simpa only [real_inner_self_eq_norm_sq] using he.symm

lemma weight_deviation (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) (v : Lp ℂ 2 μ) :
    (∫ x, 1-(h x).re ∂weight v) = ‖mul h hm hn v - v‖^2 / 2 := by
  rw [weight, integral_withDensity_eq_integral_toReal_smul₀ (weight_measurable v)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  calc
    _ = ∫ x, ‖(mul h hm hn v-v) x‖^2 /2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [mul_ae h hm hn v, Lp.coeFn_sub (mul h hm hn v) v] with x hx hy
      rw [hy, Pi.sub_apply, hx, norm_mul_sub_sq _ _ (hn x),
        ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
      ring
    _ = _ := by rw [integral_div, lp_norm_sq_integral]

end PlaneFiveColor.LpMultiplier

namespace PlaneFiveColor.Spectral
open MeasureTheory Filter Topology
open scoped ENNReal

def lineU (ν : Measure D) (a : E) (t : F) : Lp ℂ 2 ν ≃ₗᵢ[ℝ] Lp ℂ 2 ν :=
  LpMultiplier.mulEquiv (fun d => (lineCharacter a d (Multiplicative.ofAdd t) : ℂ))
    (lineCharacter_measurable a t).aestronglyMeasurable (fun _ => Circle.norm_coe _)

lemma lineU_apply (ν : Measure D) (a : E) (t : F) (v : Lp ℂ 2 ν) :
    lineU ν a t v = LpMultiplier.mul
      (fun d => (lineCharacter a d (Multiplicative.ofAdd t) : ℂ))
      (lineCharacter_measurable a t).aestronglyMeasurable (fun _ => Circle.norm_coe _) v := rfl

lemma lineU_ae (ν : Measure D) (a : E) (t : F) (v : Lp ℂ 2 ν) :
    lineU ν a t v =ᵐ[ν] (fun d => (lineCharacter a d (Multiplicative.ofAdd t) : ℂ) * v d) :=
  LpMultiplier.mul_ae _ (lineCharacter_measurable a t).aestronglyMeasurable
    (fun _ => Circle.norm_coe _) v

lemma lineU_add (ν : Measure D) (a : E) (s t : F) (v : Lp ℂ 2 ν) :
    lineU ν a s (lineU ν a t v) = lineU ν a (s+t) v := by
  apply Lp.ext
  filter_upwards [lineU_ae ν a s (lineU ν a t v), lineU_ae ν a t v,
    lineU_ae ν a (s+t) v] with d hs ht hst
  rw [hs, ht, hst]
  have he := congrArg (fun z : Circle => (z : ℂ))
    ((lineCharacter a d).map_mul (Multiplicative.ofAdd s) (Multiplicative.ofAdd t))
  change (lineCharacter a d (Multiplicative.ofAdd (s+t)) : ℂ) =
    (lineCharacter a d (Multiplicative.ofAdd s) : ℂ) *
      (lineCharacter a d (Multiplicative.ofAdd t) : ℂ) at he
  rw [he, mul_assoc]

lemma lineU_zero (ν : Measure D) (a : E) (v : Lp ℂ 2 ν) : lineU ν a 0 v = v := by
  apply Lp.ext
  filter_upwards [lineU_ae ν a 0 v] with d hd
  simpa using hd

lemma weighted_coeff (ν : Measure D) (a : E) (v : Lp ℂ 2 ν) (t : F) :
    ContinuousCharacters.coeff (LpMultiplier.weight v) (lineCharacter a) t =
      ‖lineU ν a t v-v‖^2/2 := by
  rw [lineU_apply]
  simpa only [ContinuousCharacters.coeff, ContinuousCharacters.deviation, pow_one]
    using LpMultiplier.weight_deviation
      (fun d => (lineCharacter a d (Multiplicative.ofAdd t) : ℂ))
      (lineCharacter_measurable a t).aestronglyMeasurable (fun _ => Circle.norm_coe _) v

/-- A wild law has no nonzero strongly continuous vector for any nonzero
algebraic line. The arbitrary L² vector is handled by its actual |v|² weight. -/
theorem strong_vector_zero (ν : Measure D) [IsProbabilityMeasure ν]
    (hν : IsWild ν) {a : E} (ha : a ≠ 0) (v : Lp ℂ 2 ν)
    (hc : Tendsto (fun t => lineU ν a t v) (𝓝 0) (𝓝 v)) : v = 0 := by
  have hcoef : ContinuousAt
      (ContinuousCharacters.coeff (LpMultiplier.weight v) (lineCharacter a)) 0 := by
    have he : ContinuousCharacters.coeff (LpMultiplier.weight v) (lineCharacter a) =
        fun t => ‖lineU ν a t v-v‖^2/2 := funext (weighted_coeff ν a v)
    rw [he]
    change Tendsto _ (𝓝 0) (𝓝 (_ / 2))
    have hh := ((hc.sub (tendsto_const_nhds (x := v))).norm.pow 2).div_const 2
    simpa only [lineU_zero, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div]
      using hh
  exact (LpMultiplier.weight_eq_zero_iff v).mp
    (wild_continuous_coefficient_zero ν (LpMultiplier.weight v) hν
      (LpMultiplier.weight_ac v) ha hcoef)

/-- Every ordinary compact window has zero weak vector average along a
nonzero algebraic line of a wild law. -/
theorem wild_smoothed_zero (ν : Measure D) [IsProbabilityMeasure ν]
    (hν : IsWild ν) {a : E} (ha : a ≠ 0)
    (φ : ℝ → ℝ) (hc : UniformContinuous φ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) (v : Lp ℂ 2 ν) :
    InvariantMean.smoothedVector (lineU ν a) (fun t => φ t)
      (fun t ht => hs t ht) (fun t => hb t) v = 0 := by
  apply strong_vector_zero ν hν ha
  exact InvariantMean.smoothed_tendsto (lineU ν a) (lineU_add ν a) φ hc hs hb v

end PlaneFiveColor.Spectral

namespace PlaneFiveColor.InvariantMean
open MeasureTheory
lemma weakMean_complex {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [DiscreteTopology G] (V : G →ᵇ ℂ) : weakMean V = cmean V := by
  have hr := weakMean_pair V (1 : ℂ)
  have hi := weakMean_pair V Complex.I
  have hpr : pairing V (1 : ℂ) = realPart V := by
    ext x
    simp [pairing_apply, real_inner_eq_re_inner ℂ, RCLike.inner_apply]
  have hpi : pairing V Complex.I = imagPart V := by
    ext x
    simp [pairing_apply, real_inner_eq_re_inner ℂ, RCLike.inner_apply]
  rw [hpr] at hr
  rw [hpi] at hi
  apply Complex.ext <;>
    simp_all [real_inner_eq_re_inner ℂ, RCLike.inner_apply, cmean]

lemma weakIntegral_complex (h : AF → ℂ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) : weakIntegral h hs hb = integralComplex h hs hb :=
  weakMean_complex _
end PlaneFiveColor.InvariantMean

namespace PlaneFiveColor.Spectral
open MeasureTheory Filter Topology
open scoped ENNReal

def lineFourier (ν : Measure D) (a : E) (t : F) : ℂ :=
  ∫ d, (lineCharacter a d (Multiplicative.ofAdd t) : ℂ) ∂ν

lemma lineFourier_norm_le (ν : Measure D) [IsProbabilityMeasure ν] (a : E) (t : F) :
    ‖lineFourier ν a t‖ ≤ 1 := by
  simpa [lineFourier] using (norm_integral_le_of_norm_le_const (μ := ν)
    (C := (1 : ℝ)) (Eventually.of_forall (fun d => (Circle.norm_coe
      (lineCharacter a d (Multiplicative.ofAdd t))).le)))

lemma lineFourier_inner (ν : Measure D) [IsProbabilityMeasure ν] (a : E) (t : F) :
    inner ℂ (Lp.const 2 ν (1 : ℂ)) (lineU ν a t (Lp.const 2 ν (1 : ℂ))) =
      lineFourier ν a t := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [lineU_ae ν a t (Lp.const 2 ν (1 : ℂ)),
    Lp.coeFn_const (2 : ℝ≥0∞) ν (1 : ℂ)] with d hu hc
  simp [hu, RCLike.inner_apply]

/-- The invariant scalar Fourier average on a nonzero algebraic line vanishes
for every real ordinary compact window; no measurability of t ↦ fν(at). -/
theorem wild_line_average_zero (ν : Measure D) [IsProbabilityMeasure ν]
    (hν : IsWild ν) {a : E} (ha : a ≠ 0)
    (φ : ℝ → ℝ) (hc : UniformContinuous φ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) :
    InvariantMean.integralComplex
      (fun t : F => (φ t : ℂ) * lineFourier ν a t)
      (fun t ht => by rw [hs t ht, Complex.ofReal_zero, zero_mul])
      (fun t => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact (mul_le_of_le_one_right (abs_nonneg _) (lineFourier_norm_le ν a t)).trans (hb t)) = 0 := by
  let v := Lp.const 2 ν (1 : ℂ)
  let L : Lp ℂ 2 ν →L[ℝ] ℂ := (innerSL ℂ v).restrictScalars ℝ
  have he (t : F) : L (φ t • lineU ν a t v) = (φ t : ℂ) * lineFourier ν a t := by
    rw [map_smul]
    change φ t • inner ℂ v (lineU ν a t v) = _
    rw [lineFourier_inner]
    rfl
  have hjs : ∀ t : F, (N : ℝ) < |(t : ℝ)| → L (φ t • lineU ν a t v) = 0 := by
    intro t ht
    rw [he, hs t ht, Complex.ofReal_zero, zero_mul]
  have hjb : ∀ t : F, ‖L (φ t • lineU ν a t v)‖ ≤ B := by
    intro t
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) (lineFourier_norm_le ν a t)).trans (hb t)
  have hm := InvariantMean.weakIntegral_map L
    (fun t : F => φ t • lineU ν a t v)
    (InvariantMean.smoothed_support (lineU ν a) (fun t => φ t) (fun t ht => hs t ht) v)
    (InvariantMean.smoothed_bound (lineU ν a) (fun t => φ t) (fun t => hb t) v)
    hjs hjb
  change InvariantMean.weakIntegral _ _ _ = L (InvariantMean.smoothedVector
    (lineU ν a) (fun t : F => φ t) (fun t ht => hs t ht) (fun t => hb t) v) at hm
  rw [wild_smoothed_zero ν hν ha φ hc hs hb v, map_zero] at hm
  rw [← InvariantMean.weakIntegral_complex]
  exact (InvariantMean.weakIntegral_congr _ _ _ _ hjs hjb (fun t => (he t).symm)).trans hm

end PlaneFiveColor.Spectral
end
end
end
end

end OAI
