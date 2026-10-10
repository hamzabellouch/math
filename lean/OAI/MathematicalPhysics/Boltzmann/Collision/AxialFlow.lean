import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

section

/-!
# The monotone implicit axial flow

The cold jet profile in Section 4 of the supplied manuscript is
`σ + α * tanh (γ * z / s)`. Its characteristic map is expanding,
giving a unique implicit velocity at every nonnegative time. The proof uses
continuity, the intermediate value theorem, and monotonicity. No differentiability or
unproved kinetic estimate is assumed.
-/

noncomputable section

open Set Function

namespace BoltzmannNonuniqueness.AxialFlow

/-- The initial axial velocity at scale `s`. -/
def profile (σ α γ s z : ℝ) : ℝ := σ + α * Real.tanh (γ * z / s)

/-- The spatial position at time `t` of a characteristic starting from `z`. -/
def characteristic (σ α γ s t z : ℝ) : ℝ := z + t * profile σ α γ s z

/-- The residual of the implicit velocity equation at the proposed velocity `u`. -/
def residual (σ α γ s t z u : ℝ) : ℝ :=
  u - profile σ α γ s (z - t * u)

private theorem tanh_monotone : Monotone Real.tanh := by
  intro x y hxy
  apply (Real.artanh_le_artanh_iff
    ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩
    ⟨Real.neg_one_lt_tanh y, Real.tanh_lt_one y⟩).mp
  simpa only [Real.artanh_tanh] using hxy

private theorem tanh_continuous : Continuous Real.tanh := by
  change Continuous (fun z : ℝ => Real.tanh z)
  simp_rw [Real.tanh_eq_sinh_div_cosh]
  exact Real.continuous_sinh.div Real.continuous_cosh (fun z => (Real.cosh_pos z).ne')

theorem continuous_profile (σ α γ s : ℝ) : Continuous (profile σ α γ s) := by
  unfold profile
  exact continuous_const.add (continuous_const.mul
    (tanh_continuous.comp ((continuous_const.mul continuous_id).div_const s)))

theorem profile_monotone {σ α γ s : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) :
    Monotone (profile σ α γ s) := by
  intro x y hxy
  have h := tanh_monotone
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxy hγ) hs.le)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h hα)

theorem profile_sub_center_le {σ α γ s z : ℝ} (hα : 0 ≤ α) :
    |profile σ α γ s z - σ| ≤ α := by
  simp only [profile, add_sub_cancel_left, abs_mul, abs_of_nonneg hα]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (Real.abs_tanh_lt_one (γ * z / s)).le hα

theorem continuous_residual (σ α γ s t z : ℝ) : Continuous (residual σ α γ s t z) := by
  unfold residual
  exact continuous_id.sub ((continuous_profile σ α γ s).comp
    (continuous_const.sub (continuous_const.mul continuous_id)))

/-- The characteristic map expands ordered distances by at least one. -/
theorem characteristic_sub_ge {σ α γ s t x y : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) (hxy : x ≤ y) :
    y - x ≤ characteristic σ α γ s t y - characteristic σ α γ s t x := by
  have hp := profile_monotone (σ := σ) hα hγ hs hxy
  have hp' := mul_le_mul_of_nonneg_left hp ht
  dsimp only [characteristic]
  linarith

theorem characteristic_strictMono {σ α γ s t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    StrictMono (characteristic σ α γ s t) := by
  intro x y hxy
  have h := characteristic_sub_ge (σ := σ) hα hγ hs ht hxy.le
  linarith

/-- The scalar residual expands ordered velocity differences by at least one. -/
theorem residual_sub_ge {σ α γ s t z u v : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) (huv : u ≤ v) :
    v - u ≤ residual σ α γ s t z v - residual σ α γ s t z u := by
  have hp := profile_monotone (σ := σ) hα hγ hs
    (show z - t * v ≤ z - t * u by nlinarith)
  dsimp only [residual]
  linarith

theorem residual_strictMono {σ α γ s t z : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    StrictMono (residual σ α γ s t z) := by
  intro u v huv
  have h := residual_sub_ge (σ := σ) (z := z) hα hγ hs ht huv.le
  linarith

/-- The implicit equation has a root between the two extremal axial speeds, even without a
sign restriction on time. Nonnegative time will be used for uniqueness. -/
theorem exists_residual_zero {σ α γ s t z : ℝ} (hα : 0 ≤ α) :
    ∃ u ∈ Icc (σ - α) (σ + α), residual σ α γ s t z u = 0 := by
  have hl : residual σ α γ s t z (σ - α) ≤ 0 := by
    have h := mul_le_mul_of_nonneg_left
      (Real.neg_one_lt_tanh (γ * (z - t * (σ - α)) / s)).le hα
    dsimp only [residual, profile]
    linarith
  have hr : 0 ≤ residual σ α γ s t z (σ + α) := by
    have h := mul_le_mul_of_nonneg_left
      (Real.tanh_lt_one (γ * (z - t * (σ + α)) / s)).le hα
    dsimp only [residual, profile]
    linarith
  exact intermediate_value_Icc (by linarith : σ - α ≤ σ + α)
    (continuous_residual σ α γ s t z).continuousOn ⟨hl, hr⟩

theorem existsUnique_implicit_velocity {σ α γ s t z : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    ∃! u : ℝ, u = σ + α * Real.tanh (γ * (z - t * u) / s) := by
  obtain ⟨u, _, hu⟩ := exists_residual_zero (σ := σ) (γ := γ) (s := s)
    (t := t) (z := z) hα
  refine ⟨u, sub_eq_zero.mp hu, ?_⟩
  intro v hv
  apply (residual_strictMono hα hγ hs ht).injective
  exact (sub_eq_zero.mpr hv).trans hu.symm

/-- The implicit velocity selected by the inverse of the residual. Its defining equation and
uniqueness are proved below under the physical parameter restrictions. -/
def velocity (σ α γ s t z : ℝ) : ℝ := invFun (residual σ α γ s t z) 0

theorem velocity_spec {σ α γ s t z : ℝ} (hα : 0 ≤ α) :
    velocity σ α γ s t z = profile σ α γ s (z - t * velocity σ α γ s t z) := by
  obtain ⟨u, _, hu⟩ := exists_residual_zero (σ := σ) (γ := γ) (s := s)
    (t := t) (z := z) hα
  exact sub_eq_zero.mp (invFun_eq ⟨u, hu⟩)

theorem velocity_unique {σ α γ s t z u : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t)
    (hu : u = profile σ α γ s (z - t * u)) : u = velocity σ α γ s t z := by
  apply (residual_strictMono hα hγ hs ht).injective
  exact (sub_eq_zero.mpr hu).trans (sub_eq_zero.mpr (velocity_spec hα)).symm

theorem velocity_sub_center_le {σ α γ s t z : ℝ} (hα : 0 ≤ α) :
    |velocity σ α γ s t z - σ| ≤ α := by
  rw [velocity_spec hα]
  exact profile_sub_center_le hα

/-- The inverse characteristic map is 1-Lipschitz in the spatial coordinate. -/
theorem characteristic_inverse_lipschitz {σ α γ s t x y : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    |x - y| ≤ |characteristic σ α γ s t x - characteristic σ α γ s t y| := by
  rcases le_total x y with hxy | hyx
  · have hd := characteristic_sub_ge (σ := σ) hα hγ hs ht hxy
    have hf := (characteristic_strictMono (σ := σ) hα hγ hs ht).monotone hxy
    rw [abs_of_nonpos (sub_nonpos.mpr hxy), abs_of_nonpos (sub_nonpos.mpr hf)]
    linarith
  · have hd := characteristic_sub_ge (σ := σ) hα hγ hs ht hyx
    have hf := (characteristic_strictMono (σ := σ) hα hγ hs ht).monotone hyx
    rw [abs_of_nonneg (sub_nonneg.mpr hyx), abs_of_nonneg (sub_nonneg.mpr hf)]
    exact hd

/-- The inverse residual is 1-Lipschitz; this estimate does not require differentiation. -/
theorem residual_inverse_lipschitz {σ α γ s t z u v : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    |u - v| ≤ |residual σ α γ s t z u - residual σ α γ s t z v| := by
  rcases le_total u v with huv | hvu
  · have hd := residual_sub_ge (σ := σ) (z := z) hα hγ hs ht huv
    have hf := (residual_strictMono (σ := σ) (z := z) hα hγ hs ht).monotone huv
    rw [abs_of_nonpos (sub_nonpos.mpr huv), abs_of_nonpos (sub_nonpos.mpr hf)]
    linarith
  · have hd := residual_sub_ge (σ := σ) (z := z) hα hγ hs ht hvu
    have hf := (residual_strictMono (σ := σ) (z := z) hα hγ hs ht).monotone hvu
    rw [abs_of_nonneg (sub_nonneg.mpr hvu), abs_of_nonneg (sub_nonneg.mpr hf)]
    exact hd

/-- A thermal perturbation of the implicit equation perturbs the velocity by at most its
amplitude. This is the compressed axial velocity estimate used for cold cores. -/
theorem thermal_velocity_error {σ α γ s t z p δ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t)
    (hp : p = profile σ α γ s (z - t * p) + δ) :
    |p - velocity σ α γ s t z| ≤ |δ| := by
  have h := residual_inverse_lipschitz (σ := σ) (z := z)
    (u := p) (v := velocity σ α γ s t z)
    hα hγ hs ht
  have hp' : residual σ α γ s t z p = δ := by
    dsimp only [residual]
    linarith
  have hu' : residual σ α γ s t z (velocity σ α γ s t z) = 0 :=
    sub_eq_zero.mpr (velocity_spec hα)
  simpa only [hp', hu', sub_zero] using h

/-- The initial spatial coordinate of the characteristic passing through `(t,z)`. -/
def foot (σ α γ s t z : ℝ) : ℝ := z - t * velocity σ α γ s t z

theorem characteristic_foot {σ α γ s t z : ℝ} (hα : 0 ≤ α) :
    characteristic σ α γ s t (foot σ α γ s t z) = z := by
  have hu := velocity_spec (σ := σ) (γ := γ) (s := s) (t := t) (z := z) hα
  dsimp only [characteristic, foot]
  rw [← hu]
  ring

theorem foot_characteristic {σ α γ s t z : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    foot σ α γ s t (characteristic σ α γ s t z) = z := by
  apply (characteristic_strictMono hα hγ hs ht).injective
  exact characteristic_foot hα

theorem characteristic_bijective {σ α γ s t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    Bijective (characteristic σ α γ s t) := by
  refine ⟨(characteristic_strictMono hα hγ hs ht).injective, ?_⟩
  intro z
  exact ⟨foot σ α γ s t z, characteristic_foot hα⟩

/-- Spatial separation does not increase when characteristics are traced backwards. -/
theorem foot_lipschitz {σ α γ s t z w : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    |foot σ α γ s t z - foot σ α γ s t w| ≤ |z - w| := by
  have h := characteristic_inverse_lipschitz (σ := σ) (x := foot σ α γ s t z)
    (y := foot σ α γ s t w) hα hγ hs ht
  simpa only [characteristic_foot hα] using h

theorem foot_lipschitzWith {σ α γ s t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    LipschitzWith 1 (foot σ α γ s t) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
    (foot_lipschitz (σ := σ) (z := z) (w := w) hα hγ hs ht)

theorem continuous_velocity {σ α γ s t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    Continuous (velocity σ α γ s t) := by
  have hEq : velocity σ α γ s t = fun z => profile σ α γ s (foot σ α γ s t z) :=
    funext fun _ => velocity_spec hα
  rw [hEq]
  exact (continuous_profile σ α γ s).comp (foot_lipschitzWith hα hγ hs ht).continuous

/-- A particle launched with thermal velocity error `δ` stays within `t * |δ|` in the inverse
spatial coordinate. This is the axial-distance estimate in the transported cold-core barrier. -/
theorem free_flight_foot_error {σ α γ s t z δ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    |foot σ α γ s t (z + t * (profile σ α γ s z + δ)) - z| ≤ t * |δ| := by
  calc
    _ = |foot σ α γ s t (z + t * (profile σ α γ s z + δ)) -
        foot σ α γ s t (characteristic σ α γ s t z)| := by
          rw [foot_characteristic hα hγ hs ht]
    _ ≤ |z + t * (profile σ α γ s z + δ) - characteristic σ α γ s t z| :=
      foot_lipschitz hα hγ hs ht
    _ = |t * δ| := by congr 1; dsimp only [characteristic]; ring
    _ = t * |δ| := by rw [abs_mul, abs_of_nonneg ht]

theorem foot_monotone {σ α γ s t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    Monotone (foot σ α γ s t) := by
  intro z w hzw
  apply (characteristic_strictMono (σ := σ) hα hγ hs ht).le_iff_le.mp
  simpa only [characteristic_foot hα] using hzw

theorem velocity_monotone {σ α γ s t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    Monotone (velocity σ α γ s t) := by
  intro z w hzw
  calc
    velocity σ α γ s t z = profile σ α γ s (foot σ α γ s t z) := velocity_spec hα
    _ ≤ profile σ α γ s (foot σ α γ s t w) :=
      profile_monotone hα hγ hs (foot_monotone hα hγ hs ht hzw)
    _ = velocity σ α γ s t w := (velocity_spec hα).symm

/-- The implicit velocity is constant on its own characteristic, including when it is traced
backwards to an earlier nonnegative time. -/
theorem velocity_on_characteristic {σ α γ s t₁ t₂ z : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht₂ : 0 ≤ t₂) :
    velocity σ α γ s t₂
      (z - (t₁ - t₂) * velocity σ α γ s t₁ z) = velocity σ α γ s t₁ z := by
  symm
  apply velocity_unique hα hγ hs ht₂
  have hfoot : z - (t₁ - t₂) * velocity σ α γ s t₁ z -
      t₂ * velocity σ α γ s t₁ z = z - t₁ * velocity σ α γ s t₁ z := by ring
  rw [hfoot]
  exact velocity_spec hα

/-- Characteristic matching, the inequality in Section 8: tracing with an arbitrary speed
cannot reduce its discrepancy from the earlier cold-flow velocity. -/
theorem characteristic_matching {σ α γ s t₁ t₂ z w : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht₂ : 0 ≤ t₂) (ht : t₂ ≤ t₁) :
    |w - velocity σ α γ s t₁ z| ≤
      |w - velocity σ α γ s t₂ (z - (t₁ - t₂) * w)| := by
  let u := velocity σ α γ s t₁ z
  have hchar : velocity σ α γ s t₂ (z - (t₁ - t₂) * u) = u :=
    velocity_on_characteristic hα hγ hs ht₂
  rcases le_total w u with hwu | huw
  · have hpos : z - (t₁ - t₂) * u ≤ z - (t₁ - t₂) * w := by nlinarith
    have hm := velocity_monotone (σ := σ) hα hγ hs ht₂ hpos
    rw [hchar] at hm
    have hwu' : w ≤ velocity σ α γ s t₂ (z - (t₁ - t₂) * w) := hwu.trans hm
    change |w - u| ≤ _
    rw [abs_of_nonpos (sub_nonpos.mpr hwu), abs_of_nonpos (sub_nonpos.mpr hwu')]
    linarith
  · have hpos : z - (t₁ - t₂) * w ≤ z - (t₁ - t₂) * u := by nlinarith
    have hm := velocity_monotone (σ := σ) hα hγ hs ht₂ hpos
    rw [hchar] at hm
    have huw' : velocity σ α γ s t₂ (z - (t₁ - t₂) * w) ≤ w := hm.trans huw
    change |w - u| ≤ _
    rw [abs_of_nonneg (sub_nonneg.mpr huw), abs_of_nonneg (sub_nonneg.mpr huw')]
    linarith

/-- An algebraic form of the density-coefficient estimate. The two conditions on `C` absorb
the spatial scale and the compressed-time scale separately. -/
theorem density_coefficient_le_of_constant {K S s t k C : ℝ}
    (hK : 0 ≤ K) (hS : 0 ≤ S) (hS1 : S ≤ 1) (hs : 0 < s) (ht : 0 ≤ t)
    (hk : 0 < k) (hC : 1 ≤ C) (hCk : 1 ≤ C * k) :
    K * S / (s + t * k * S) ≤ K * C / (s + t) := by
  have hspace : s * S ≤ C * s := by
    have h₁ := mul_le_mul_of_nonneg_left hS1 hs.le
    have h₂ := mul_le_mul_of_nonneg_right hC hs.le
    nlinarith only [h₁, h₂]
  have htime : t * S ≤ C * (t * k * S) := by
    have h := mul_le_mul_of_nonneg_right hCk (mul_nonneg ht hS)
    nlinarith only [h]
  have hsum : S * (s + t) ≤ C * (s + t * k * S) := by
    nlinarith only [hspace, htime]
  apply (div_le_div_iff₀ (by positivity : 0 < s + t * k * S)
    (by positivity : 0 < s + t)).mpr
  calc
    (K * S) * (s + t) = K * (S * (s + t)) := by ring
    _ ≤ K * (C * (s + t * k * S)) := mul_le_mul_of_nonneg_left hsum hK
    _ = (K * C) * (s + t * k * S) := by ring

/-- Uniform density coefficient bound for the cold-core Jacobian. In the manuscript `k` is
`α * γ` and `S` is a squared hyperbolic secant. -/
theorem density_coefficient_le {K S s t k : ℝ}
    (hK : 0 ≤ K) (hS : 0 ≤ S) (hS1 : S ≤ 1) (hs : 0 < s) (ht : 0 ≤ t)
    (hk : 0 < k) :
    K * S / (s + t * k * S) ≤ K * max 1 (1 / k) / (s + t) := by
  apply density_coefficient_le_of_constant hK hS hS1 hs ht hk (le_max_left _ _)
  calc
    1 = (1 / k) * k := by field_simp
    _ ≤ max 1 (1 / k) * k := mul_le_mul_of_nonneg_right (le_max_right _ _) hk.le

end BoltzmannNonuniqueness.AxialFlow

end

end

section

/-!
# Singular line integrals in the Carleman slice bound

For `q > 1`, the one-dimensional slice of the transverse power singularity
is integrable away from the line through the axis and has exactly the
power `|A|^(1-q)` appearing in Section 3, equation `ker:line-integral`.
-/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.AxialSlices

def lineProfile (q s : ℝ) : ℝ := (1 + s ^ 2) ^ (-q / 2)

def lineConstant (q : ℝ) : ℝ := ∫ s : ℝ, lineProfile q s

theorem lineProfile_pos (q s : ℝ) : 0 < lineProfile q s := by
  unfold lineProfile
  exact Real.rpow_pos_of_pos (by positivity) _

theorem integrable_lineProfile {q : ℝ} (hq : 1 < q) : Integrable (lineProfile q) := by
  change Integrable (fun s : ℝ => (1 + s ^ 2) ^ (-q / 2))
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
    (r := q) (by simpa using hq)
  simpa only [Real.norm_eq_abs, sq_abs] using h

theorem lineConstant_pos {q : ℝ} (hq : 1 < q) : 0 < lineConstant q := by
  have hs : Function.support (lineProfile q) = univ := by
    ext s
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (lineProfile_pos q s).ne'
  apply (integral_pos_iff_support_of_nonneg (fun s => (lineProfile_pos q s).le)
    (integrable_lineProfile hq)).mpr
  rw [hs]
  simp

theorem lineProfile_scale (q A s : ℝ) (hA : A ≠ 0) :
    (A ^ 2 + s ^ 2) ^ (-q / 2) = |A| ^ (-q) * lineProfile q (s / |A|) := by
  have ha : 0 < |A| := abs_pos.mpr hA
  have hsq : A ^ 2 + s ^ 2 = |A| ^ 2 * (1 + (s / |A|) ^ 2) := by
    field_simp
    nlinarith [sq_abs A]
  rw [hsq, Real.mul_rpow (sq_nonneg _) (by positivity)]
  have hp : (|A| ^ 2) ^ (-q / 2) = |A| ^ (-q) := by
    rw [← Real.rpow_natCast_mul ha.le 2]
    congr 1
    ring
  rw [hp]
  rfl

theorem integrable_singular_line {q A : ℝ} (hq : 1 < q) (hA : A ≠ 0) :
    Integrable (fun s : ℝ => (A ^ 2 + s ^ 2) ^ (-q / 2)) := by
  have h := ((integrable_lineProfile hq).comp_div (abs_ne_zero.mpr hA)).const_mul
    (|A| ^ (-q))
  apply h.congr
  filter_upwards [] with s
  exact (lineProfile_scale q A s hA).symm

/-- Exact singular line integral, including finiteness in a separate theorem above. -/
theorem singular_line_formula {q A : ℝ} (hq : 1 < q) (hA : A ≠ 0) :
    Integrable (fun s : ℝ => (A ^ 2 + s ^ 2) ^ (-q / 2)) ∧
      (∫ s : ℝ, (A ^ 2 + s ^ 2) ^ (-q / 2)) = lineConstant q * |A| ^ (1 - q) := by
  refine ⟨integrable_singular_line hq hA, ?_⟩
  have ha : 0 < |A| := abs_pos.mpr hA
  simp_rw [lineProfile_scale q A _ hA]
  rw [integral_const_mul, Measure.integral_comp_div]
  simp only [abs_abs, smul_eq_mul]
  have hp : |A| ^ (-q) * |A| = |A| ^ (1 - q) := by
    calc
      |A| ^ (-q) * |A| = |A| ^ (-q) * |A| ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = |A| ^ (-q + 1) := (Real.rpow_add ha _ _).symm
      _ = |A| ^ (1 - q) := by congr 1; ring
  change |A| ^ (-q) * (|A| * lineConstant q) = _
  rw [← mul_assoc, hp, mul_comm]

end BoltzmannNonuniqueness.AxialSlices

end

end

section

/-! # Uniform collapse of the implicit axial profile at small scales

This is the small-scale part of the characteristic-matching lemma in §8.
An interior profile value must approach z/t; the remaining values are close
to one of the two endpoint speeds. The bound is uniform in z and the center.
-/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.AxialFlow

def interiorArgumentBound (c : ℝ) : ℝ :=
  max |Real.artanh (-c)| |Real.artanh c|

theorem interiorArgumentBound_nonneg (c : ℝ) : 0 ≤ interiorArgumentBound c :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem abs_argument_le_of_tanh {x c : ℝ} (hc₁ : c < 1)
    (hx : |Real.tanh x| ≤ c) : |x| ≤ interiorArgumentBound c := by
  have hl := Real.artanh_le_artanh (x := -c) (y := Real.tanh x)
    (by linarith) (Real.tanh_lt_one x) (abs_le.mp hx).1
  have hu := Real.artanh_le_artanh (x := Real.tanh x) (y := c)
    (Real.neg_one_lt_tanh x) hc₁ (abs_le.mp hx).2
  rw [Real.artanh_tanh] at hl hu
  apply abs_le.mpr
  constructor
  · exact (neg_le_neg (le_max_left |Real.artanh (-c)| |Real.artanh c|)).trans
      ((neg_abs_le _).trans hl)
  · exact hu.trans ((le_abs_self _).trans (le_max_right _ _))

theorem velocity_interior_small_scale {α γ a δ : ℝ}
    (hα : 0 < α) (hγ : 0 < γ) (ha : 0 < a) (hδ : 0 < δ)
    {σ s t z : ℝ} (hs : 0 < s) (ht : a ≤ t)
    (hl : δ ≤ velocity σ α γ s t z-(σ-α))
    (hu : δ ≤ (σ+α)-velocity σ α γ s t z) :
    |velocity σ α γ s t z-z/t| ≤
      (interiorArgumentBound (1-δ/α)/(γ*a))*s := by
  let u := velocity σ α γ s t z
  let w := γ*(z-t*u)/s
  have he : u = σ+α*Real.tanh w := velocity_spec hα.le
  have hc₁ : 1-δ/α < 1 := by have := div_pos hδ hα; linarith
  have htan : |Real.tanh w| ≤ 1-δ/α := by
    apply abs_le.mpr
    constructor
    · apply (mul_le_mul_iff_right₀ hα).mp
      have hr : α*(-(1-δ/α)) = δ-α := by field_simp; ring
      rw [hr]
      linarith
    · apply (mul_le_mul_iff_right₀ hα).mp
      have hr : α*(1-δ/α) = α-δ := by field_simp
      rw [hr]
      linarith
  have hb := abs_argument_le_of_tanh hc₁ htan
  have hB := interiorArgumentBound_nonneg (1-δ/α)
  have hta : 0 < t := ha.trans_le ht
  have hz : |z-t*u| ≤ s*interiorArgumentBound (1-δ/α)/γ := by
    have hh : |w| = γ*|z-t*u|/s := by
      dsimp only [w]
      rw [abs_div,abs_mul,abs_of_pos hγ,abs_of_pos hs]
    rw [hh] at hb
    apply (le_div_iff₀ hγ).mpr
    have h := (div_le_iff₀ hs).mp hb
    nlinarith
  have hnorm : |u-z/t| = |z-t*u|/t := by
    have heq : u-z/t = -(z-t*u)/t := by field_simp; ring
    rw [heq,abs_div,abs_neg,abs_of_pos hta]
  rw [hnorm]
  calc
    _ ≤ (s*interiorArgumentBound (1-δ/α)/γ)/t := div_le_div_of_nonneg_right hz hta.le
    _ ≤ (s*interiorArgumentBound (1-δ/α)/γ)/a :=
      div_le_div_of_nonneg_left (by positivity) ha ht
    _ = _ := by ring

end BoltzmannNonuniqueness.AxialFlow

end

end

end OAI
