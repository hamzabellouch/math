import OAI.Geometry.RCD.Harmonic.LocalCaccioppoli

namespace OAI

/-! # Exact gradient localization for bounded level truncations

The level-set locality of the Cheeger energy gives the chain rule for
piecewise affine truncations without differentiability at their corners.
These are the bounded tests for the local harmonic mean-value argument.
-/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Equality up to a constant on a measurable level set identifies gradients. -/
theorem localGamma_eq_on_diff_level (f g h : SobolevSpace μ hQ) (c : ℝ) :
    ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ f x-SobolevSpace.toLp μ hQ g x = c →
      localGamma μ hQ f h x = localGamma μ hQ g h x := by
  have hz := localGamma_zero_on_level μ hQ (f-g) h c
  rw [map_sub] at hz
  filter_upwards [hz, localGamma_sub_left μ hQ f g h,
    Lp.coeFn_sub (SobolevSpace.toLp μ hQ f) (SobolevSpace.toLp μ hQ g)] with x hx hd he
  intro hfg
  have hh := hx (by simpa only [he, Pi.sub_apply] using hfg)
  rw [hd] at hh
  exact sub_eq_zero.mp hh

/-- The scalar truncation on the interval from k to k+m. -/
def upperLevelClip (k m s : ℝ) : ℝ := min (max (s-k) 0) m

theorem upperLevelClip_lipschitz (k m : ℝ) :
    LipschitzWith 1 (upperLevelClip k m) := by
  have hs : LipschitzWith 1 (fun s : ℝ => s-k) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simp only [Real.dist_eq, NNReal.coe_one, one_mul, sub_sub_sub_cancel_right, le_refl]
  exact (hs.max_const 0).min_const m

theorem upperLevelClip_zero {k m : ℝ} (hk : 0 ≤ k) (hm : 0 ≤ m) :
    upperLevelClip k m 0 = 0 := by
  simp only [upperLevelClip, zero_sub, max_eq_right (neg_nonpos.mpr hk),
    min_eq_left hm]

def SobolevSpace.upperLevelTruncation (f : SobolevSpace μ hQ) {k m : ℝ}
    (hk : 0 ≤ k) (hm : 0 ≤ m) : SobolevSpace μ hQ :=
  SobolevSpace.compContraction μ hQ (upperLevelClip_lipschitz k m)
    (upperLevelClip_zero hk hm) f

omit [BorelSpace X] [ProperSpace X] in
theorem SobolevSpace.upperLevelTruncation_coe (f : SobolevSpace μ hQ) {k m : ℝ}
    (hk : 0 ≤ k) (hm : 0 ≤ m) :
    SobolevSpace.toLp μ hQ (f.upperLevelTruncation μ hQ hk hm) =ᵐ[μ]
      fun x => upperLevelClip k m (SobolevSpace.toLp μ hQ f x) :=
  (upperLevelClip_lipschitz k m).coeFn_compLp (upperLevelClip_zero hk hm) _

/-- The localized bilinear chain rule for the bounded upper-level truncation. -/
theorem localGamma_upperLevelTruncation (f g : SobolevSpace μ hQ) {k m : ℝ}
    (hk : 0 ≤ k) (hm : 0 ≤ m) :
    localGamma μ hQ (f.upperLevelTruncation μ hQ hk hm) g =ᵐ[μ] fun x =>
      if k < SobolevSpace.toLp μ hQ f x ∧ SobolevSpace.toLp μ hQ f x < k+m
      then localGamma μ hQ f g x else 0 := by
  classical
  let v := f.upperLevelTruncation μ hQ hk hm
  filter_upwards [f.upperLevelTruncation_coe μ hQ hk hm,
    localGamma_zero_on_level μ hQ v g 0, localGamma_zero_on_level μ hQ v g m,
    localGamma_eq_on_diff_level μ hQ v f g (-k)] with x hv hzero htop hmid
  change SobolevSpace.toLp μ hQ v x = upperLevelClip k m (SobolevSpace.toLp μ hQ f x) at hv
  by_cases hlo : SobolevSpace.toLp μ hQ f x ≤ k
  · have hv0 : SobolevSpace.toLp μ hQ v x = 0 := by
      rw [hv, upperLevelClip, max_eq_right (sub_nonpos.mpr hlo), min_eq_left hm]
    rw [ite_eq_right (fun hh => (not_lt_of_ge hlo) hh.1)]
    exact hzero hv0
  · have hkf : k < SobolevSpace.toLp μ hQ f x := lt_of_not_ge hlo
    by_cases hhi : k+m ≤ SobolevSpace.toLp μ hQ f x
    · have hvm : SobolevSpace.toLp μ hQ v x = m := by
        rw [hv, upperLevelClip, max_eq_left (sub_nonneg.mpr hkf.le),
          min_eq_right (by linarith)]
      rw [ite_eq_right (fun hh => (not_lt_of_ge hhi) hh.2)]
      exact htop hvm
    · have hfm : SobolevSpace.toLp μ hQ f x < k+m := lt_of_not_ge hhi
      rw [ite_eq_left ⟨hkf,hfm⟩]
      apply hmid
      rw [hv, upperLevelClip, max_eq_left (sub_nonneg.mpr hkf.le),
        min_eq_left (by linarith)]
      ring

/-- The truncated square-gradient is the original square-gradient restricted
to the open level strip, including the correct zero values at both corners. -/
theorem localGamma_upperLevelTruncation_self (f : SobolevSpace μ hQ) {k m : ℝ}
    (hk : 0 ≤ k) (hm : 0 ≤ m) :
    let v := f.upperLevelTruncation μ hQ hk hm
    localGamma μ hQ v v =ᵐ[μ] fun x =>
      if k < SobolevSpace.toLp μ hQ f x ∧ SobolevSpace.toLp μ hQ f x < k+m
      then localGamma μ hQ f f x else 0 := by
  classical
  intro v
  filter_upwards [localGamma_upperLevelTruncation μ hQ f v hk hm,
    localGamma_upperLevelTruncation μ hQ f f hk hm,
    localGamma_comm μ hQ f v] with x h1 h2 hcomm
  change localGamma μ hQ v v x = _ at h1
  change localGamma μ hQ v f x = _ at h2
  rw [h1, hcomm, h2]
  split_ifs <;> rfl

/-- The upper positive part is a contraction fixing zero for nonnegative levels. -/
def upperLevelPart (k s : ℝ) : ℝ := max (s-k) 0

theorem upperLevelPart_lipschitz (k : ℝ) : LipschitzWith 1 (upperLevelPart k) := by
  have hs : LipschitzWith 1 (fun s : ℝ => s-k) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simp only [Real.dist_eq, NNReal.coe_one, one_mul, sub_sub_sub_cancel_right, le_refl]
  exact hs.max_const 0

theorem upperLevelPart_zero {k : ℝ} (hk : 0 ≤ k) : upperLevelPart k 0 = 0 := by
  simp only [upperLevelPart, zero_sub, max_eq_right (neg_nonpos.mpr hk)]

def SobolevSpace.upperPositivePart (f : SobolevSpace μ hQ) {k : ℝ}
    (hk : 0 ≤ k) : SobolevSpace μ hQ :=
  SobolevSpace.compContraction μ hQ (upperLevelPart_lipschitz k)
    (upperLevelPart_zero hk) f

omit [BorelSpace X] [ProperSpace X] in
theorem SobolevSpace.upperPositivePart_coe (f : SobolevSpace μ hQ) {k : ℝ}
    (hk : 0 ≤ k) :
    SobolevSpace.toLp μ hQ (f.upperPositivePart μ hQ hk) =ᵐ[μ]
      fun x => upperLevelPart k (SobolevSpace.toLp μ hQ f x) :=
  (upperLevelPart_lipschitz k).coeFn_compLp (upperLevelPart_zero hk) _

/-- The positive-part gradient agrees with the original gradient above the
level and vanishes on and below it. -/
theorem localGamma_upperPositivePart (f g : SobolevSpace μ hQ) {k : ℝ}
    (hk : 0 ≤ k) :
    localGamma μ hQ (f.upperPositivePart μ hQ hk) g =ᵐ[μ] fun x =>
      if k < SobolevSpace.toLp μ hQ f x then localGamma μ hQ f g x else 0 := by
  let v := f.upperPositivePart μ hQ hk
  filter_upwards [f.upperPositivePart_coe μ hQ hk,
    localGamma_zero_on_level μ hQ v g 0,
    localGamma_eq_on_diff_level μ hQ v f g (-k)] with x hv hzero hmid
  change SobolevSpace.toLp μ hQ v x = upperLevelPart k (SobolevSpace.toLp μ hQ f x) at hv
  by_cases hlo : SobolevSpace.toLp μ hQ f x ≤ k
  · have hv0 : SobolevSpace.toLp μ hQ v x = 0 := by
      rw [hv, upperLevelPart, max_eq_right (sub_nonpos.mpr hlo)]
    rw [ite_eq_right (not_lt_of_ge hlo)]
    exact hzero hv0
  · have hkf : k < SobolevSpace.toLp μ hQ f x := lt_of_not_ge hlo
    rw [ite_eq_left hkf]
    apply hmid
    rw [hv, upperLevelPart, max_eq_left (sub_nonneg.mpr hkf.le)]
    ring

/-- The same localized chain rule holds for the square-gradient. -/
theorem localGamma_upperPositivePart_self (f : SobolevSpace μ hQ) {k : ℝ}
    (hk : 0 ≤ k) :
    let v := f.upperPositivePart μ hQ hk
    localGamma μ hQ v v =ᵐ[μ] fun x =>
      if k < SobolevSpace.toLp μ hQ f x then localGamma μ hQ f f x else 0 := by
  intro v
  filter_upwards [localGamma_upperPositivePart μ hQ f v hk,
    localGamma_upperPositivePart μ hQ f f hk,
    localGamma_comm μ hQ f v] with x h1 h2 hcomm
  change localGamma μ hQ v v x = _ at h1
  change localGamma μ hQ v f x = _ at h2
  rw [h1, hcomm, h2]
  split_ifs <;> rfl

end RegularPointCoordinates

end

end OAI
