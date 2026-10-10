import OAI.Analysis.OInfinity.ClockGram
import OAI.Analysis.OInfinity.RohlinPolar

namespace OAI

/-! # Continuous polar correction of the actual clock path

The correction is the fixed formula `x (x* x)^(-1/2)`. Both Gram bounds
come from the proved three-term cancellation estimates. Continuity and
exact endpoint preservation are proved for this formula; no cocycle or
half-flip equation is assumed or concluded.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

local instance clockPolarOrder : PartialOrder E := CStarAlgebra.spectralOrder E
local instance clockPolarStarOrder : StarOrderedRing E := CStarAlgebra.spectralOrderedRing E

/-- The explicit polar correction, on the open set used below. -/
def clockPolarValue (x : E) : E := x * CFC.rpow (star x * x) (-1 / 2 : ℝ)

lemma clockPolarValue_mem (x : E) (hi : IsUnit (star x * x))
    (hf : IsUnit (x * star x)) : clockPolarValue x ∈ unitary E := by
  obtain ⟨u, hu⟩ := exists_polar_unitary_of_two_gram_units x hi hf
  change x * CFC.rpow (star x * x) (-1 / 2 : ℝ) ∈ unitary E
  rw [← hu]
  exact u.prop

lemma clockPolarValue_of_unitary (x : E) (hx : x ∈ unitary E) :
    clockPolarValue x = x := by
  simp only [clockPolarValue, hx.1, CFC.rpow_eq_pow, CFC.one_rpow, mul_one]

/-- Continuity uses strict positivity of the actual initial Gram element. -/
lemma clockPolarValue_continuous {X : Type*} [TopologicalSpace X] (f : X → E)
    (hf : Continuous f) (hi : ∀ t, IsUnit (star (f t) * f t)) :
    Continuous (fun t => clockPolarValue (f t)) := by
  have hg : Continuous (fun t => star (f t) * f t) := hf.star.mul hf
  have hp : ∀ t, IsStrictlyPositive (star (f t) * f t) :=
    fun t => (hi t).isStrictlyPositive (star_mul_self_nonneg _)
  have hc : Continuous (fun t => CFC.rpow (star (f t) * f t) (-1 / 2 : ℝ)) :=
    (CFC.continuousOn_rpow (-1 / 2 : ℝ)).comp_continuous hg hp
  exact hf.mul hc

/-- A uniform tolerance for this explicit correction, not an unspecified
choice of a nearby unitary. -/
lemma exists_clockPolar_tolerance [Nontrivial E] (ε : ℝ) (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ ∀ x : E,
      ‖star x * x - 1‖ < τ → ‖x * star x - 1‖ < τ →
      clockPolarValue x ∈ unitary E ∧ ‖clockPolarValue x - x‖ < ε := by
  have hcont : ContinuousWithinAt (fun a : E => CFC.rpow a (-1 / 2 : ℝ))
      {a | IsStrictlyPositive a} 1 :=
    CFC.continuousOn_rpow (-1 / 2 : ℝ) 1 isStrictlyPositive_one
  obtain ⟨τ, hτ, hb⟩ := Metric.continuousWithinAt_iff.mp hcont (ε / 2) (half_pos hε)
  refine ⟨min τ 1, lt_min hτ zero_lt_one, min_le_right _ _, ?_⟩
  intro x hix hfx
  have hix1 : ‖star x * x - 1‖ < 1 := hix.trans_le (min_le_right _ _)
  have hfx1 : ‖x * star x - 1‖ < 1 := hfx.trans_le (min_le_right _ _)
  have hi := isUnit_of_norm_sub_one_lt _ hix1
  have hf := isUnit_of_norm_sub_one_lt _ hfx1
  refine ⟨clockPolarValue_mem x hi hf, ?_⟩
  have ha : IsStrictlyPositive (star x * x) := hi.isStrictlyPositive (star_mul_self_nonneg _)
  have hbsmall : ‖CFC.rpow (star x * x) (-1 / 2 : ℝ) - 1‖ < ε / 2 := by
    simpa only [dist_eq_norm, CFC.rpow_eq_pow, CFC.one_rpow] using
      hb ha (show dist (star x * x) 1 < τ from by
        rw [dist_eq_norm]
        exact hix.trans_le (min_le_left _ _))
  have hxnorm : ‖x‖ < 2 := by
    have hh : ‖star x * x‖ < 2 := by
      calc
        _ ≤ ‖star x * x - 1‖ + ‖(1 : E)‖ := norm_le_norm_sub_add _ _
        _ = ‖star x * x - 1‖ + 1 := by rw [norm_one]
        _ < 2 := by linarith
    rw [CStarRing.norm_star_mul_self] at hh
    nlinarith [norm_nonneg x]
  calc
    _ = ‖x * (CFC.rpow (star x * x) (-1 / 2 : ℝ) - 1)‖ := by
      rw [clockPolarValue, mul_sub, mul_one]
    _ ≤ ‖x‖ * ‖CFC.rpow (star x * x) (-1 / 2 : ℝ) - 1‖ := norm_mul_le _ _
    _ ≤ 2 * ‖CFC.rpow (star x * x) (-1 / 2 : ℝ) - 1‖ :=
      mul_le_mul_of_nonneg_right hxnorm.le (norm_nonneg _)
    _ < 2 * (ε / 2) := mul_lt_mul_of_pos_left hbsmall (by norm_num)
    _ = ε := by ring

/-- The actual clock-corrected cancellation has a continuous unitary polar
correction, with both original endpoints unchanged and uniform error. -/
lemma exists_clockCorrected_unitary_path [Nontrivial E] (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (k : unitary E) (a b u : E),
      star a * a = 1 → star b * b = 1 → star a * b = 0 → u ∈ unitary E →
      ‖a * (k : E) - (k : E) * a‖ ≤ δ →
      ‖b * (k : E) - (k : E) * b‖ ≤ δ →
      ‖u * (k : E) - (k : E) * u‖ ≤ δ →
      ∃ p : ℝ → unitary E, Continuous p ∧
        (p 0 : E) = cornerCompression a u * cornerCompression b (star u) ∧
        (p (Real.pi / 2) : E) = 1 ∧
        (∀ θ, Joined (1 : unitary E) (p θ)) ∧
        ∀ θ, ‖(p θ : E) - clockCorrectedCancellation k a b u θ‖ < ε := by
  obtain ⟨τ, hτ, hτ1, hcorr⟩ := exists_clockPolar_tolerance (E := E) ε hε
  let δ := τ / 1800
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro k a b u ha hb hab hu hca hcb hcu
  let z := clockCorrectedCancellation k a b u
  have hg (θ : ℝ) : ‖star (z θ) * z θ - 1‖ < τ ∧ ‖z θ * star (z θ) - 1‖ < τ := by
    have h := clockCorrectedCancellation_gram_errors_of_constituents k a b u
      ha hb hab hu δ hδ.le hca hcb hcu θ
    have hbnd : 900 * δ < τ := by dsimp only [δ]; linarith
    exact ⟨h.1.trans_lt hbnd, h.2.trans_lt hbnd⟩
  have hi (θ : ℝ) : IsUnit (star (z θ) * z θ) :=
    isUnit_of_norm_sub_one_lt _ ((hg θ).1.trans_le hτ1)
  have hf (θ : ℝ) : IsUnit (z θ * star (z θ)) :=
    isUnit_of_norm_sub_one_lt _ ((hg θ).2.trans_le hτ1)
  let p (θ : ℝ) : unitary E := ⟨clockPolarValue (z θ), clockPolarValue_mem _ (hi θ) (hf θ)⟩
  have hp : Continuous p :=
    (clockPolarValue_continuous z (clockCorrectedCancellation_continuous k a b u) hi).subtype_mk _
  have hz0 : z 0 = cornerCancellationPath a b u 0 :=
    clockCorrectedCancellation_zero k a b u ha hb hab hu.2
  have hu0 : z 0 ∈ unitary E := by
    rw [hz0]
    exact cornerCancellationPath_mem 1 a b u (star_one _) ha hb hab
      (mul_one _) (mul_one _) (one_mul _) (mul_one _) hu.1 hu.2 0
  have hp0 : (p 0 : E) = cornerCompression a u * cornerCompression b (star u) := by
    change clockPolarValue (z 0) = _
    rw [clockPolarValue_of_unitary _ hu0, hz0, cornerCancellationPath_zero]
  have hq : (p (Real.pi / 2) : E) = 1 := by
    change clockPolarValue (z (Real.pi / 2)) = 1
    rw [show z (Real.pi / 2) = 1 from clockCorrectedCancellation_pi_div_two k a b u]
    exact clockPolarValue_of_unitary 1 (one_mem _)
  refine ⟨p, hp, hp0, hq, ?_, ?_⟩
  · intro θ
    have hj := (PathConnectedSpace.joined (Real.pi / 2) θ).map hp
    have hqp : p (Real.pi / 2) = 1 := Subtype.ext hq
    rwa [hqp] at hj
  · intro θ
    exact (hcorr (z θ) (hg θ).1 (hg θ).2).2


private lemma clockPolar_isometry_norm (x : E) (hx : star x * x = 1) : ‖x‖ ≤ 1 := by
  have h := congrArg norm hx
  rw [CStarRing.norm_star_mul_self] at h
  nlinarith [norm_nonneg x, (IsStarProjection.one E).norm_le]

private lemma clockPolar_corner_norm (a b x : E)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hx : ‖x‖ ≤ 2) :
    ‖a * x * star b‖ ≤ 2 := by
  calc
    _ ≤ ‖a * x‖ * ‖star b‖ := norm_mul_le _ _
    _ ≤ (‖a‖ * ‖x‖) * ‖b‖ := by rw [norm_star]; gcongr; exact norm_mul_le _ _
    _ ≤ (1 * 2) * 1 := by gcongr
    _ = 2 := by norm_num

/-- The explicit corrected polynomial retains a uniform angular bound,
independently of the clock and of the constituent unitary. -/
lemma clockCorrectedCancellation_sub_norm_le (k : unitary E) (a b u : E)
    (ha : star a * a = 1) (hb : star b * b = 1) (hu : u ∈ unitary E)
    (θ φ : ℝ) :
    ‖clockCorrectedCancellation k a b u θ - clockCorrectedCancellation k a b u φ‖ ≤
      16 * |θ - φ| := by
  have han := clockPolar_isometry_norm a ha
  have hbn := clockPolar_isometry_norm b hb
  have hun := clockPolar_isometry_norm u hu.1
  have hum : ‖u - 1‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [(IsStarProjection.one E).norm_le])
  have hus : ‖star u - 1‖ ≤ 2 := by
    calc
      _ = ‖star (u - 1)‖ := by rw [star_sub, star_one]
      _ = ‖u - 1‖ := norm_star _
      _ ≤ 2 := hum
  let C := clockCancellationIncrement a b u
  let X := clockCancellationCross a b u
  let Y := clockDegreeCorrection k 1 X - clockDegreeCorrection k (-1) (star X)
  have hC : ‖C‖ ≤ 4 := by
    apply (norm_add_le _ _).trans
    have h₁ := clockPolar_corner_norm a a (u - 1) han han hum
    have h₂ := clockPolar_corner_norm b b (star u - 1) hbn hbn hus
    linarith
  have hX : ‖X‖ ≤ 2 := clockPolar_corner_norm a b (u - 1) han hbn hum
  have hY : ‖Y‖ ≤ 4 := by
    apply (norm_sub_le _ _).trans
    simp only [clockDegreeCorrection_norm, norm_star]
    linarith
  have hsum : |Real.cos θ + Real.cos φ| ≤ 2 :=
    (abs_add_le _ _).trans (by linarith [Real.abs_cos_le_one θ, Real.abs_cos_le_one φ])
  have hcc : |Real.cos θ ^ 2 - Real.cos φ ^ 2| ≤ 2 * |θ - φ| := by
    rw [show Real.cos θ ^ 2 - Real.cos φ ^ 2 =
      (Real.cos θ - Real.cos φ) * (Real.cos θ + Real.cos φ) by ring, abs_mul]
    exact (mul_le_mul (Real.abs_cos_sub_cos_le θ φ) hsum (abs_nonneg _) (abs_nonneg _)).trans_eq (by ring)
  have hsc : |Real.sin θ * Real.cos θ - Real.sin φ * Real.cos φ| ≤ 2 * |θ - φ| := by
    rw [show Real.sin θ * Real.cos θ - Real.sin φ * Real.cos φ =
      (Real.sin θ - Real.sin φ) * Real.cos θ + Real.sin φ * (Real.cos θ - Real.cos φ) by ring]
    calc
      _ ≤ |(Real.sin θ - Real.sin φ) * Real.cos θ| +
          |Real.sin φ * (Real.cos θ - Real.cos φ)| := abs_add_le _ _
      _ = |Real.sin θ - Real.sin φ| * |Real.cos θ| +
          |Real.sin φ| * |Real.cos θ - Real.cos φ| := by rw [abs_mul, abs_mul]
      _ ≤ |θ - φ| * 1 + 1 * |θ - φ| := add_le_add
        (mul_le_mul (Real.abs_sin_sub_sin_le θ φ) (Real.abs_cos_le_one θ) (abs_nonneg _) (abs_nonneg _))
        (mul_le_mul (Real.abs_sin_le_one φ) (Real.abs_cos_sub_cos_le θ φ) (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  have he : clockCorrectedCancellation k a b u θ - clockCorrectedCancellation k a b u φ =
      (Real.cos θ ^ 2 - Real.cos φ ^ 2) • C +
      (Real.sin θ * Real.cos θ - Real.sin φ * Real.cos φ) • Y := by
    dsimp only [clockCorrectedCancellation, C, X, Y, clockCancellationIncrement, clockCancellationCross]
    simp only [star_mul, star_sub, star_one, star_star, mul_assoc]
    module
  rw [he]
  calc
    _ ≤ ‖(Real.cos θ ^ 2 - Real.cos φ ^ 2) • C‖ +
        ‖(Real.sin θ * Real.cos θ - Real.sin φ * Real.cos φ) • Y‖ := norm_add_le _ _
    _ = |Real.cos θ ^ 2 - Real.cos φ ^ 2| * ‖C‖ +
        |Real.sin θ * Real.cos θ - Real.sin φ * Real.cos φ| * ‖Y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (2 * |θ - φ|) * 4 + (2 * |θ - φ|) * 4 := by gcongr
    _ = _ := by ring

/-- Uniform closeness suffices for sampling the polar path; no Lipschitz
property of the functional-calculus correction is assumed. -/
lemma clockCorrected_near_path_sample_bound (k : unitary E) (a b u : E)
    (ha : star a * a = 1) (hb : star b * b = 1) (hu : u ∈ unitary E)
    (p : ℝ → unitary E) (η : ℝ)
    (hp : ∀ θ, ‖(p θ : E) - clockCorrectedCancellation k a b u θ‖ ≤ η)
    (θ φ : ℝ) : ‖(p θ : E) - p φ‖ ≤ 16 * |θ - φ| + 2 * η := by
  let z := clockCorrectedCancellation k a b u
  calc
    _ ≤ ‖(p θ : E) - z θ‖ + ‖z θ - p φ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖(p θ : E) - z θ‖ + (‖z θ - z φ‖ + ‖z φ - p φ‖) :=
      add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ ≤ η + (16 * |θ - φ| + η) := by
      apply add_le_add (hp θ)
      apply add_le_add (clockCorrectedCancellation_sub_norm_le k a b u ha hb hu θ φ)
      rw [norm_sub_rev]
      exact hp φ
    _ = _ := by ring

end WeakPureInfiniteness

end

end OAI
