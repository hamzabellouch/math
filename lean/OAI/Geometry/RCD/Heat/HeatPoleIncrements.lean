import OAI.Geometry.RCD.Heat.DyadicHeatFamily

namespace OAI

/-! # Heat increments with a fixed cutoff center and a variable pole -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {n : ℕ} {U : Euclidean n →L[ℝ] SobolevSpace μ hQ}
  {M : PositiveBilinearMeasure X (Euclidean n)} {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0}
  (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r L v)
  {ρ C : ℝ} (χ : GoodLaplacianCutoff μ hQ p ρ C)

/-- The cutoff and energy are fixed; the pole is an independent point. -/
theorem harmonic_heat_increment_lower_mass_at (x : X) (hρ : 0 < ρ) (hρr : ρ < r) (hκ : 0 ≤ κ)
    (S : Set X) (hS : MeasurableSet S) (hχone : ∀ y ∈ S, (χ.weight : X → ℝ) y = 1)
    {s t c η lambda : ℝ} (hs : 0 < s) (hst : s ≤ t) (hlambda0 : 0 ≤ lambda)
    (hlambda : 2 * κ * (L : ℝ) ^ 2 + η ≤ lambda)
    (herror : ∀ u ∈ Icc s t, ‖harmonicHeatError μ hQ (k := ker) G χ u x‖ ≤ η)
    (hkernel : ∀ u ∈ Icc s t, ∀ y ∈ S, c ≤ ker u x y)
    (v : Euclidean n) :
    (2 * c * (t - s)) * ⟪v, M.massOperator S v⟫_ℝ ≤
      ⟪v, cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
        U (hs.trans_le hst) x lambda v⟫_ℝ -
      ⟪v, cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
        U hs x lambda v⟫_ℝ := by
  let F := fun u => ⟪v, cutoffHeatGramAt μ hQ hk χ.weight.continuous
    (χ.hasCompactSupport μ hQ) U u x lambda v⟫_ℝ
  let b := 2 * c * ⟪v, M.massOperator S v⟫_ℝ
  have hderiv (u : ℝ) (hu : u ∈ Icc s t) :
      HasDerivAt F ⟪v, harmonicHeatDerivative μ hQ hk G χ (hs.trans_le hu.1) x lambda v⟫_ℝ u :=
    harmonicHeatQuadratic_hasDerivAt μ hQ hk G χ hρ hρr (hs.trans_le hu.1) x hlambda0 v
  have hbound (u : ℝ) (hu : u ∈ Icc s t) :
      b ≤ ⟪v, harmonicHeatDerivative μ hQ hk G χ (hs.trans_le hu.1) x lambda v⟫_ℝ := by
    have hm := cutoffHeatMass_lower_mass μ hQ hk χ.weight.continuous
      (χ.hasCompactSupport μ hQ) M (fun y => (χ.bounds y).1) (hs.trans_le hu.1) x S hS hχone
      c (hkernel u hu) v
    have hd := (harmonicHeatDerivative_bounds μ hQ hk G χ hρr hκ (hs.trans_le hu.1) x
      (herror u hu) hlambda v).1
    dsimp only [b]
    linarith
  have hm := (convex_Icc s t).mul_sub_le_image_sub_of_le_deriv
    (fun u hu => (hderiv u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hderiv u (interior_subset hu)).differentiableAt.differentiableWithinAt)
    (C := b)
    (fun u hu => by
      rw [(hderiv u (interior_subset hu)).deriv]
      exact hbound u (interior_subset hu))
    s (left_mem_Icc.mpr hst) t (right_mem_Icc.mpr hst) hst
  dsimp only [F, b] at hm
  rw [cutoffHeatGramAt_of_pos μ hQ hk _ _ U hs,
    cutoffHeatGramAt_of_pos μ hQ hk _ _ U (hs.trans_le hst)] at hm
  linarith


/-- The upper increment also uses an independent heat pole. -/
theorem dyadic_heat_increment_upper_bound_at (x : X) (hρ : 0 < ρ) (hρr : ρ < r) (hκ : 0 ≤ κ)
    {s E η lambda : ℝ} (hs : 0 < s) (hlambda0 : 0 ≤ lambda)
    (hlambda : 2 * κ * (L : ℝ) ^ 2 + η ≤ lambda)
    (herror : ∀ t ∈ Icc (s ^ 2 / 4) (s ^ 2), ‖harmonicHeatError μ hQ (k := ker) G χ t x‖ ≤ η)
    (v : Euclidean n)
    (hmass : ∀ t ∈ Icc (s ^ 2 / 4) (s ^ 2), ∀ ht : 0 < t,
      s ^ 2 * ⟪v, cutoffHeatMass μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ) M ht x v⟫_ℝ ≤ E) :
    ⟪v, cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
      U (sq_pos_of_pos hs) x lambda v⟫_ℝ -
    ⟪v, cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
      U (div_pos (sq_pos_of_pos hs) (by norm_num : (0 : ℝ) < 4)) x lambda v⟫_ℝ ≤
      (3 / 2 : ℝ) * E + (3 / 4 : ℝ) * s ^ 2 * (lambda + η) * ‖v‖ ^ 2 := by
  let F := fun t => ⟪v, cutoffHeatGramAt μ hQ hk χ.weight.continuous
    (χ.hasCompactSupport μ hQ) U t x lambda v⟫_ℝ
  have hs0 : 0 < s ^ 2 / 4 := div_pos (sq_pos_of_pos hs) (by norm_num)
  have hst : s ^ 2 / 4 ≤ s ^ 2 := by nlinarith [sq_nonneg s]
  have hderiv (t : ℝ) (ht : t ∈ Icc (s ^ 2 / 4) (s ^ 2)) :
      HasDerivAt F ⟪v, harmonicHeatDerivative μ hQ hk G χ (hs0.trans_le ht.1) x lambda v⟫_ℝ t :=
    harmonicHeatQuadratic_hasDerivAt μ hQ hk G χ hρ hρr (hs0.trans_le ht.1) x hlambda0 v
  have hbound (t : ℝ) (ht : t ∈ Icc (s ^ 2 / 4) (s ^ 2)) :
      ⟪v, harmonicHeatDerivative μ hQ hk G χ (hs0.trans_le ht.1) x lambda v⟫_ℝ ≤
        2 * E / s ^ 2 + (lambda + η) * ‖v‖ ^ 2 := by
    have hb := (harmonicHeatDerivative_bounds μ hQ hk G χ hρr hκ (hs0.trans_le ht.1) x
      (herror t ht) hlambda v).2
    have hM : ⟪v, cutoffHeatMass μ hQ hk χ.weight.continuous
        (χ.hasCompactSupport μ hQ) M (hs0.trans_le ht.1) x v⟫_ℝ ≤ E / s ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hs)).mpr
      nlinarith only [hmass t ht (hs0.trans_le ht.1)]
    calc
      _ ≤ _ := hb
      _ ≤ 2 * (E / s ^ 2) + (lambda + η) * ‖v‖ ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hM (by norm_num)) le_rfl
      _ = _ := by ring
  have hm := (convex_Icc (s ^ 2 / 4) (s ^ 2)).image_sub_le_mul_sub_of_deriv_le
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (C := 2 * E / s ^ 2 + (lambda + η) * ‖v‖ ^ 2)
    (fun t ht => by rw [(hderiv t (interior_subset ht)).deriv]; exact hbound t (interior_subset ht))
    (s ^ 2 / 4) (left_mem_Icc.mpr hst) (s ^ 2) (right_mem_Icc.mpr hst) hst
  have he : (2 * E / s ^ 2 + (lambda + η) * ‖v‖ ^ 2) * (s ^ 2 - s ^ 2 / 4) =
      (3 / 2 : ℝ) * E + (3 / 4 : ℝ) * s ^ 2 * (lambda + η) * ‖v‖ ^ 2 := by
    field_simp [ne_of_gt hs]
    ring
  rw [he] at hm
  dsimp only [F] at hm
  simpa only [cutoffHeatGramAt_of_pos μ hQ hk _ _ U hs0,
    cutoffHeatGramAt_of_pos μ hQ hk _ _ U (sq_pos_of_pos hs)] using hm

end RegularPointCoordinates

end

end OAI
