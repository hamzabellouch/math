import OAI.Geometry.RCD.Metric.EuclideanDimensionGap

namespace OAI

/-!
# An extra Euclidean factor contradicts a sufficiently flat n-dimensional ball

This uses the actual pointed approximation predicate: lift n+1 orthogonal
unit vectors through its density clause, then apply the finite-dimensional
distance obstruction. No topological dimension theorem is assumed.
-/

open Metric

noncomputable section

namespace RegularPointCoordinates

/-- Distortion and density for a ball approximation, without requiring the
center to be preserved. This also covers ordinary, unpointed GH maps. -/
def IsBallApproximation {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (p : X) (q : Y) (r R ε : ℝ) (f : X → Y) : Prop :=
  (∀ x y : X, dist x p ≤ R * r → dist y p ≤ R * r →
    |dist (f x) (f y) - dist x y / r| ≤ ε) ∧
  ∀ y : Y, dist y q ≤ R - ε →
    ∃ x : X, dist x p ≤ R * r ∧ dist (f x) y ≤ ε

private theorem approximation_distance_error {X Y Z : Type*}
    [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    {p : X} {qY : Y} {qZ : Z} {r R δ η : ℝ} {f : X → Y} {g : X → Z}
    (hf : IsBallApproximation p qY r R δ f)
    (hg : IsBallApproximation p qZ r R η g)
    {x y : X} (hx : dist x p ≤ R * r) (hy : dist y p ≤ R * r) (a b : Z) :
    |dist (f x) (f y) - dist a b| ≤ δ + η + dist (g x) a + dist (g y) b := by
  have hfxy := hf.1 x y hx hy
  have hgxy : |dist x y / r - dist (g x) (g y)| ≤ η := by
    simpa only [abs_sub_comm] using hg.1 x y hx hy
  have hab : |dist (g x) (g y) - dist a b| ≤ dist (g x) a + dist (g y) b := by
    simpa only [Real.dist_eq] using dist_dist_dist_le (g x) (g y) a b
  calc
    _ ≤ |dist (f x) (f y) - dist x y / r| + |dist x y / r - dist a b| := abs_sub_le _ _ _
    _ ≤ δ + (|dist x y / r - dist (g x) (g y)| + |dist (g x) (g y) - dist a b|) :=
      add_le_add hfxy (abs_sub_le _ _ _)
    _ ≤ _ := by linarith

private theorem orthogonal_units_distance {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    dist (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j 1) = Real.sqrt 2 := by
  have hs : dist (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j 1) ^ 2 = 2 := by
    rw [dist_eq_norm, norm_sub_sq_real]
    norm_num [EuclideanSpace.inner_single_left, hij]
  have he := Real.sqrt_sq (dist_nonneg : 0 ≤ dist (EuclideanSpace.single i (1 : ℝ))
    (EuclideanSpace.single j 1))
  rw [hs] at he
  exact he.symm

/-- The obstruction does not require either approximation to preserve
centers: lift the target center as well as the simplex vertices. -/
theorem unpointed_simplex_approximation_obstruction {X Y : Type*}
    [MetricSpace X] [MetricSpace Y] (n : ℕ) {p : X} {q : Y} {r R δ η a : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (ha : 0 < a) (hinside : a ≤ R - η)
    (f : X → Euclidean n) (g : X → Y) (v : Fin (n + 1) → Y)
    (hv : ∀ i, dist (v i) q = a)
    (hvv : ∀ i j, i ≠ j → dist (v i) (v j) = Real.sqrt 2 * a)
    (hf : IsBallApproximation p 0 r R δ f)
    (hg : IsBallApproximation p q r R η g) :
    a ≤ 10 * ((n + 1 : ℕ) : ℝ) ^ 2 * (δ + 3 * η) := by
  obtain ⟨x₀, hx₀ball, hx₀close⟩ := hg.2 q (by simp only [dist_self]; linarith)
  have hlift (i : Fin (n + 1)) : ∃ x : X, dist x p ≤ R * r ∧
      dist (g x) (v i) ≤ η := hg.2 (v i) (by rw [hv]; exact hinside)
  choose x hxball hxclose using hlift
  apply extra_dimension_scaled_distance_error n (f x₀) (fun i => f (x i)) ha
    (by positivity : 0 ≤ δ + 3 * η)
  · intro i
    have h := approximation_distance_error hf hg (hxball i) hx₀ball (v i) q
    rw [hv] at h
    linarith [hxclose i]
  · intro i j hij
    have h := approximation_distance_error hf hg (hxball i) (hxball j) (v i) (v j)
    rw [hvv i j hij] at h
    linarith [hxclose i, hxclose j]

/-- A finite orthogonal simplex already detects an extra direction. -/
theorem simplex_approximation_obstruction_radius {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (n : ℕ) {p : X} {q : Y} {r R δ η a : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (ha : 0 < a) (hinside : a ≤ R - η)
    (f : X → Euclidean n) (g : X → Y) (v : Fin (n + 1) → Y)
    (hv : ∀ i, dist (v i) q = a)
    (hvv : ∀ i j, i ≠ j → dist (v i) (v j) = Real.sqrt 2 * a)
    (hf : IsPointedApproximation p 0 r R δ f)
    (hg : IsPointedApproximation p q r R η g) :
    a ≤ 10 * ((n + 1 : ℕ) : ℝ) ^ 2 * (δ + 3 * η) := by
  have hlift (i : Fin (n + 1)) : ∃ x : X, dist x p ≤ R * r ∧
      dist (g x) (v i) ≤ η := hg.2.2 (v i) (by rw [hv]; exact hinside)
  choose x hxball hxclose using hlift
  have hpp : dist p p ≤ R * r := by simp only [dist_self]; exact mul_nonneg hR hr.le
  apply extra_dimension_scaled_distance_error n (f p) (fun i => f (x i)) ha
    (by positivity : 0 ≤ δ + 3 * η)
  · intro i
    have h := approximation_distance_error hf.2 hg.2 (hxball i) hpp (v i) q
    rw [hv] at h
    linarith [hxclose i, hg.1]
  · intro i j hij
    have h := approximation_distance_error hf.2 hg.2 (hxball i) (hxball j) (v i) (v j)
    rw [hvv i j hij] at h
    linarith [hxclose i, hxclose j]

/-- A finite orthogonal simplex already detects an extra direction. -/
theorem simplex_approximation_obstruction {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (n : ℕ) {p : X} {q : Y} {r δ η a : ℝ} (hr : 0 < r) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (ha : 0 < a) (hinside : a ≤ 2 - η)
    (f : X → Euclidean n) (g : X → Y) (v : Fin (n + 1) → Y)
    (hv : ∀ i, dist (v i) q = a)
    (hvv : ∀ i j, i ≠ j → dist (v i) (v j) = Real.sqrt 2 * a)
    (hf : IsPointedApproximation p 0 r 2 δ f)
    (hg : IsPointedApproximation p q r 2 η g) :
    a ≤ 10 * ((n + 1 : ℕ) : ℝ) ^ 2 * (δ + 3 * η) := by
  exact simplex_approximation_obstruction_radius n hr (by norm_num) hδ hη ha hinside
    f g v hv hvv hf hg

/-- A ball close to R^n cannot also be close to a space containing an
isometric R^(n+1) through its base point. This is the finite-point obstruction
needed for the non-extra-factor hypothesis of Huang--Huang Theorem4.1. -/
theorem extra_factor_approximation_obstruction {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (n : ℕ) {p : X} {r δ η : ℝ} (hr : 0 < r) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hsmall : δ + 3 * η ≤ 1)
    (f : X → Euclidean n) (g : X → Y) (e : Euclidean (n + 1) → Y) (he : Isometry e)
    (hf : IsPointedApproximation p 0 r 2 δ f)
    (hg : IsPointedApproximation p (e 0) r 2 η g) :
    1 ≤ 10 * ((n + 1 : ℕ) : ℝ) ^ 2 * (δ + 3 * η) := by
  have hlift (i : Fin (n + 1)) : ∃ x : X, dist x p ≤ 2 * r ∧
      dist (g x) (e (EuclideanSpace.single i 1)) ≤ η := by
    apply hg.2.2
    rw [he.dist_eq]
    have hunit : dist (EuclideanSpace.single i (1 : ℝ)) 0 = 1 := by simp
    rw [hunit]
    linarith
  choose x hxball hxclose using hlift
  have hpp : dist p p ≤ 2 * r := by simp only [dist_self]; positivity
  apply extra_dimension_distance_error n (f p) (fun i => f (x i))
    (by positivity : 0 ≤ δ + 3 * η) hsmall
  · intro i
    have h := approximation_distance_error hf.2 hg.2 (hxball i) hpp
      (e (EuclideanSpace.single i 1)) (e 0)
    have heq : dist (e (EuclideanSpace.single i 1)) (e 0) = 1 := by rw [he.dist_eq]; simp
    rw [heq] at h
    linarith [hxclose i, hg.1]
  · intro i j hij
    have h := approximation_distance_error hf.2 hg.2 (hxball i) (hxball j)
      (e (EuclideanSpace.single i 1)) (e (EuclideanSpace.single j 1))
    rw [he.dist_eq, orthogonal_units_distance i j hij] at h
    linarith [hxclose i, hxclose j]

end RegularPointCoordinates

end

end OAI
