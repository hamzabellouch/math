import OAI.Geometry.RCD.Metric.ProductFactorDiameter

namespace OAI

/-!
# The quantitative no-extra-factor hypothesis

An approximation by R^n excludes a product with an R^(n+1) factor, at a
fixed positive dimensional tolerance, giving the non-extra-factor
hypothesis in the Huang--Huang transformation theorem.
-/

open Metric

noncomputable section

namespace RegularPointCoordinates

universe u

/-- The ball-map form of the no-(n+1)-Euclidean condition. -/
def NoExtraEuclideanFactor {X : Type u} [MetricSpace X]
    (n : ℕ) (p : X) (r η : ℝ) : Prop :=
  ∀ (Z : Type u) (dZ : MetricSpace Z), letI := dZ
    ∀ (z : Z) (g : X → WithLp 2 (Euclidean (n + 1) × Z)),
      ¬IsBallApproximation p (WithLp.toLp 2 (0, z)) r 1 η g

/-- A single explicit tolerance works at every center and scale. -/
theorem noExtraEuclideanFactor_of_approximation {X : Type u} [MetricSpace X]
    (n : ℕ) {p : X} {r δ : ℝ} (_hr : 0 < r) (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / (100 * ((n + 1 : ℕ) : ℝ) ^ 2))
    (f : X → Euclidean n) (hf : IsPointedApproximation p 0 r 1 δ f) :
    NoExtraEuclideanFactor n p r (1 / (100 * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
  intro Z dZ z g hg
  let : MetricSpace Z := dZ
  let η : ℝ := 1 / (100 * ((n + 1 : ℕ) : ℝ) ^ 2)
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hden : 0 < 100 * ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hη : 0 < η := one_div_pos.mpr hden
  have hηsmall : η ≤ 1 / 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  let e : Euclidean (n + 1) → WithLp 2 (Euclidean (n + 1) × Z) :=
    fun v => WithLp.toLp 2 (v, z)
  have he (a b : Euclidean (n + 1)) : dist (e a) (e b) = dist a b :=
    metric_prod_same_second a b z
  let v : Fin (n + 1) → WithLp 2 (Euclidean (n + 1) × Z) :=
    fun i => e ((1 / 2 : ℝ) • EuclideanSpace.single i 1)
  have hv (i) : dist (v i) (WithLp.toLp 2 (0, z)) = 1 / 2 := by
    change dist (e ((1 / 2 : ℝ) • EuclideanSpace.single i 1)) (e 0) = _
    rw [he, dist_zero_right, norm_smul]
    norm_num
  have hvv (i j) (hij : i ≠ j) : dist (v i) (v j) = Real.sqrt 2 * (1 / 2) := by
    change dist (e ((1 / 2 : ℝ) • EuclideanSpace.single i 1))
      (e ((1 / 2 : ℝ) • EuclideanSpace.single j 1)) = _
    rw [he, dist_smul₀]
    have hd : dist (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j 1) = Real.sqrt 2 := by
      have hs : dist (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j 1) ^ 2 = 2 := by
        rw [dist_eq_norm, norm_sub_sq_real]
        norm_num [EuclideanSpace.inner_single_left, hij]
      have hsqrt := Real.sqrt_sq (dist_nonneg : 0 ≤ dist (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single j 1))
      rw [hs] at hsqrt
      exact hsqrt.symm
    rw [hd]
    norm_num
    ring
  have hobs := unpointed_simplex_approximation_obstruction n hδ hη.le
    (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : (1 / 2 : ℝ) ≤ 1 - η)
    f g v hv hvv hf.2 hg
  have hbound : 10 * ((n + 1 : ℕ) : ℝ) ^ 2 * (δ + 3 * η) ≤ 2 / 5 := by
    calc
      _ ≤ 10 * ((n + 1 : ℕ) : ℝ) ^ 2 * (η + 3 * η) := by gcongr
      _ = 2 / 5 := by dsimp [η]; field_simp; ring
  linarith

end RegularPointCoordinates

end

end OAI
