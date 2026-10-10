import OAI.Geometry.EinsteinFour.WeylGeometry
import Mathlib.MeasureTheory.Measure.Hausdorff

namespace OAI

/-! The finite sphere moments needed for the angular Jacobi calculation.
The conditional input below is precisely the degree 2, 4 and 6 specialization
of Folland, *How to Integrate a Polynomial over a Sphere*, American
Mathematical Monthly 108 (2001), 446–448, Theorem on p.447, after division by
the area of S³. DOI: 10.1080/00029890.2001.11919774.
It contains no curvature or geometric inequality.
-/

namespace PositiveEinsteinFour.Angular

open EinsteinFour MeasureTheory

noncomputable section

abbrev Directions := {q : FourSpace // ‖q‖ = 1}

instance : CompactSpace Directions := by
  apply isCompact_iff_compactSpace.mp
  simpa only [Metric.sphere, dist_zero_right] using! isCompact_sphere (0 : FourSpace) 1

/-- The normalized spherical measure is fixed, not an arbitrary probability
measure satisfying the desired curvature averages. -/
def sphereMeasure : Measure Directions :=
  ((Measure.hausdorffMeasure 3 : Measure Directions) Set.univ)⁻¹ •
    (Measure.hausdorffMeasure 3 : Measure Directions)

def delta (i j : Fin 4) : ℝ := if i = j then 1 else 0

def momentTwo (i j : Fin 4) : ℝ := delta i j / 4

def momentFour (i j k l : Fin 4) : ℝ :=
  (delta i j * delta k l + delta i k * delta j l + delta i l * delta j k) / 24

/-- The fifteen pairings of six indices, grouped by the partner of `i`. -/
def momentSix (i j k l m n : Fin 4) : ℝ :=
  (delta i j * momentFour k l m n + delta i k * momentFour j l m n +
    delta i l * momentFour j k m n + delta i m * momentFour j k l n +
    delta i n * momentFour j k l m) / 8

/-- Finite angular moment identities. -/
structure FollandMoments : Prop where
  probability : IsProbabilityMeasure sphereMeasure
  second (i j : Fin 4) :
    (∫ q : Directions, q.val i * q.val j ∂sphereMeasure) = momentTwo i j
  fourth (i j k l : Fin 4) :
    (∫ q : Directions, q.val i * q.val j * q.val k * q.val l ∂sphereMeasure) =
      momentFour i j k l
  sixth (i j k l m n : Fin 4) :
    (∫ q : Directions, q.val i * q.val j * q.val k * q.val l * q.val m * q.val n
      ∂sphereMeasure) = momentSix i j k l m n

theorem continuous_coordinate (i : Fin 4) : Continuous (fun q : Directions => q.val i) := by
  fun_prop

theorem continuous_integrable (h : FollandMoments) {f : Directions → ℝ}
    (hf : Continuous f) : Integrable f sphereMeasure := by
  let : IsProbabilityMeasure sphereMeasure := h.probability
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem integral_sum {ι : Type*} [Fintype ι] (h : FollandMoments)
    (f : ι → Directions → ℝ) (hf : ∀ i, Continuous (f i)) :
    (∫ q, ∑ i, f i q ∂sphereMeasure) = ∑ i, ∫ q, f i q ∂sphereMeasure := by
  exact integral_finsetSum _ (fun i _ => continuous_integrable h (hf i))

theorem integral_sum4 {ι κ ρ τ : Type*} [Fintype ι] [Fintype κ]
    [Fintype ρ] [Fintype τ] (h : FollandMoments)
    (f : ι → κ → ρ → τ → Directions → ℝ)
    (hf : ∀ i j k l, Continuous (f i j k l)) :
    (∫ q, ∑ i, ∑ j, ∑ k, ∑ l, f i j k l q ∂sphereMeasure) =
      ∑ i, ∑ j, ∑ k, ∑ l, ∫ q, f i j k l q ∂sphereMeasure := by
  rw [integral_sum h _ (fun _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_sum h _ (fun _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_sum h _ (fun _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro k _
  exact integral_sum h _ (hf i j k)

theorem integral_quadratic (h : FollandMoments) (C : Fin 4 → Fin 4 → ℝ) :
    (∫ q : Directions, ∑ i, ∑ j, C i j * (q.val i * q.val j) ∂sphereMeasure) =
      (∑ i, C i i) / 4 := by
  let : IsProbabilityMeasure sphereMeasure := h.probability
  have hi (i j : Fin 4) : Integrable
      (fun q : Directions => C i j * (q.val i * q.val j)) sphereMeasure :=
    ((continuous_coordinate i).mul (continuous_coordinate j)).const_mul _ |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hi i j)]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j), integral_const_mul, h.second]
  simp [momentTwo, delta, div_eq_mul_inv, mul_ite, ite_mul, Finset.sum_mul]

/-- A directional derivative has one fourth of its full squared norm on S³. -/
theorem integral_directional_square (h : FollandMoments) (v : Fin 4 → ℝ) :
    (∫ q : Directions, (∑ i, q.val i * v i) ^ 2 ∂sphereMeasure) =
      (∑ i, v i ^ 2) / 4 := by
  have heq : (fun q : Directions => (∑ i, q.val i * v i) ^ 2) =
      (fun q => ∑ i, ∑ j, (v i * v j) * (q.val i * q.val j)) := by
    funext q
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq, integral_quadratic h]
  simp only [pow_two]

end

end PositiveEinsteinFour.Angular

end OAI
