import Mathlib
import OAI.Probability.Ballisticity.Walk.BoundaryPathCoordinates
import OAI.Probability.Ballisticity.Estimates.SharedEndpointTests

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def boundaryPrefixPair {d : ℕ} (D : BoundaryData d) : Path d × Path d :=
  (extendPrefix D.1.1 D.2.1, extendPrefix D.1.2 D.2.2)

noncomputable def centeredPastCoordinates {d q : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r : ℝ) (j : Fin q → ℕ) (x y : Lattice d) (P : Path d × Path d) : Fin q → ℝ × ℝ :=
  fun a => (centeredFirstHit ℓ f θ r (j a) x P.1, centeredFirstHit ℓ f θ r (j a) y P.2)

lemma measurable_centeredPastCoordinates {d q : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r : ℝ) (j : Fin q → ℕ) (x y : Lattice d) :
    Measurable (centeredPastCoordinates ℓ f θ r j x y) := by
  apply Measurable.of_eval
  intro a
  exact ((measurable_centeredFirstHit ℓ f θ r (j a) x).comp measurable_fst).prodMk
    ((measurable_centeredFirstHit ℓ f θ r (j a) y).comp measurable_snd)

lemma shared_centeredPastCoordinates_boundary {d q : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (x y : Lattice d) (hxy : signedHeight e x = signedHeight e y)
    (H : ℕ) (hH : 0 < H) (j : Fin q → ℕ) (hj : ∀ a, j a ≤ H) (θ r : ℝ) :
    let ℓ := realPosition (step e)
    ∀ᵐ P ∂sharedConditionedPairLaw ν ℓ x y,
      centeredPastCoordinates ℓ f θ r j x y P =
      centeredPastCoordinates ℓ f θ r j x y
        (boundaryPrefixPair (boundaryData ℓ ((signedHeight e x+H : ℤ) : ℝ) P)) := by
  dsimp only
  let ℓ := realPosition (step e)
  filter_upwards [sharedConditioned_regularPath ν ℓ htrans x y,
    shared_boundaryTimes_spec ν hue ℓ (signed_direction_unit e) htrans
      (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) x y hxy H hH]
    with P hP hb
  funext a
  obtain ⟨h1,h2⟩ := boundaryData_firstHit_prefix e x y hxy H P
    hP.1.1 hP.2.1 hP.1.2 hP.2.2 hb (j a) (hj a)
  simp only [centeredPastCoordinates,centeredFirstHit,boundaryPrefixPair]
  rw [h1,h2]

end DirectionalTransience

end

end

end OAI
