import Mathlib
import OAI.Probability.Ballisticity.Estimates.BufferFirstFailure
import OAI.Probability.Ballisticity.Estimates.PairUpwardRetention

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma rawPairEndpointLaw_height {d : ℕ} (e : Direction d) (H : ℕ)
    (ω : Environment d) (x : Lattice d × Lattice d) (a : ℝ)
    (hx : x ∈ PairAtHeight (realPosition (step e)) a) :
    ∀ᵐ y ∂rawPairEndpointLaw (realPosition (step e)) H ω x,
      y ∈ PairAtHeight (realPosition (step e)) (a+H) := by
  have hfinite (z : Lattice d) : IsFiniteMeasure
      (hitKernel (Strip (realPosition (step e)) z H) (Upper (realPosition (step e)) z H) (ω,z)) :=
    ⟨lt_of_le_of_lt (hitKernel_total_le_one (disjoint_strip_upper _ _ _) _) ENNReal.one_lt_top⟩
  let := hfinite x.2
  rw [rawPairEndpointLaw,Measure.ae_prod_iff_ae_ae (Set.to_countable _ |>.measurableSet)]
  filter_upwards [coordinate_hitKernel_supported e x.1 H ω] with y hy
  filter_upwards [coordinate_hitKernel_supported e x.2 H ω] with z hz
  constructor
  · change dot (realPosition y) (realPosition (step e)) = a+H
    rw [signedHeight_projection]
    have h := hx.1
    rw [signedHeight_projection] at h
    rw [←h]
    exact_mod_cast hy
  · change dot (realPosition z) (realPosition (step e)) = a+H
    rw [signedHeight_projection]
    have h := hx.2
    rw [signedHeight_projection] at h
    rw [←h]
    exact_mod_cast hz

lemma rawPairMixture_height {d : ℕ} (e : Direction d) (H : ℕ)
    (ω : Environment d) (π : Measure (Lattice d × Lattice d)) (a : ℝ)
    (hπ : ∀ᵐ x ∂π, x ∈ PairAtHeight (realPosition (step e)) a) :
    ∀ᵐ y ∂rawPairMixture (realPosition (step e)) H π ω,
      y ∈ PairAtHeight (realPosition (step e)) (a+H) := by
  rw [ae_iff,rawPairMixture_apply]
  apply (lintegral_eq_zero_iff (measurable_of_countable _)).mpr
  filter_upwards [hπ] with x hx
  exact (ae_iff.mp (rawPairEndpointLaw_height e H ω x a hx))

lemma retainedPairLaw_height {d : ℕ} (e f : Direction d) (H : ℕ) (z : ℝ)
    (ω : Environment d) (π : Measure (Lattice d × Lattice d)) (a : ℝ)
    (hπ : ∀ᵐ x ∂π, x ∈ PairAtHeight (realPosition (step e)) a) :
    ∀ᵐ y ∂retainedPairLaw (realPosition (step e)) f H z π ω,
      y ∈ PairAtHeight (realPosition (step e)) (a+H) :=
  (Measure.absolutelyContinuous_of_le (retainedPairLaw_le _ _ _ _ _ _)).ae_le
    (rawPairMixture_height e H ω π a hπ)

lemma pairUp_height {d : ℕ} (e : Direction d) (x : Lattice d × Lattice d) (a : ℝ)
    (hx : x ∈ PairAtHeight (realPosition (step e)) a) :
    pairUp e x ∈ PairAtHeight (realPosition (step e)) (a+1) := by
  constructor <;> simp only [pairUp,dot_realPosition_add,signed_direction_unit]
  · rw [hx.1]
  · rw [hx.2]

lemma upwardRetainedLaw_height {d : ℕ} (e f : Direction d) (H : ℕ) (z : ℝ)
    (ω : Environment d) (π : Measure (Lattice d × Lattice d)) (κ : ℝ≥0) (a : ℝ)
    (hπ : ∀ᵐ x ∂π, x ∈ PairAtHeight (realPosition (step e)) a) :
    ∀ᵐ y ∂upwardRetainedLaw e f H z π ω κ,
      y ∈ PairAtHeight (realPosition (step e)) (a+(H+1:ℕ)) := by
  unfold upwardRetainedLaw
  apply Measure.ae_smul_measure
  rw [ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _ |>.measurableSet)]
  filter_upwards [retainedPairLaw_height e f H z ω π a hπ] with x hx
  have := pairUp_height e x (a+H) hx
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using this
end DirectionalTransience

end

end

end OAI
