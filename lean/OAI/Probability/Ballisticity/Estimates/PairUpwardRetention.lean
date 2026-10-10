import Mathlib
import OAI.Probability.Ballisticity.Estimates.RawPairRetention
import OAI.Probability.Ballisticity.Crossings.FirstHitUpward

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def pairUp {d : ℕ} (e : Direction d) (x : Lattice d × Lattice d) : Lattice d × Lattice d :=
  (x.1+step e,x.2+step e)

lemma rawPairEndpointLaw_upward {d : ℕ} (e : Direction d)
    (H : ℕ) (ω : Environment d) (x : Lattice d × Lattice d)
    {κ : ℝ≥0} (hκ : ∀ y, κ ≤ (ω y).1 e) :
    (κ : ℝ≥0∞)^2 • (rawPairEndpointLaw (realPosition (step e)) H ω x).map (pairUp e) ≤
      rawPairEndpointLaw (realPosition (step e)) (H+1) ω x := by
  let ℓ := realPosition (step e)
  have hfinite (y : Lattice d) (h : ℕ) :
      IsFiniteMeasure (hitKernel (Strip ℓ y h) (Upper ℓ y h) (ω,y)) :=
    ⟨lt_of_le_of_lt (hitKernel_total_le_one (disjoint_strip_upper _ _ _) _) ENNReal.one_lt_top⟩
  let := hfinite x.1 H
  let := hfinite x.2 H
  let := hfinite x.1 (H+1)
  let := hfinite x.2 (H+1)
  have hp := Measure.prod_mono (coordinate_hitKernel_upward_retention e x.1 H ω hκ)
    (coordinate_hitKernel_upward_retention e x.2 H ω hκ)
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,←pow_two,
    Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_of_countable _)] at hp
  unfold pairUp
  simpa only [rawPairEndpointLaw,Prod.map_def,Nat.cast_add,Nat.cast_one] using hp

lemma rawPairMixture_upward {d : ℕ} (e : Direction d) (H : ℕ)
    (ω : Environment d) (π : Measure (Lattice d × Lattice d))
    {κ : ℝ≥0} (hκ : ∀ y, κ ≤ (ω y).1 e) :
    (κ : ℝ≥0∞)^2 • (rawPairMixture (realPosition (step e)) H π ω).map (pairUp e) ≤
      rawPairMixture (realPosition (step e)) (H+1) π ω := by
  intro U
  have hU := (Set.to_countable U).measurableSet
  have hm : Measurable (pairUp e) := measurable_of_countable _
  rw [Measure.smul_apply,smul_eq_mul,Measure.map_apply hm hU,rawPairMixture_apply,
    ←lintegral_const_mul _ (measurable_of_countable _),rawPairMixture_apply]
  apply lintegral_mono
  intro x
  have hh := rawPairEndpointLaw_upward e H ω x hκ U
  rwa [Measure.smul_apply,smul_eq_mul,Measure.map_apply hm hU] at hh

lemma pairUp_preserves_gap {d : ℕ} (e f : Direction d) (x : Lattice d × Lattice d) :
    signedCoordinate f ((pairUp e x).2-(pairUp e x).1) = signedCoordinate f (x.2-x.1) := by
  dsimp [pairUp]
  congr 1
  abel

noncomputable def upwardRetainedLaw {d : ℕ} (e f : Direction d) (H : ℕ) (z : ℝ)
    (π : Measure (Lattice d × Lattice d)) (ω : Environment d) (κ : ℝ≥0) :
    Measure (Lattice d × Lattice d) :=
  (κ : ℝ≥0∞)^2 • (retainedPairLaw (realPosition (step e)) f H z π ω).map (pairUp e)

lemma upwardRetainedLaw_le {d : ℕ} (e f : Direction d) (H : ℕ) (z : ℝ)
    (π : Measure (Lattice d × Lattice d)) (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y, κ ≤ (ω y).1 e) :
    upwardRetainedLaw e f H z π ω κ ≤ rawPairMixture (realPosition (step e)) (H+1) π ω := by
  apply le_trans _ (rawPairMixture_upward e H ω π hκ)
  intro U
  have hU := (Set.to_countable U).measurableSet
  simp only [upwardRetainedLaw,Measure.smul_apply,smul_eq_mul,
    Measure.map_apply (measurable_of_countable _) hU]
  exact mul_le_mul_right (retainedPairLaw_le _ _ _ _ _ _ _) _

lemma upwardRetainedLaw_mass {d : ℕ} (e f : Direction d) (H : ℕ) (z : ℝ)
    (π : Measure (Lattice d × Lattice d)) (ω : Environment d) (κ : ℝ≥0) :
    upwardRetainedLaw e f H z π ω κ Set.univ =
      (κ : ℝ≥0∞)^2 * pairKernelMass (realPosition (step e)) f H z π ω := by
  simp only [upwardRetainedLaw,Measure.smul_apply,smul_eq_mul,
    Measure.map_apply (measurable_of_countable _) MeasurableSet.univ,
    Set.preimage_univ,retainedPairLaw_mass]

lemma upwardRetainedLaw_support {d : ℕ} (e f : Direction d) (H : ℕ) (z : ℝ)
    (π : Measure (Lattice d × Lattice d)) (ω : Environment d) (κ : ℝ≥0) :
    ∀ᵐ y ∂upwardRetainedLaw e f H z π ω κ, z ≤ signedCoordinate f (y.2-y.1) := by
  unfold upwardRetainedLaw
  apply Measure.ae_smul_measure
  rw [ae_map_iff (measurable_of_countable _).aemeasurable (measurableSet_le measurable_const (measurable_of_countable _))]
  simpa only [pairUp_preserves_gap] using retainedPairLaw_support (realPosition (step e)) f H z π ω
end DirectionalTransience

end

end

end OAI
