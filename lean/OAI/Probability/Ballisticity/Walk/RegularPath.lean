import Mathlib
import OAI.Probability.Ballisticity.Crossings.FirstLayerHitRecordIndexTime
import OAI.Probability.Ballisticity.Estimates.GaussianAbsTail

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def RegularPath {d : ℕ} (ℓ : Vector d) (x : Lattice d) : Set (Path d) :=
  {X | X 0 = x ∧ (∀ n, ∃ f, X (n+1) = X n+step f) ∧ X ∈ TransientPaths ℓ}

lemma measurableSet_regularPath {d : ℕ} (ℓ : Vector d) (x : Lattice d) :
    MeasurableSet (RegularPath ℓ x) := by
  apply (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
  apply MeasurableSet.inter _ (measurableSet_transientPaths ℓ)
  change MeasurableSet {X : Path d | ∀ n, ∃ f, X (n+1) = X n+step f}
  simp only [Set.ofPred_forall,Set.ofPred_exists]
  exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun f =>
    measurableSet_eq_fun (by fun_prop : Measurable (fun X : Path d => X (n+1)))
      (by fun_prop : Measurable (fun X : Path d => X n+step f))

lemma annealedFrom_regularPath {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (x : Lattice d) :
    ∀ᵐ X ∂annealedFrom ν x, X ∈ RegularPath ℓ x := by
  apply annealedFrom_ae_of_quenched ν x _ (measurableSet_regularPath ℓ x)
  filter_upwards [quenched_directionallyTransient_ae ν ℓ htrans] with ω hω
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x),hω x] with X h0 hnn ht
  exact ⟨h0,hnn,ht⟩

lemma sharedConditioned_regularPath {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (x y : Lattice d) :
    ∀ᵐ Z ∂sharedConditionedPairLaw ν ℓ x y,
      (Z.1 ∈ RegularPath ℓ x ∧ Z.1 ∈ NoDrop ℓ x) ∧
      (Z.2 ∈ RegularPath ℓ y ∧ Z.2 ∈ NoDrop ℓ y) := by
  have hh := shared_pair_ae ν x y _ _ (measurableSet_regularPath ℓ x) (measurableSet_regularPath ℓ y)
    (annealedFrom_regularPath ν ℓ htrans x) (annealedFrom_regularPath ν ℓ htrans y)
  filter_upwards [(sharedConditionedPairLaw_absolutelyContinuous ν ℓ x y).ae_le hh,
    sharedConditionedPairLaw_noDrop ν ℓ x y] with Z hZ hD
  exact ⟨⟨hZ.1,hD.1⟩,hZ.2,hD.2⟩

lemma conditionedFrom_regularPath {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (x : Lattice d) :
    ∀ᵐ X ∂conditionedFrom ν ℓ x, X ∈ RegularPath ℓ x ∧ X ∈ NoDrop ℓ x := by
  have hac : conditionedFrom ν ℓ x ≪ annealedFrom ν x :=
    Measure.smul_absolutelyContinuous.trans Measure.absolutelyContinuous_restrict
  have hD : ∀ᵐ X ∂conditionedFrom ν ℓ x, X ∈ NoDrop ℓ x := by
    exact Measure.smul_absolutelyContinuous.ae_le (ae_restrict_mem (measurableSet_noDrop ℓ x))
  have hR : ∀ᵐ X ∂conditionedFrom ν ℓ x, X ∈ RegularPath ℓ x :=
    hac.ae_le (annealedFrom_regularPath ν ℓ htrans x)
  exact hR.and hD

lemma open_lane_record_iff {d : ℕ} (e f : Direction d) (x : Lattice d) (X : Path d)
    (hX : X ∈ RegularPath (realPosition (step e)) x)
    (hD : X ∈ NoDrop (realPosition (step e)) x) {k : ℕ} (hk : 0 < k)
    (θ r a : ℝ) (hr : 0 < r) :
    X ∈ SurvivingLane {z | dot (realPosition x) (realPosition (step e)) ≤ dot (realPosition z) (realPosition (step e))}
      (Upper (realPosition (step e)) x k)
      {z | |signedCoordinate f z-(signedCoordinate f x+(k:ℝ)*θ)| < a*r} ↔
      |scaledRecordEndpoint (realPosition (step e)) f θ r k x X| < a := by
  rw [survivingLane_record_iff e x X hX.1 hD hX.2.1 hX.2.2 hk]
  change |signedCoordinate f (_+x)-(signedCoordinate f x+(k:ℝ)*θ)| < a*r ↔ _
  rw [signedCoordinate_add]
  have he (z : Lattice d) : signedCoordinate f z+signedCoordinate f x-(signedCoordinate f x+(k:ℝ)*θ) =
      signedCoordinate f z-(k:ℝ)*θ := by ring
  rw [he]
  simp only [scaledRecordEndpoint,abs_div,abs_of_pos hr]
  exact (div_lt_iff₀ hr).symm

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
