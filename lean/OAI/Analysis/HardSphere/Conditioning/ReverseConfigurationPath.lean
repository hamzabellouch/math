import Mathlib
import OAI.Analysis.HardSphere.Geometry.ConfigurationPath
import OAI.Analysis.HardSphere.Bridges.ReverseTime

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open Wiener
open scoped ComplexConjugate

def reverseConfigurationPath (N : ℕ) (L : Length) (ω : ConfigurationPath N L) :
    ConfigurationPath N L := ω.comp reverseTime

lemma reverseConfigurationPath_continuous (N : ℕ) (L : Length) :
    Continuous (reverseConfigurationPath N L) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ConfigurationPath N L × Time ↦ p.1 (reverseTime p.2))
  fun_prop

@[simp] lemma reverseConfigurationPath_apply (N : ℕ) (L : Length)
    (ω : ConfigurationPath N L) (s : Time) :
    reverseConfigurationPath N L ω s = ω (reverseTime s) := rfl

@[simp] lemma reverseConfigurationPath_reverse (N : ℕ) (L : Length)
    (ω : ConfigurationPath N L) :
    reverseConfigurationPath N L (reverseConfigurationPath N L ω) = ω := by
  ext s i j
  simp only [reverseConfigurationPath_apply,reverseTime_reverse]

lemma staysAllowed_reverse (N : ℕ) (L : Length) (a : ℝ) :
    reverseConfigurationPath N L ⁻¹' staysAllowed N L a = staysAllowed N L a := by
  ext ω
  change (Set.range (reverseConfigurationPath N L ω) ⊆ allowed N L a) ↔
    (Set.range ω ⊆ allowed N L a)
  have hr : Set.range (reverseConfigurationPath N L ω) = Set.range ω := by
    change Set.range (ω ∘ reverseTime) = Set.range ω
    exact (Function.Involutive.surjective reverseTime_reverse).range_comp ω
  rw [hr]

lemma coordinateReverse_preserving (N : ℕ) :
    MeasurePreserving (fun w : CoordinatePaths N ↦ fun p ↦ reverseIncrements (w p))
      (coordinateWiener N) (coordinateWiener N) := by
  refine ⟨Measurable.of_eval fun p ↦ reverseIncrements.continuous.measurable.comp (measurable_pi_apply p), ?_⟩
  unfold coordinateWiener
  rw [Measure.pi_map_pi (fun _ ↦ reverseIncrements.continuous.measurable.aemeasurable)]
  simp_rw [reverseIncrements_preserving.map_eq]

lemma reverse_freeTrajectory (N : ℕ) (L : Length) (t : ℝ) (w : CoordinatePaths N)
    (X : Configuration N L) :
    reverseConfigurationPath N L (freeTrajectory N L t w X) =
      freeTrajectory N L t (fun p ↦ reverseIncrements (w p))
        (freeTrajectory N L t w X 1) := by
  ext s i j
  change X i j + ((Real.sqrt (2*t)*w (i,j) (reverseTime s) : ℝ) : AddCircle L.val) =
    (X i j + ((Real.sqrt (2*t)*w (i,j) 1 : ℝ) : AddCircle L.val)) +
      ((Real.sqrt (2*t)*(w (i,j) (reverseTime s)-w (i,j) 1) : ℝ) : AddCircle L.val)
  rw [mul_sub,AddCircle.coe_sub]
  abel

lemma reverse_freePath_preserving (N : ℕ) (L : Length) (t : ℝ) :
    MeasurePreserving (reverseConfigurationPath N L) (freePathLaw N L t) (freePathLaw N L t) := by
  let : (volume : Measure (Torus L)).IsAddLeftInvariant := by
    rw [volume_pi]
    exact Measure.pi.isAddLeftInvariant _
  let : (volume : Measure (Configuration N L)).IsAddLeftInvariant := by
    rw [volume_pi]
    exact Measure.pi.isAddLeftInvariant _
  let : (volume : Measure (Configuration N L)).IsAddRightInvariant :=
    IsAddLeftInvariant.isAddRightInvariant
  have hm : Measurable (fun p : CoordinatePaths N × Configuration N L ↦
      freeTrajectory N L t p.1 p.2 1) :=
    ((freeTrajectory_continuous N L t).eval continuous_const).measurable
  have hskew := (coordinateReverse_preserving N).skew_product hm
    (Filter.Eventually.of_forall (fun w : CoordinatePaths N ↦
      map_add_right_eq_self (volume : Measure (Configuration N L))
        (fun i j ↦ ((Real.sqrt (2*t) * w (i,j) 1 : ℝ) : AddCircle L.val))))
  refine ⟨(reverseConfigurationPath_continuous N L).measurable, ?_⟩
  unfold freePathLaw
  rw [Measure.map_map (reverseConfigurationPath_continuous N L).measurable
    (freeTrajectory_continuous N L t).measurable]
  have heq : (reverseConfigurationPath N L ∘
      (fun p : CoordinatePaths N × Configuration N L ↦ freeTrajectory N L t p.1 p.2)) =
      (fun p : CoordinatePaths N × Configuration N L ↦ freeTrajectory N L t p.1 p.2) ∘
        (fun p ↦ (fun q ↦ reverseIncrements (p.1 q), freeTrajectory N L t p.1 p.2 1)) := by
    funext p
    exact reverse_freeTrajectory N L t p.1 p.2
  change MeasurePreserving
    (fun p : CoordinatePaths N × Configuration N L ↦
      (fun q ↦ reverseIncrements (p.1 q), freeTrajectory N L t p.1 p.2 1))
    ((coordinateWiener N).prod volume) ((coordinateWiener N).prod volume) at hskew
  rw [heq, ← Measure.map_map (freeTrajectory_continuous N L t).measurable hskew.measurable,
    hskew.map_eq]

lemma reverse_killedPath_preserving (N : ℕ) (L : Length) (a t : ℝ) :
    MeasurePreserving (reverseConfigurationPath N L) (killedPathLaw N L a t)
      (killedPathLaw N L a t) := by
  refine ⟨(reverseConfigurationPath_continuous N L).measurable,?_⟩
  unfold killedPathLaw
  conv_rhs => rw [← (reverse_freePath_preserving N L t).map_eq]
  rw [Measure.restrict_map (reverseConfigurationPath_continuous N L).measurable
    (staysAllowed_open N L a).measurableSet, staysAllowed_reverse]

def reversePathEquiv (N : ℕ) (L : Length) : ConfigurationPath N L ≃ᵐ ConfigurationPath N L where
  toFun := reverseConfigurationPath N L
  invFun := reverseConfigurationPath N L
  left_inv := reverseConfigurationPath_reverse N L
  right_inv := reverseConfigurationPath_reverse N L
  measurable_toFun := (reverseConfigurationPath_continuous N L).measurable
  measurable_invFun := (reverseConfigurationPath_continuous N L).measurable

lemma killedTransition_selfAdjoint (N : ℕ) (L : Length) (a t : ℝ) :
    IsSelfAdjoint (killedTransition N L a t) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℂ (killedTransition N L a t f) g = inner ℂ f (killedTransition N L a t g)
  rw [← inner_conj_symm, killedTransition_pairing, ← integral_conj, killedTransition_pairing]
  have h := (reverse_killedPath_preserving N L a t).integral_comp
    (reversePathEquiv N L).measurableEmbedding
    (fun ω : ConfigurationPath N L ↦ conj (f (ω 0)) * g (ω 1))
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [map_mul,starRingEnd_self_apply,reverseConfigurationPath_apply,reverseTime_zero,
    reverseTime_one]
  ring

end HardSphere

end

end OAI
