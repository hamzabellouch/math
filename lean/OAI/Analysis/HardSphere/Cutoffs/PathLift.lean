import Mathlib
import OAI.Analysis.HardSphere.Cutoffs.DiameterTail

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

abbrev EuclideanPath := Fin 3 → C(Time,ℝ)
def IsPathLift {L : Length} (ω : ConfigurationPath 1 L) (ζ : EuclideanPath) : Prop :=
  ∀ j s, (ζ j s : AddCircle L.val)=ω s 0 j

lemma exists_pathLift {L : Length} (ω : ConfigurationPath 1 L) : ∃ ζ, IsPathLift ω ζ := by
  have hx (j : Fin 3) : ∃ ζ : C(Time,ℝ), ∀ s, (ζ s : AddCircle L.val)=ω s 0 j := by
    let γ : C(Time,AddCircle L.val) := ⟨fun s ↦ ω s 0 j, by fun_prop⟩
    let x : ℝ := ((AddCircle.equivIco L.val 0) (γ 0)).val
    have h0 : γ 0=(x : AddCircle L.val) := AddCircle.coe_equivIco.symm
    obtain ⟨ζ,hζ,_⟩ := (AddCircle.isCoveringMap_coe L.val).exists_path_lifts γ x h0
    exact ⟨ζ,fun s ↦ congrFun hζ s⟩
  choose ζ hζ using hx
  exact ⟨ζ,hζ⟩

lemma liftDiff_coe {L : Length} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) (j : Fin 3) (s q : Time) :
    ((ζ j s-ζ j q : ℝ) : AddCircle L.val)=ω s 0 j-ω q 0 j := by
  rw [AddCircle.coe_sub,hζ j s,hζ j q]

lemma liftDiff_lt_half_period {L : Length} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) (a b : Time) (hsmall : intervalDiameter a b ω < L.val/2)
    (j : Fin 3) (s q : Time) :
    |ζ j (intervalTime a b s)-ζ j (intervalTime a b q)| < L.val/2 := by
  by_contra h
  have hf : Continuous (fun v ↦ |ζ j (intervalTime a b v)-ζ j (intervalTime a b q)|) :=
    (((ζ j).continuous.comp (intervalTime_continuous a b)).sub continuous_const).abs
  obtain ⟨v,hv⟩ := intermediate_value_univ q s hf ⟨by simp; exact div_nonneg L.property.le (by norm_num),
    le_of_not_gt h⟩
  dsimp only at hv
  have ha : |ζ j (intervalTime a b v)-ζ j (intervalTime a b q)| ≤ |L.val|/2 := by
    rw [hv,abs_of_pos L.property]
  have he := (AddCircle.norm_coe_eq_abs_iff L.val L.property.ne').mpr ha
  rw [liftDiff_coe hζ,← dist_eq_norm,hv] at he
  have hb := (CellOrbital.dist_coord_le_torusDistance L (ω (intervalTime a b v) 0)
    (ω (intervalTime a b q) 0) j).trans (intervalDistance_le a b v q ω)
  linarith

lemma liftDiff_norm_eq {L : Length} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) (a b : Time) (hsmall : intervalDiameter a b ω < L.val/2)
    (j : Fin 3) (s q : Time) :
    dist (ω (intervalTime a b s) 0 j) (ω (intervalTime a b q) 0 j)=
      |ζ j (intervalTime a b s)-ζ j (intervalTime a b q)| := by
  have hle := (liftDiff_lt_half_period hζ a b hsmall j s q).le
  rw [← abs_of_pos L.property] at hle
  have he := (AddCircle.norm_coe_eq_abs_iff L.val L.property.ne').mpr hle
  simpa only [liftDiff_coe hζ,←dist_eq_norm] using he

def liftedDiameterMap (a b : Time) (ζ : EuclideanPath) : C(Time×Time,ℝ) :=
  ⟨fun p ↦ Real.sqrt (∑j, (ζ j (intervalTime a b p.1)-ζ j (intervalTime a b p.2))^2), by
    apply Real.continuous_sqrt.comp
    apply continuous_finsetSum
    intro j _
    exact (((ζ j).continuous.comp ((intervalTime_continuous a b).comp continuous_fst)).sub
      ((ζ j).continuous.comp ((intervalTime_continuous a b).comp continuous_snd))).pow 2⟩

def liftedDiameter (a b : Time) (ζ : EuclideanPath) : ℝ := ‖liftedDiameterMap a b ζ‖

lemma liftedDiameter_eq {L : Length} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) (a b : Time) (hsmall : intervalDiameter a b ω < L.val/2) :
    liftedDiameter a b ζ=intervalDiameter a b ω := by
  unfold liftedDiameter intervalDiameter
  congr 1
  ext p
  change Real.sqrt (∑j, (ζ j (intervalTime a b p.1)-ζ j (intervalTime a b p.2))^2)=
    torusDistance L _ _
  simp only [torusDistance,liftDiff_norm_eq hζ a b hsmall,sq_abs]

end HardSphere.PathCutoff

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

lemma intervalDiameter_le_lifted {L : Length} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) (a b : Time) : intervalDiameter a b ω ≤ liftedDiameter a b ζ := by
  apply intervalDiameter_le a b ω (norm_nonneg _)
  intro s q
  have hfirst : torusDistance L (ω (intervalTime a b s) 0) (ω (intervalTime a b q) 0) ≤
      liftedDiameterMap a b ζ (s,q) := by
    unfold torusDistance liftedDiameterMap
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro j _
    have hle : dist (ω (intervalTime a b s) 0 j) (ω (intervalTime a b q) 0 j) ≤
        |ζ j (intervalTime a b s)-ζ j (intervalTime a b q)| := by
      rw [dist_eq_norm,←liftDiff_coe hζ]
      exact QuotientAddGroup.norm_mk_le_norm
    have hh := pow_le_pow_left₀ dist_nonneg hle 2
    simpa only [sq_abs] using hh
  exact hfirst.trans ((le_abs_self _).trans (ContinuousMap.norm_coe_le_norm (liftedDiameterMap a b ζ) (s,q)))

lemma interval_small_iff_lifted_small {L : Length} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) (a b : Time) {R : ℝ} (hR : R < L.val/2) :
    intervalDiameter a b ω ≤ R ↔ liftedDiameter a b ζ ≤ R := by
  constructor
  · intro h
    rw [liftedDiameter_eq hζ a b (h.trans_lt hR)]
    exact h
  · exact fun h ↦ (intervalDiameter_le_lifted hζ a b).trans h

lemma intervalTime_assoc (a b c d s : Time) :
    intervalTime a b (intervalTime c d s)=intervalTime (intervalTime a b c) (intervalTime a b d) s := by
  apply Subtype.ext
  dsimp [intervalTime]
  ring

lemma meshSegment_lift {L : Length} {m : ℕ} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) (j : Fin m) :
    IsPathLift (meshSegment j ω) (fun k ↦ (ζ k).comp ⟨meshTime j,meshTime_continuous j⟩) := by
  intro k s
  exact hζ k _

end HardSphere.PathCutoff

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

lemma diameterRatio_reverse {L : Length} (r : ℝ) (ω : ConfigurationPath 1 L) :
    diameterRatio r (reverseConfigurationPath 1 L ω)=diameterRatio r ω := by
  unfold diameterRatio
  rw [intervalDiameter_reverse]
  simp [reverseTime]

lemma meshRegular_reverse {L : Length} (m : ℕ) (r R C : ℝ) (ω : ConfigurationPath 1 L) :
    MeshRegular m r R C (reverseConfigurationPath 1 L ω) ↔ MeshRegular m r R C ω := by
  unfold MeshRegular
  rw [mesh_sum_reverse _ (cubicCost_reverse r)]
  simp only [meshSegment_reverse,diameterRatio_reverse]
  constructor
  · rintro ⟨h,h'⟩
    exact ⟨fun j ↦ by simpa using h j.rev,h'⟩
  · rintro ⟨h,h'⟩
    exact ⟨fun j ↦ h j.rev,h'⟩

def EndpointRegular {L : Length} (u : Time) (S : ℝ) (ω : ConfigurationPath 1 L) : Prop :=
  intervalDiameter 0 u ω ≤ S ∧ intervalDiameter (reverseTime u) 1 ω ≤ S

def Regular {L : Length} (m : ℕ) (r R C : ℝ) (u : Time) (S : ℝ) (ω : ConfigurationPath 1 L) : Prop :=
  MeshRegular m r R C ω ∧ EndpointRegular u S ω

lemma regular_measurable {L : Length} (m : ℕ) (r R C : ℝ) (u : Time) (S : ℝ) :
    MeasurableSet {ω : ConfigurationPath 1 L | Regular m r R C u S ω} := by
  change MeasurableSet ({ω | MeshRegular m r R C ω} ∩
    ({ω | intervalDiameter 0 u ω ≤ S} ∩ {ω | intervalDiameter (reverseTime u) 1 ω ≤ S}))
  exact (meshRegular_measurable m r R C).inter
    ((measurableSet_le (intervalDiameter_continuous L 0 u).measurable measurable_const).inter
      (measurableSet_le (intervalDiameter_continuous L (reverseTime u) 1).measurable measurable_const))

lemma endpointRegular_reverse {L : Length} (u : Time) (S : ℝ) (ω : ConfigurationPath 1 L) :
    EndpointRegular u S (reverseConfigurationPath 1 L ω) ↔ EndpointRegular u S ω := by
  unfold EndpointRegular
  rw [intervalDiameter_reverse,intervalDiameter_reverse,reverseTime_reverse]
  simpa only [reverseTime_zero,reverseTime_one] using (and_comm : (_ ∧ _) ↔ (_ ∧ _))

lemma regular_reverse {L : Length} (m : ℕ) (r R C : ℝ) (u : Time) (S : ℝ) (ω : ConfigurationPath 1 L) :
    Regular m r R C u S (reverseConfigurationPath 1 L ω) ↔ Regular m r R C u S ω := by
  exact and_congr (meshRegular_reverse m r R C ω) (endpointRegular_reverse u S ω)

lemma mesh_lift_diameter {L : Length} {m : ℕ} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) {r R : ℝ} (hr : 0 < r) (hR : R*r < L.val/2)
    (hmax : ∀j : Fin m,diameterRatio r (meshSegment j ω) ≤ R) (j : Fin m) :
    liftedDiameter 0 1 (fun k ↦ (ζ k).comp ⟨meshTime j,meshTime_continuous j⟩)=
      intervalDiameter 0 1 (meshSegment j ω) := by
  apply liftedDiameter_eq (meshSegment_lift hζ j)
  exact ((div_le_iff₀ hr).mp (hmax j)).trans_lt hR

lemma regular_lifted_iff {L : Length} {m : ℕ} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) {r R C S : ℝ} (u : Time) (hr : 0 < r)
    (hR : R*r < L.val/2) (hS : S < L.val/2) :
    Regular m r R C u S ω ↔
    ((∀j : Fin m,liftedDiameter 0 1 (fun k ↦ (ζ k).comp ⟨meshTime j,meshTime_continuous j⟩)/r ≤ R) ∧
      (∑j : Fin m,(1+liftedDiameter 0 1 (fun k ↦ (ζ k).comp ⟨meshTime j,meshTime_continuous j⟩)/r)^3) ≤ C*(m:ℝ)) ∧
      (liftedDiameter 0 u ζ ≤ S ∧ liftedDiameter (reverseTime u) 1 ζ ≤ S) := by
  constructor
  · rintro ⟨⟨hm,ha⟩,hb⟩
    have he := mesh_lift_diameter hζ hr hR hm
    refine ⟨⟨?_,?_⟩,?_,?_⟩
    · simpa only [he,diameterRatio] using hm
    · simpa only [he,cubicCost,diameterRatio] using ha
    · exact (interval_small_iff_lifted_small hζ 0 u hS).mp hb.1
    · exact (interval_small_iff_lifted_small hζ (reverseTime u) 1 hS).mp hb.2
  · rintro ⟨⟨hm,ha⟩,hb⟩
    have ht : ∀j : Fin m,diameterRatio r (meshSegment j ω) ≤ R := fun j ↦
      (div_le_div_of_nonneg_right (intervalDiameter_le_lifted (meshSegment_lift hζ j) 0 1) hr.le).trans (hm j)
    have he := mesh_lift_diameter hζ hr hR ht
    refine ⟨⟨ht,?_⟩,?_,?_⟩
    · simpa only [he,cubicCost,diameterRatio] using ha
    · exact (interval_small_iff_lifted_small hζ 0 u hS).mpr hb.1
    · exact (interval_small_iff_lifted_small hζ (reverseTime u) 1 hS).mpr hb.2

lemma interval_prefix {L : Length} (u : Time) (ω : ConfigurationPath 1 L) :
    intervalDiameter 0 u ω=intervalDiameter 0 1 (configurationPrefix 1 L u ω) := by
  apply congrArg norm
  apply ContinuousMap.ext
  intro p
  change torusDistance L (ω (intervalTime 0 u p.1) 0) (ω (intervalTime 0 u p.2) 0)=
    torusDistance L (ω (prefixTime u (intervalTime 0 1 p.1)) 0) (ω (prefixTime u (intervalTime 0 1 p.2)) 0)
  have he (s : Time) : intervalTime 0 u s=prefixTime u (intervalTime 0 1 s) := by
    apply Subtype.ext
    simp [intervalTime,prefixTime,mul_comm]
  rw [he,he]

lemma interval_suffix {L : Length} (u : Time) (ω : ConfigurationPath 1 L) :
    intervalDiameter u 1 ω=intervalDiameter 0 1 (configurationSuffix 1 L u ω) := by
  apply congrArg norm
  apply ContinuousMap.ext
  intro p
  change torusDistance L (ω (intervalTime u 1 p.1) 0) (ω (intervalTime u 1 p.2) 0)=
    torusDistance L (ω (suffixTime u (intervalTime 0 1 p.1)) 0) (ω (suffixTime u (intervalTime 0 1 p.2)) 0)
  have he (s : Time) : intervalTime u 1 s=suffixTime u (intervalTime 0 1 s) := by
    apply Subtype.ext
    change (1-(s:ℝ))*(u:ℝ)+(s:ℝ)*1 = (u:ℝ)+(1-(u:ℝ))*((1-(s:ℝ))*0+(s:ℝ)*1)
    ring
  rw [he,he]

end HardSphere.PathCutoff

end
end

end

end OAI
