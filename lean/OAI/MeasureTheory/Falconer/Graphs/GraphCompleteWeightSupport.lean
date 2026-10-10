import OAI.MeasureTheory.Falconer.Angular.GraphRotatedWeights

namespace OAI

namespace PlanarFalconer
open Set
open scoped ComplexConjugate

def graphSourceSign (distance plus : Bool) : ℝ :=
  if distance then 1 else if plus then 1 else -1

theorem graphSourceSign_cases (distance plus : Bool) :
    graphSourceSign distance plus = 1 ∨ graphSourceSign distance plus = -1 := by
  cases distance <;> cases plus <;> norm_num [graphSourceSign]

noncomputable def graphSourceBinDirection (distance : Bool) (axis : ℝ)
    (u : UnitCircle) : UnitCircle := if distance then sourceCircleRotate (-axis) u else u

theorem graphSourceBinDirection_continuous (distance : Bool) (axis : ℝ) :
    Continuous (graphSourceBinDirection distance axis) := by
  cases distance
  · exact continuous_id
  · exact (sourceCircleRotate_isometry (-axis)).continuous

theorem graphSourceBinDirection_dist (distance : Bool) (axis : ℝ) (u v : UnitCircle) :
    dist (graphSourceBinDirection distance axis u) (graphSourceBinDirection distance axis v) = dist u v := by
  cases distance
  · rfl
  · exact sourceCircleRotate_dist (-axis) u v

theorem graphSourceWeight_support_bins (distance plus : Bool) (axis : ℝ) (n j k : ℕ) :
    tsupport (graphSourceWeight distance plus axis n j k) ⊆
      {p | graphSourceBinDirection distance axis p.1 ∈ tsupport (circleAngularBin n j) ∧
        graphSourceBinDirection distance axis p.2 ∈ tsupport (circleAngularBin n k)} := by
  apply closure_minimal
  · intro p hp
    constructor
    · apply subset_closure
      intro hz
      apply hp
      cases distance <;> simp_all [graphSourceWeight, graphSourceBinDirection,
        graphRotatedDistanceWeight, graphDistanceWeight, graphProductWeight, graphBinWeight]
    · apply subset_closure
      intro hz
      apply hp
      cases distance <;> simp_all [graphSourceWeight, graphSourceBinDirection,
        graphRotatedDistanceWeight, graphDistanceWeight, graphProductWeight, graphBinWeight]
  · exact (isClosed_closure.preimage ((graphSourceBinDirection_continuous distance axis).comp continuous_fst)).inter
      (isClosed_closure.preimage ((graphSourceBinDirection_continuous distance axis).comp continuous_snd))

theorem graphSourceWeight_support_nondegenerate (distance plus : Bool) (axis : ℝ) (n j k : ℕ) :
    tsupport (graphSourceWeight distance plus axis n j k) ⊆
      {p | 1/2 ≤ ‖(p.1:Plane)+graphSourceSign distance plus • (p.2:Plane)‖} := by
  apply closure_minimal
  · intro p hp
    cases distance
    · have hs : p ∈ tsupport (circleGraphSignWeight (graphSourceSign false plus)) := by
        apply subset_closure
        intro hz
        apply hp
        cases plus <;> simp_all [graphSourceWeight, graphSourceSign, circleGraphSignWeight, graphProductWeight]
        norm_num at hz
        exact hp.2 hz
      exact circleGraphSignWeight_nondegenerate _ (graphSourceSign_cases false plus) hs
    · have he : graphRotatedDistanceWeight axis n j k p ≠ 0 := hp
      rw [graphRotatedDistanceWeight_eq] at he
      have hu : sourceConeCircle axis p.1 ≠ 0 := by intro hz; exact he (by simp [hz])
      have hv : sourceConeCircle axis p.2 ≠ 0 := by intro hz; exact he (by simp [hz])
      have hb := sourceConeCircle_plus_nondegenerate axis p.1 p.2 (subset_closure hu) (subset_closure hv)
      change 1/2 ≤ ‖(p.1:Plane)+(1:ℝ) • (p.2:Plane)‖
      simpa only [one_smul] using (by norm_num : (1/2:ℝ) ≤ 6/5).trans hb
  · exact isClosed_le continuous_const (by fun_prop)

theorem graphSourceWeight_complete_representative {δ : ℝ} (hδ : 0 < δ) (hcap : δ ≤ 2*Real.pi)
    (distance plus : Bool) (axis : ℝ) (j k : ℕ)
    (hS : (tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k)).Nonempty) :
    ∃ q ∈ tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k),
      ∀ p ∈ tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k),
      |graphChartZ (p.1:Plane) (graphSourceSign distance plus • (p.2:Plane))-
        graphChartZ (q.1:Plane) (graphSourceSign distance plus • (q.2:Plane))|+
      dist (graphChartAxis (p.1:Plane) (graphSourceSign distance plus • (p.2:Plane)))
        (graphChartAxis (q.1:Plane) (graphSourceSign distance plus • (q.2:Plane))) ≤ 112*δ := by
  have hb := graphSourceWeight_support_bins distance plus axis (angularBinCount δ) j k
  have hv := graph_complete_support_representative _ (4*δ) (graphSourceSign_cases distance plus) _ hS
    (graphSourceWeight_support_nondegenerate distance plus axis (angularBinCount δ) j k) ?_
  · convert hv using 1
    ring_nf
  · intro p hp q hq
    have h₁ := circleAngularBin_scale_diameter hδ hcap j (hb hp).1 (hb hq).1
    have h₂ := circleAngularBin_scale_diameter hδ hcap k (hb hp).2 (hb hq).2
    rw [graphSourceBinDirection_dist] at h₁ h₂
    exact ⟨h₁,h₂⟩

end PlanarFalconer

end OAI
