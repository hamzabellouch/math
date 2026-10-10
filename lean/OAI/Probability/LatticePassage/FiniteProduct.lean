import OAI.Probability.LatticePassage.EdgeInfluence
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset

abbrev LocalCoordinates (x : Vertex) (R : ℕ) := (e : ↥(localEdges x R)) → ℝ

noncomputable def extendLocalCoordinates (x : Vertex) (R : ℕ)
    (v : LocalCoordinates x R) : Environment := by
  classical
  exact fun e => if he : e ∈ localEdges x R then v ⟨e,he⟩ else 0

@[simp] lemma extendLocalCoordinates_apply (x : Vertex) (R : ℕ)
    (v : LocalCoordinates x R) (e : ↥(localEdges x R)) :
    extendLocalCoordinates x R v e = v e := by
  classical
  simp [extendLocalCoordinates, e.property]

@[fun_prop] lemma measurable_extendLocalCoordinates (x : Vertex) (R : ℕ) :
    Measurable (extendLocalCoordinates x R) := by
  classical
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ localEdges x R
  · simpa [extendLocalCoordinates, he] using (measurable_pi_apply (⟨e,he⟩ : ↥(localEdges x R)))
  · simp [extendLocalCoordinates, he]

noncomputable def finitePassageTime (x y : Vertex) (R : ℕ)
    (v : LocalCoordinates x R) : ℝ := localPassageTime (extendLocalCoordinates x R v) x y R

@[fun_prop] lemma measurable_finitePassageTime (x y : Vertex) (R : ℕ) :
    Measurable (finitePassageTime x y R) :=
  (measurable_localPassageTime x y R).comp (measurable_extendLocalCoordinates x R)

theorem finitePassageTime_restrict (x y : Vertex) (R : ℕ) (ω : Environment) :
    finitePassageTime x y R ((localEdges x R).restrict ω) = localPassageTime ω x y R := by
  apply localPassageTime_eq_of_agree
  intro e he
  exact extendLocalCoordinates_apply x R _ ⟨e,he⟩

theorem finitePassageTime_law (x y : Vertex) (R : ℕ) :
    Measure.map (localPassageTime · x y R) environmentLaw =
      Measure.map (finitePassageTime x y R)
        (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) := by
  rw [← Measure.infinitePi_map_restrict (fun _ : Edge => expMeasure 1),
    Measure.map_map (measurable_finitePassageTime x y R) (measurable_restrict _)]
  congr 1
  funext ω
  exact (finitePassageTime_restrict x y R ω).symm

theorem finitePassageTime_change_squared (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (v w : LocalCoordinates x R) :
    (finitePassageTime x y R v - finitePassageTime x y R w)^2 ≤
      (R : ℝ) * ∑ e : ↥(localEdges x R), (v e - w e)^2 := by
  have h := localPassageTime_change_squared (extendLocalCoordinates x R w)
    (extendLocalCoordinates x R v) x y R hR
  rw [← Finset.sum_attach (localEdges x R)] at h
  simpa only [finitePassageTime, extendLocalCoordinates_apply, Finset.attach_eq_univ] using h

theorem finitePassageTime_lipschitz (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) :
    LipschitzWith ⟨sqrt R, sqrt_nonneg _⟩
      (fun v : EuclideanSpace ℝ ↥(localEdges x R) => finitePassageTime x y R v) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [Real.dist_eq]
  have h := finitePassageTime_change_squared x y R hR v w
  have hd : dist v w ^ 2 = ∑ e : ↥(localEdges x R), (v e-w e)^2 := by
    rw [dist_eq_norm, EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  rw [← hd] at h
  have hs := sq_sqrt (show 0 ≤ (R : ℝ) by positivity)
  change _ ≤ sqrt R * dist v w
  nlinarith [sq_abs (finitePassageTime x y R v-finitePassageTime x y R w),
    abs_nonneg (finitePassageTime x y R v-finitePassageTime x y R w),
    mul_nonneg (sqrt_nonneg (R : ℝ)) (dist_nonneg (x := v) (y := w))]

end CompanionFPP

end OAI
