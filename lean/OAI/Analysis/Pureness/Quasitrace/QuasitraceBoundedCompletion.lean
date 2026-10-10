import OAI.Analysis.Pureness.Quasitrace.QuasitraceMetricContinuity

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace UniformSpace
open scoped Topology NNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)

structure MetricPoint (T : CuntzPureness.PositiveQuasitrace D)
    (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y) where
  val : D

instance metricPointPseudoMetric : PseudoMetricSpace (T.MetricPoint hadd) where
  dist x y := T.distance x.val y.val
  dist_self x := T.distance_self x.val
  dist_comm x y := T.distance_comm x.val y.val
  dist_triangle x y z := T.distance_triangle hadd x.val y.val z.val

def BoundedPoint (C : ℝ) := {x : T.MetricPoint hadd // ‖x.val‖ ≤ C}
instance boundedPointPseudoMetric (C : ℝ) : PseudoMetricSpace (T.BoundedPoint hadd C) :=
  inferInstanceAs (PseudoMetricSpace {x : T.MetricPoint hadd // ‖x.val‖ ≤ C})

abbrev BoundedCompletion (C : ℝ) := Completion (T.BoundedPoint hadd C)

def boundedStar (C : ℝ) (x : T.BoundedPoint hadd C) : T.BoundedPoint hadd C :=
  ⟨⟨star x.1.val⟩,by simpa only [norm_star] using x.2⟩
def boundedAdd (C E : ℝ) (x : T.BoundedPoint hadd C) (y : T.BoundedPoint hadd E) :
    T.BoundedPoint hadd (C+E) := ⟨⟨x.1.val+y.1.val⟩,(norm_add_le _ _).trans (add_le_add x.2 y.2)⟩
def boundedMul (C E : ℝ) (hC : 0 ≤ C) (x : T.BoundedPoint hadd C) (y : T.BoundedPoint hadd E) :
    T.BoundedPoint hadd (C*E) := ⟨⟨x.1.val*y.1.val⟩,
      (norm_mul_le _ _).trans (mul_le_mul x.2 y.2 (norm_nonneg _) hC)⟩

lemma boundedStar_isometry (C : ℝ) : Isometry (T.boundedStar hadd C) := by
  apply Isometry.of_dist_eq
  intro x y
  exact T.distance_star _ _
lemma boundedAdd_lipschitz (C E : ℝ) :
    LipschitzWith 2 (fun p : T.BoundedPoint hadd C × T.BoundedPoint hadd E =>
      T.boundedAdd hadd C E p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  change T.distance (p.1.1.val+p.2.1.val) (q.1.1.val+q.2.1.val) ≤
    (2:ℝ)*max (T.distance p.1.1.val q.1.1.val) (T.distance p.2.1.val q.2.1.val)
  exact (T.distance_add hadd _ _ _ _).trans (by
    linarith [le_max_left (T.distance p.1.1.val q.1.1.val) (T.distance p.2.1.val q.2.1.val),
      le_max_right (T.distance p.1.1.val q.1.1.val) (T.distance p.2.1.val q.2.1.val)])
lemma boundedMul_lipschitz (C E : ℝ) (hC : 0 ≤ C) (hE : 0 ≤ E) :
    LipschitzWith ⟨C^(2/3:ℝ)+E^(2/3:ℝ),by positivity⟩
      (fun p : T.BoundedPoint hadd C × T.BoundedPoint hadd E => T.boundedMul hadd C E hC p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  change T.distance (p.1.1.val*p.2.1.val) (q.1.1.val*q.2.1.val) ≤
    (C^(2/3:ℝ)+E^(2/3:ℝ))*max (T.distance p.1.1.val q.1.1.val) (T.distance p.2.1.val q.2.1.val)
  calc
    _ ≤ ‖p.1.1.val‖^(2/3:ℝ)*T.distance p.2.1.val q.2.1.val+
        ‖q.2.1.val‖^(2/3:ℝ)*T.distance p.1.1.val q.1.1.val := T.distance_mul hadd _ _ _ _
    _ ≤ C^(2/3:ℝ)*max (T.distance p.1.1.val q.1.1.val) (T.distance p.2.1.val q.2.1.val)+
        E^(2/3:ℝ)*max (T.distance p.1.1.val q.1.1.val) (T.distance p.2.1.val q.2.1.val) :=
      add_le_add
        (mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) p.1.2 (by norm_num)) (le_max_right _ _)
          (T.distance_nonneg _ _) (by positivity))
        (mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) q.2.2 (by norm_num)) (le_max_left _ _)
          (T.distance_nonneg _ _) (by positivity))
    _ = _ := by ring

def completedBoundedStar (C : ℝ) : T.BoundedCompletion hadd C → T.BoundedCompletion hadd C :=
  Completion.map (T.boundedStar hadd C)
def completedBoundedAdd (C E : ℝ) :
    T.BoundedCompletion hadd C → T.BoundedCompletion hadd E → T.BoundedCompletion hadd (C+E) :=
  Completion.map₂ (T.boundedAdd hadd C E)
def completedBoundedMul (C E : ℝ) (hC : 0 ≤ C) :
    T.BoundedCompletion hadd C → T.BoundedCompletion hadd E → T.BoundedCompletion hadd (C*E) :=
  Completion.map₂ (T.boundedMul hadd C E hC)

lemma completedBoundedStar_coe (C : ℝ) (x : T.BoundedPoint hadd C) :
    T.completedBoundedStar hadd C x = (T.boundedStar hadd C x : T.BoundedCompletion hadd C) :=
  Completion.map_coe (T.boundedStar_isometry hadd C).uniformContinuous x
lemma completedBoundedAdd_coe (C E : ℝ) (x : T.BoundedPoint hadd C) (y : T.BoundedPoint hadd E) :
    T.completedBoundedAdd hadd C E x y =
      (T.boundedAdd hadd C E x y : T.BoundedCompletion hadd (C+E)) := by
  exact Completion.map₂_coe_coe x y _ (T.boundedAdd_lipschitz hadd C E).uniformContinuous
lemma completedBoundedMul_coe (C E : ℝ) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (x : T.BoundedPoint hadd C) (y : T.BoundedPoint hadd E) :
    T.completedBoundedMul hadd C E hC x y =
      (T.boundedMul hadd C E hC x y : T.BoundedCompletion hadd (C*E)) := by
  exact Completion.map₂_coe_coe x y _ (T.boundedMul_lipschitz hadd C E hC hE).uniformContinuous
end CuntzPureness.PositiveQuasitrace

end

end OAI
