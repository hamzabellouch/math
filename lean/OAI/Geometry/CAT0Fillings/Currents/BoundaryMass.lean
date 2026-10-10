import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.LevelLocality

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter

lemma vecCons_update_head {α : Type*} {k : ℕ} (b f : α) (π : Fin k → α) :
    Function.update (Matrix.vecCons b π) 0 f = Matrix.vecCons f π := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

lemma vecCons_update_tail {α : Type*} {k : ℕ} (b : α) (π : Fin k → α) (i : Fin k) (f : α) :
    Matrix.vecCons b (Function.update π i f) = Function.update (Matrix.vecCons b π) i.succ f := by
  funext j
  refine Fin.cases ?_ (fun l => ?_) j
  · rw [Function.update_of_ne (Fin.succ_ne_zero i).symm]; rfl
  · by_cases h : l = i <;> simp [h]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {k : ℕ}

omit [BorelSpace X] in

lemma boundary_isMetricCurrent_of_finiteMass {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hrect : IntegerRectifiable T)
    (hm : ∃ μ : Measure X, IsFiniteMeasure μ ∧ Controls (boundarySucc T) μ) :
    IsMetricCurrent (boundarySucc T) := by
  classical
  have hcons {b : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible b π) :
      Admissible (fun _ : X => (1:ℝ)) (Matrix.vecCons b π) :=
    ⟨BoundedLip.const 1,fun i => Fin.cases h.1.1 (fun j => h.2 j) i⟩
  refine ⟨?_,?_,?_,?_,hrect.boundary_locality,hm⟩
  · intro b π hab
    exact ite_eq_right hab
  · intro b c π a d hb hc hπ
    rw [boundarySucc,ite_eq_left ⟨(hb.const_mul a).add (hc.const_mul d),hπ⟩,
      boundarySucc,ite_eq_left ⟨hb,hπ⟩,boundarySucc,ite_eq_left ⟨hc,hπ⟩]
    simpa only [vecCons_update_head,Matrix.cons_val_zero] using
      hT.linearCoord (fun _ => 1) (Matrix.vecCons b π) 0 c a d (hcons ⟨hb,hπ⟩) hc.1
  · intro b π i f a d hab hf
    have had : ∃ K : ℝ≥0, LipschitzWith K (fun x => a*π i x+d*f x) := by
      obtain ⟨L,hL⟩ := hab.2 i
      obtain ⟨K,hK⟩ := hf
      exact ⟨_,(lipschitz_mul_real hL a).add (lipschitz_mul_real hK d)⟩
    have hup {g : X → ℝ} (hg : ∃ K : ℝ≥0, LipschitzWith K g) :
        Admissible b (Function.update π i g) := by
      refine ⟨hab.1,fun j => ?_⟩
      by_cases hji : j = i
      · simpa [hji] using hg
      · simpa [Function.update_of_ne hji] using hab.2 j
    rw [boundarySucc,ite_eq_left (hup had),boundarySucc,ite_eq_left hab,
      boundarySucc,ite_eq_left (hup hf)]
    simpa only [vecCons_update_tail,Matrix.cons_val_succ] using
      hT.linearCoord (fun _ => 1) (Matrix.vecCons b π) i.succ f a d (hcons hab) hf
  · intro b π πs hb hLip hpt
    choose K hK using hLip
    have hπ (i) : LipschitzWith (K i) (π i) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      exact le_of_tendsto ((hpt i x).dist (hpt i y))
        (Eventually.of_forall fun j => (hK i j).dist_le_mul x y)
    have hab : Admissible b π := ⟨hb,fun i => ⟨K i,hπ i⟩⟩
    have habs j : Admissible b (πs j) := ⟨hb,fun i => ⟨K i,hK i j⟩⟩
    simp only [boundarySucc,ite_eq_left hab,ite_eq_left (habs _)]
    apply hT.sequentialContinuity _ _ _ (BoundedLip.const 1)
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · obtain ⟨L,hL⟩ := hb.1
        exact ⟨L,fun _ => hL⟩
      · exact ⟨K j,hK j⟩
    · intro i x
      exact Fin.cases tendsto_const_nhds (fun j => hpt j x) i


open Set MeasureTheory Filter

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {k : ℕ}

end CAT0Fillings
end

end OAI
