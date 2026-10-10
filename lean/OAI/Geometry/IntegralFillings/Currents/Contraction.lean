import Mathlib
import OAI.Geometry.IntegralFillings.Currents.BoundaryMass

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

namespace SharpIntegralFillings
open Set MeasureTheory Filter

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {k : ℕ}
noncomputable def contractCurrent (u : X → ℝ) (T : Functional X (k+1)) : Functional X k :=
  fun b π => if Admissible b π then T b (Matrix.vecCons u π) else 0

omit [MeasurableSpace X] in
lemma contractCurrent_apply (u : X → ℝ) (T : Functional X (k+1))
    {b : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible b π) :
    contractCurrent u T b π = T b (Matrix.vecCons u π) := ite_eq_left h

lemma contractCurrent_controls {T : Functional X (k+1)} (hT : IsMetricCurrent T)
    {μ : Measure X} (hμ : Controls T μ) {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    Controls (contractCurrent u T) (K • μ) := by
  intro b π hb hπ
  rw [contractCurrent_apply _ _ ⟨hb,fun i => ⟨1,hπ i⟩⟩,integral_smul_nnreal_measure]
  have h := hT.mass_bound hμ hb (Matrix.vecCons K (fun _ => 1))
    (show ∀ i, LipschitzWith (Matrix.vecCons K (fun _ => 1) i) (Matrix.vecCons u π i) from
      fun i => Fin.cases hu (fun j => hπ j) i)
  simpa [Fin.prod_univ_succ,NNReal.smul_def] using h

lemma contractCurrent_isMetricCurrent {T : Functional X (k+1)} (hT : IsMetricCurrent T)
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) : IsMetricCurrent (contractCurrent u T) := by
  have hcons {b : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible b π) :
      Admissible b (Matrix.vecCons u π) :=
    ⟨h.1,fun i => Fin.cases ⟨K,hu⟩ (fun j => h.2 j) i⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro b π hab
    exact ite_eq_right hab
  · intro b c π a d hb hc hπ
    rw [contractCurrent_apply _ _ ⟨(hb.const_mul a).add (hc.const_mul d),hπ⟩,
      contractCurrent_apply _ _ ⟨hb,hπ⟩,contractCurrent_apply _ _ ⟨hc,hπ⟩]
    exact hT.linearFirst b c _ a d hb hc (hcons ⟨hb,hπ⟩).2
  · intro b π i f a d hab hf
    have had : ∃ L : ℝ≥0, LipschitzWith L (fun x => a*π i x+d*f x) := by
      obtain ⟨L,hL⟩ := hab.2 i
      obtain ⟨J,hJ⟩ := hf
      exact ⟨_,(lipschitz_mul_real hL a).add (lipschitz_mul_real hJ d)⟩
    have hup {g : X → ℝ} (hg : ∃ L : ℝ≥0, LipschitzWith L g) :
        Admissible b (Function.update π i g) := by
      refine ⟨hab.1,fun j => ?_⟩
      by_cases hji : j = i
      · simpa [hji] using hg
      · simpa [Function.update_of_ne hji] using hab.2 j
    rw [contractCurrent_apply _ _ (hup had),contractCurrent_apply _ _ hab,
      contractCurrent_apply _ _ (hup hf)]
    simpa only [vecCons_update_tail,Matrix.cons_val_succ] using
      hT.linearCoord b (Matrix.vecCons u π) i.succ f a d (hcons hab) hf
  · intro b π πs hb hLip hpt
    choose L hL using hLip
    have hπ (i) : LipschitzWith (L i) (π i) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      exact le_of_tendsto ((hpt i x).dist (hpt i y))
        (Eventually.of_forall fun j => (hL i j).dist_le_mul x y)
    have hab : Admissible b π := ⟨hb,fun i => ⟨L i,hπ i⟩⟩
    have habs j : Admissible b (πs j) := ⟨hb,fun i => ⟨L i,hL i j⟩⟩
    simp only [contractCurrent,ite_eq_left hab,ite_eq_left (habs _)]
    apply hT.sequentialContinuity _ _ _ hb
    · intro i
      exact Fin.cases ⟨K,fun _ => hu⟩ (fun j => ⟨L j,hL j⟩) i
    · intro i x
      exact Fin.cases tendsto_const_nhds (fun j => hpt j x) i
  · intro b π hab hloc
    rw [contractCurrent_apply _ _ hab]
    obtain ⟨i,U,c,hU,hb,hc⟩ := hloc
    exact hT.locality _ _ (hcons hab) ⟨i.succ,U,c,hU,hb,hc⟩
  · obtain ⟨μ,hfin,hμ⟩ := hT.finiteMass
    let : IsFiniteMeasure μ := hfin
    exact ⟨K • μ,inferInstance,contractCurrent_controls hT hμ hu⟩

omit [MeasurableSpace X] in
lemma contractCurrent_boundary_cycle {T : Functional X (k+2)} {u : X → ℝ}
    (hu : BoundedLip u) (hz : boundarySucc T = 0) : boundarySucc (contractCurrent u T) = 0 := by
  funext b π
  by_cases hab : Admissible b π
  · have hcons : Admissible (fun _ : X => (1:ℝ)) (Matrix.vecCons b π) :=
      ⟨BoundedLip.const 1,fun i => Fin.cases hab.1.1 (fun j => hab.2 j) i⟩
    rw [boundarySucc,ite_eq_left hab,contractCurrent_apply _ _ hcons]
    have hz' := congrFun (congrFun hz u) (Matrix.vecCons b π)
    rw [boundarySucc,ite_eq_left ⟨hu,fun i => Fin.cases hab.1.1 (fun j => hab.2 j) i⟩] at hz'
    exact hz'
  · simp [boundarySucc,hab]

end SharpIntegralFillings

end

end OAI
