import OAI.GroupTheory.PolycyclicRecognition.Analysis.DynkinHaarConstruction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentCoordinatesInput
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinInput
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentExponentialSurjective

namespace OAI

/-! # Haar measure from nilpotent exponential coordinates

A global exponential homeomorphism and the finite BCH formula imply
Lebesgue invariance in every linear basis.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory LieModule Module
open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]

theorem NilpotentGlobalExponentialChartInput.toCoordinates
    (charts : NilpotentGlobalExponentialChartInput E G)
    (dynkin : NilpotentDynkinExpansionInput E G) :
    NilpotentExponentialCoordinatesInput E G := by
  intro Exp hExp hnil
  obtain ⟨chart, hchart⟩ := charts Exp hExp hnil
  refine ⟨⟨chart, hchart⟩, ?_⟩
  let L := GroupLieAlgebra (𝓘(ℝ, E)) G
  let : NormedAddCommGroup L := by
    change NormedAddCommGroup E
    exact inferInstance
  let : NormedSpace ℝ L := by
    change NormedSpace ℝ E
    exact inferInstance
  let : RealNormedLieAlgebra L :=
    { (inferInstance : NormedAddCommGroup L), (inferInstance : LieRing L),
      (inferInstance : NormedSpace ℝ L), (inferInstance : LieAlgebra ℝ L) with }
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : MeasurableSpace L := borel L
  let : BorelSpace L := ⟨rfl⟩
  obtain ⟨d, hd⟩ := (isNilpotent_iff ℝ _ _).mp hnil
  obtain ⟨coeff, _, hprod⟩ := dynkin Exp hExp d hd 2
  have hmul (x y : L) : chart x * chart y =
      chart (finiteDynkinPolynomial coeff ![x, y]) := by
    simpa only [hchart, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
      List.prod_nil, mul_one, Matrix.cons_val_zero, Matrix.cons_val_succ] using
      hprod ![x, y]
  intro n b
  let e := b.equivFun.symm.toContinuousLinearEquiv
  let μ : Measure L := Measure.map e volume
  let hμ : μ.IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  have hh := @dynkin_chart_map_isHaar L _
    (by change FiniteDimensional ℝ E; infer_instance) (borel L) ⟨rfl⟩ G _ _ _ _ _
    chart ((hchart 0).trans hExp.map_zero) _ coeff hmul _ hd μ hμ
  have hmap : Measure.map chart μ = Measure.map (Exp ∘ b.equivFun.symm) volume := by
    rw [Measure.map_map chart.measurable e.continuous.measurable]
    congr 1
    funext x
    exact hchart (b.equivFun.symm x)
  exact hmap ▸ hh

end PolycyclicRecognition

end

end OAI
