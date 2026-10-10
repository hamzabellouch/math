import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorHaarInvariance
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TupleFixedSlicePacking
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NormalizedTuplePacking

namespace OAI

/-! # Actual target tuple counts from source Cartan-fiber volume -/

noncomputable section
namespace PolycyclicRecognition.CartanFactorModel

open Module LieAlgebra MeasureTheory Set Filter
open scoped Manifold NNReal Topology

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

include T M in
theorem exists_target_source_tuple_count {h : ℕ}
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (hunimod : ∀ z : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ z) = 0)
    (μ : Measure F.N.carrier) [μ.IsHaarMeasure]
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) (p : ℕ → NormalizedPair G Λ)
    {scale : ℕ → ℝ} (hs : Tendsto scale atTop atTop)
    (x : ℕ → G) (d : ℕ → F.D.carrier)
    (S : ℕ → Set (Fin h → F.N.carrier)) (hS : ∀ n, IsCompact (S n))
    {b : ℝ} (hvol : HasSubexponentialLowerBoundSeq scale
      (fun n => ((Measure.pi fun _ : Fin h => μ) (S n)).toReal / Real.exp (scale n * b))) :
    ∃ t : ℕ → Finset (Fin h → G),
      (∀ n, (↑(t n) : Set (Fin h → G)) ⊆
        (fun u => fun i => (p n).val.1 (x n * F.inclusionN (u i) * F.inclusionD (d n))) '' S n) ∧
      (∀ n, ∀ u ∈ t n, ∀ v ∈ t n, u ≠ v → 1 ≤ dist u v) ∧
      HasSubexponentialLowerBoundSeq scale
        (fun n => ((t n).card : ℝ) / Real.exp (scale n * b)) := by
  classical
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  let : SecondCountableTopology F.N.carrier := F.closedN.isEmbedding.secondCountableTopology
  let : LocallyCompactSpace F.N.carrier := F.closedN.locallyCompactSpace
  obtain ⟨u, hu, hsep, hcount⟩ := exists_tuple_fixedSlice_count_rate
    F.inclusionN F.inclusionD F.action μ
    (F.action_preserves_haar T M hExp realize haarN haarD dynkinN hunimod μ)
    F.conjugation F.closedN hs (fun n _ => x n) (fun n _ => d n) S hS hvol
    (show 0 < (Λ : ℝ) * ((Λ : ℝ) + 1) by positivity)
  let t := fun n => (u n).image (fun v i => (p n).val.1 (v i))
  obtain ⟨htsep, htcount⟩ := normalizedPair_tuple_count_rate p hΛ u hsep hcount
  refine ⟨t, ?_, htsep, htcount⟩
  intro n y hy
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨w, hw, rfl⟩ := hu n hv
  exact ⟨w, hw, rfl⟩

end PolycyclicRecognition.CartanFactorModel

end

end OAI
