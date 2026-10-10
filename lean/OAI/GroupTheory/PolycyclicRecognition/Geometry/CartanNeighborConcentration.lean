import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborSamplingRow
import OAI.GroupTheory.PolycyclicRecognition.Analysis.AffineProfileConcentration

namespace OAI

/-! # Identical supported neighboring profiles give actual concentration -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]
  [Fintype I] [DecidableEq I]
  (π : G →* Multiplicative W)
  (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  (cell : Set W) (β : M.Bases)
  (X : I → H) {d : ℕ} (βD : WordBasisSelections X (boundedBracketWords d))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (pivot : Fin M.letterCount → H) (B δ : ℝ)
  (Profiles : Set C((Fin (finrank ℝ H) → ℝ), W))
  [MeasurableSpace Profiles] [BorelSpace Profiles] [BorelSpace (Profiles × Profiles)]
  [HasOuterApproxClosed (Profiles × Profiles)]
  [HereditarilyLindelofSpace (Profiles × Profiles)]
  {Λ : ℝ≥0}
  (D : NeighborSamplingRow T M F hunimod eW π bN cell β X βD
    haarN chartN hchartN pivot B δ Profiles (Λ := Λ))

omit [SecondCountableTopology F.N.carrier] in
/-- Portmanteau is applied to the original Haar samples, retaining the
actual neighboring law rather than replacing it by an abstract measure. -/
theorem NeighborSamplingRow.distance_tendsto_zero
    (Z : Set (Fin (finrank ℝ H) → ℝ)) [CompactSpace Z]
    (hpoints : ∀ f ∈ (D.law : Measure (Profiles × Profiles)).support,
      ∀ z ∈ Z, f.1.val z = f.2.val z)
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n => (M.translatedGroupBoxProbability T F hunimod eW
      haarN chartN hchartN bN cell β (D.scale n) (D.base n) : Measure F.N.carrier)
      {q | η ≤ dist ((D.profile n q).val.restrict Z)
        ((D.profile n (q * D.step n)).val.restrict Z)}) atTop (𝓝 0) := by
  let bad : Set (Profiles × Profiles) :=
    {f | η ≤ dist (f.1.val.restrict Z) (f.2.val.restrict Z)}
  have hcont : Continuous (fun f : Profiles × Profiles =>
      dist (f.1.val.restrict Z) (f.2.val.restrict Z)) :=
    ((ContinuousMap.continuous_restrict Z).comp
      (continuous_subtype_val.comp continuous_fst)).dist
      ((ContinuousMap.continuous_restrict Z).comp
        (continuous_subtype_val.comp continuous_snd))
  have hbad : IsClosed bad := isClosed_le continuous_const hcont
  have hc := measure_closed_tendsto_zero_of_support D.converges hbad (by
    intro f hf
    have heq : f.1.val.restrict Z = f.2.val.restrict Z := by
      ext z
      exact hpoints f hf z.val z.property
    change ¬η ≤ dist (f.1.val.restrict Z) (f.2.val.restrict Z)
    simpa only [heq, dist_self, not_le] using hη)
  apply hc.congr'
  filter_upwards [] with n
  have hm : Measurable (fun q => (D.profile n q, D.profile n (q * D.step n))) :=
    (D.measurable_profile n).prodMk
      ((D.measurable_profile n).comp (measurable_id.mul_const _))
  exact ProbabilityMeasure.map_apply'
    (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN bN
      cell β (D.scale n) (D.base n)) hm.aemeasurable hbad.measurableSet

end PolycyclicRecognition.CartanWordModel

end

end OAI
