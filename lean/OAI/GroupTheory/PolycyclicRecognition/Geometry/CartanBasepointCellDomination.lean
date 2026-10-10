import OAI.GroupTheory.PolycyclicRecognition.Analysis.CellProfileRestriction
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BasepointCellDomination
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxRadiusProbability
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorHaarInvariance

namespace OAI

/-! # Exact Haar domination for the changed Cartan sampling cell -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Set
open scoped Manifold ENNReal

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]

/-- The changed-center cell is dominated by independent smaller-cell and
conjugated-suffix sampling, with the exact factor `L ^ dim N`. -/
theorem exists_basepoint_groupBox_domination
    (hExp : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (r s : ℝ) {L : ℝ} (hL : 0 < L)
    (u : F.N.carrier) (d : F.D.carrier)
    (hcover : ∀ a₀ ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β s 1,
      ∀ a ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1,
      (F.action d a₀)⁻¹ * u⁻¹ * a ∈
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r L) :
    ∃ ν : ProbabilityMeasure F.N.carrier,
      (∀ᵐ k ∂(ν : Measure F.N.carrier), F.action d k ∈
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r L) ∧
      ∀ S : Set F.N.carrier, MeasurableSet S →
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β r 1 :
        Measure F.N.carrier) ((fun a => F.action d⁻¹ (u⁻¹ * a)) ⁻¹' S) ≤
      (ENNReal.ofReal L ^ finrank ℝ (cartanRootIdeal H)) *
        (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β s 1 :
          Measure F.N.carrier).prod (ν : Measure F.N.carrier) {p | p.1 * p.2 ∈ S} := by
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  let _ : μ.IsHaarMeasure := exponential_basis_measure_isHaar haarN F.N.equiv
    (cartanRootIdeal_nilpotent H T) F.ExpN F.isExpN b₀
  let A := M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β s 1
  let C := M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1
  let B := M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r L
  let μA := M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β s 1
  have hAp := M.groupBox_radius_properties T F hunimod eW haarN chartN hchartN b₀ E β s zero_lt_one
  have hCp := M.groupBox_radius_properties T F hunimod eW haarN chartN hchartN b₀ E β r zero_lt_one
  have hBp := M.groupBox_radius_properties T F hunimod eW haarN chartN hchartN b₀ E β r hL
  have hφ := F.action_preserves_haar T M hExp realize haarN haarD dynkinN hunimod μ
  have hA : ∀ᵐ a ∂(μA : Measure F.N.carrier), a ∈ A := by
    simpa only [μA, translatedGroupBoxProbability, mul_one, image_id'] using
      ae_mem_cellProbabilityMeasure μ A hAp.1 hAp.2.1 hAp.2.2.1
  obtain ⟨ν, hν, hd⟩ := exists_basepoint_cell_domination F.action μ hφ μA A hA C B
    hCp.1 hBp.1 hCp.2.1 hCp.2.2.1 hBp.2.1 hBp.2.2.1 u d hcover hBp.2.2.2.le
  refine ⟨ν, hν, ?_⟩
  intro S hS
  simpa only [μA, translatedGroupBoxProbability, mul_one, image_id'] using hd S hS

end PolycyclicRecognition.CartanWordModel

end

end OAI
