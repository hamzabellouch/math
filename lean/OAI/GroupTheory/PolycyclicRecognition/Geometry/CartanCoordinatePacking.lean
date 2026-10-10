import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWordModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialSubsetVolume
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SubgroupPacking

namespace OAI

/-! # Separated counts for arbitrary good coordinate subsets

The coordinate Haar measure and the closed root-factor embedding give a
single finite packing constant. Every subset of a bounded rescaled chart
has its determinant volume bounded by the cardinality of an actual
ambient separated net. The subset need not itself be measurable.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set
open scoped Manifold ENNReal

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

omit [SimplyConnectedSpace G] in
include T in
/-- A uniform ambient separated count for any bounded coordinate subset
in an actual rescaled word basis. -/
theorem exists_coordinate_subset_packing
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (cost : M.wordList → ℝ) (β : M.Bases) (r R : ℝ)
      (S : Set (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)), S ⊆ closedBall 0 R →
      let b := exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => cost (β.val j)) r
      ∃ t : Finset G,
        (↑t : Set G) ⊆ (fun y => F.inclusionN (F.ExpN (F.N.equiv (b.equivFun.symm y)))) '' S ∧
        (∀ x ∈ t, ∀ y ∈ t, x ≠ y → ρ < dist x y) ∧
        ENNReal.ofReal |(columnBasisMatrix (wordListCoordinates M.letter M.wordList b₀) β.val).det| *
          ENNReal.ofReal (Real.exp (r * columnBasisWeight cost β.val)) * volume S ≤
            (t.card : ℝ≥0∞) * C := by
  classical
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let _ : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  obtain ⟨⟨chart, hc⟩, hhaar⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  have heq : ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) =
      F.ExpN ∘ (b₀.map F.N.equiv.toLinearEquiv).equivFun.symm := by
    funext y
    rw [Basis.map_equivFun]
    rfl
  have hμ : μ.IsHaarMeasure := by
    dsimp only [μ]
    rw [heq]
    exact hhaar _ (b₀.map F.N.equiv.toLinearEquiv)
  let : μ.IsHaarMeasure := hμ
  refine ⟨μ (F.inclusionN ⁻¹' closedBall (1 : G) ρ),
    fixedSlice_packing_constant_lt_top F.inclusionN μ F.closedN ρ, ?_⟩
  intro cost β r R S hS b
  let f := (F.ExpN ∘ F.N.equiv) ∘ b.equivFun.symm
  let c : (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ≃ₜ F.N.carrier :=
    (b.map F.N.equiv.toLinearEquiv).equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart
  have hf : f = c := by
    funext y
    dsimp only [f, c, Function.comp_apply, Homeomorph.trans_apply,
      ContinuousLinearEquiv.coe_toHomeomorph, LinearEquiv.coe_toContinuousLinearEquiv]
    rw [hc, Basis.map_equivFun]
    rfl
  have hcompact : IsCompact (f '' closedBall 0 R) :=
    (isCompact_closedBall _ _).image (hf ▸ c.continuous)
  obtain ⟨t, ht, hsep, hmass⟩ := exists_subgroup_separated_net F.inclusionN μ F.closedN.continuous
    hcompact (image_mono hS) hρ
  refine ⟨t, ?_, hsep, ?_⟩
  · simpa only [← image_comp, Function.comp_def, f] using ht
  · rw [exponential_rescaled_subset_measure F.N.equiv F.ExpN chart hc M.letter M.wordList
      b₀ β cost r S] at hmass
    exact hmass

end PolycyclicRecognition.CartanWordModel

end

end OAI
