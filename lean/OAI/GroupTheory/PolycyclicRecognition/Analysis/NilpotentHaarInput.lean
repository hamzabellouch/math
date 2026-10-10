import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBoxCoordinates
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

namespace OAI

/-! # Exponential-coordinate Haar measure

E. Le Donne, *Metric Lie Groups*, Graduate Texts in Mathematics 306,
Springer (2025), Theorem 9.4.7 (exponential coordinates) and Corollary 9.4.21.
https://doi.org/10.1007/978-3-031-98832-5_9

A global exponential chart identifies Haar measure on a simply connected
nilpotent Lie group with Lebesgue measure. The Euclidean determinant formula
then gives the volume of weighted boxes, including their scale factors.
-/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory
open scoped Manifold

variable (E G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

/-- The part of the nilpotent exponential-coordinate theorem needed for Haar
volume. The hypotheses concern the actual tangent Lie algebra of the group. -/
def NilpotentExponentialHaarInput [T2Space G] [SimplyConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] : Prop :=
  (LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G) →
    ∃ Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G, IsGroupExponential Exp) ∧
  ∀ (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G), IsGroupExponential Exp →
    LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G) →
    (∃ c : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G, ∀ x, c x = Exp x) ∧
    ∀ (n : ℕ) (b : Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)),
      (Measure.map (Exp ∘ b.equivFun.symm) volume).IsHaarMeasure

variable {E G} [T2Space G] [SimplyConnectedSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Normalize Haar measure using one exponential coordinate basis. -/
theorem exists_haar_exponential_cube_volume
    (haarInput : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {n : ℕ} (b : Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    ∃ (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (μ : Measure G),
      (∀ x, chart x = Exp x) ∧ μ.IsHaarMeasure ∧
      ∀ R : ℝ, 0 ≤ R → μ (exponentialCoordinateBox Exp b R) = ENNReal.ofReal (2 * R) ^ n := by
  obtain ⟨⟨chart, hchart⟩, hhaar⟩ := haarInput.2 Exp hExp hnil
  let f := Exp ∘ b.equivFun.symm
  let e : (Fin n → ℝ) ≃ₜ G :=
    b.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart
  have hf : f = e := by
    funext t
    exact (hchart (b.equivFun.symm t)).symm
  have hmeas : MeasurableEmbedding f := by rw [hf]; exact e.measurableEmbedding
  refine ⟨chart, Measure.map f volume, hchart, hhaar n b, ?_⟩
  intro R hR
  rw [exponentialCoordinateBox_eq_cube_image Exp b R hR]
  change (Measure.map f volume) (f '' _) = _
  rw [hmeas.map_apply, Set.preimage_image_eq _ hmeas.injective, Real.volume_Icc_pi]
  simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- An actual Haar measure with the exact exponential weighted-box formula.
All template dependence is in the already proved finite determinant sum. -/
theorem exists_haar_measure_model_weighted_boxes
    (haarInput : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (hnil : LieRing.IsNilpotent L)
    {I : Type*} (X : I → L) (S : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ μ : Measure G, μ.IsHaarMeasure ∧
      ∀ (cost : S → ℝ) (β : WordBasisSelections X S) (r R : ℝ), 0 ≤ R →
        μ (exponentialCoordinateBox (Exp ∘ e)
          (exponentialRescaleBasis (WordBasisSelections.basis X S β)
            (fun i => cost (β.val i)) r) R) =
        ENNReal.ofReal |(columnBasisMatrix (wordListCoordinates X S b₀) β.val).det| *
          ENNReal.ofReal (Real.exp (r * columnBasisWeight cost β.val)) *
            ENNReal.ofReal (2 * R) ^ finrank ℝ L := by
  have hnil' := e.nilpotent_iff_equiv_nilpotent.mp hnil
  obtain ⟨⟨c, hc⟩, hhaar⟩ := haarInput.2 Exp hExp hnil'
  let b := b₀.map e.toLinearEquiv
  let f := (Exp ∘ e) ∘ b₀.equivFun.symm
  let chart : (Fin (finrank ℝ L) → ℝ) ≃ₜ G :=
    b.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans c
  have hf' : f = Exp ∘ b.equivFun.symm := by
    funext t
    change Exp (e (b₀.equivFun.symm t)) = Exp ((b₀.map e.toLinearEquiv).equivFun.symm t)
    rw [Basis.map_equivFun]
    rfl
  have hf : f = chart := by
    rw [hf']
    funext t
    exact (hc (b.equivFun.symm t)).symm
  have hmeas : MeasurableEmbedding f := by
    rw [hf]
    exact chart.measurableEmbedding
  have hhaar' : (Measure.map f volume).IsHaarMeasure := by
    rw [hf']
    exact hhaar _ b
  refine ⟨Measure.map f volume, hhaar', ?_⟩
  intro cost β r R hR
  rw [exponentialCoordinateBox_eq_weighted_image X S b₀ β cost r R hR (Exp ∘ e)]
  change (Measure.map f volume) (f '' _) = _
  rw [hmeas.map_apply, Set.preimage_image_eq _ hmeas.injective]
  exact volume_weightedCoordinateBox _ _ _ _ _

end PolycyclicRecognition

end

end OAI
