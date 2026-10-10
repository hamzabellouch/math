import OAI.Analysis.FiniteFactor.CrossedProduct.UncappedPairIdentity

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

@[simp] theorem sourceTorusRotate_zero (θ : SourceCoordinate → ℝ) (z : SourceTorus) :
    sourceTorusRotate θ 0 z = z := by
  funext i
  simp [sourceTorusRotate]

theorem sourceTorusRotate_add (θ : SourceCoordinate → ℝ) (n m : ℤ) (z : SourceTorus) :
    sourceTorusRotate θ n (sourceTorusRotate θ m z) = sourceTorusRotate θ (n+m) z := by
  funext i
  simp only [sourceTorusRotate, add_zsmul]
  abel

theorem sourceTorusRotate_preserving (θ : SourceCoordinate → ℝ) (n : ℤ) :
    MeasurePreserving (sourceTorusRotate θ n) sourceTorusHaar sourceTorusHaar := by
  have he : sourceTorusRotate θ n =
      sourceTorusQuotient ∘ coordinateRotate θ n ∘ sourceTorusRepresentative := by
    funext z
    simp only [Function.comp_def,sourceTorusQuotient_rotate,sourceTorusQuotient_representative]
  rw [he]
  exact sourceTorusQuotient_preserving.comp
    ((coordinateRotate_preserving θ n).comp sourceTorusRepresentative_preserving)

theorem exists_source_invariant_conull (θ : SourceCoordinate → ℝ)
    (P : SourceTorus → Prop) (hP : ∀ᵐ z ∂sourceTorusHaar, P z) :
    ∃ Q : Set SourceTorus, MeasurableSet Q ∧ (∀ᵐ z ∂sourceTorusHaar, z ∈ Q) ∧
      (∀ z ∈ Q, P z) ∧ (∀ n : ℤ, ∀ z ∈ Q, sourceTorusRotate θ n z ∈ Q) := by
  let B : Set SourceTorus := (toMeasurable sourceTorusHaar {z | ¬ P z})ᶜ
  have hB : MeasurableSet B := (measurableSet_toMeasurable _ _).compl
  have hBa : ∀ᵐ z ∂sourceTorusHaar, z ∈ B := by
    rw [ae_iff] at hP ⊢
    simpa [B,measure_toMeasurable] using hP
  let Q : Set SourceTorus := ⋂ n : ℤ, (sourceTorusRotate θ n) ⁻¹' B
  refine ⟨Q,MeasurableSet.iInter (fun n => hB.preimage (sourceTorusRotate_continuous θ n).measurable),?_,?_,?_⟩
  · have hall := ae_all_iff.mpr (fun n : ℤ => (sourceTorusRotate_preserving θ n).quasiMeasurePreserving.ae hBa)
    simpa only [Q,Set.mem_iInter,Set.mem_preimage] using hall
  · intro z hz
    have hb : z ∈ B := by simpa using Set.mem_iInter.mp hz 0
    by_contra hn
    exact hb (subset_toMeasurable sourceTorusHaar _ hn)
  · intro n z hz
    apply Set.mem_iInter.mpr
    intro m
    change sourceTorusRotate θ m (sourceTorusRotate θ n z) ∈ B
    rw [sourceTorusRotate_add]
    exact Set.mem_iInter.mp hz (m+n)

/-- A single invariant Borel conull set for the fixed original projection:
finite cocycles, actual projection fields, all covariance entries and all
ordered orbit identities hold at every point of the set. -/
theorem sourceProjection_common_conull (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0) :
    ∃ Q : Set SourceTorus, MeasurableSet Q ∧ (∀ᵐ z ∂sourceTorusHaar, z ∈ Q) ∧
      (∀ z ∈ Q,
        finiteFloorSupport θ (sourceTorusRepresentative z) ∧
        IsStarProjection (sourceTorusOperatorField p z) ∧
        (∀ r k m : ℤ, (sourceTorusOperatorField p (sourceTorusRotate θ r z)
          (lp.single 2 m (1 : ℂ))) k =
          (sourceTorusOperatorField p z (lp.single 2 (m+r) (1 : ℂ))) (k+r)) ∧
        (∀ n : ℕ, (∀ i, sourceTorusRepresentative z i ≤
          sourceTorusRepresentative (sourceTorusRotate θ n z) i) →
          (z,sourceTorusRotate θ n z) ∈ sourceCappedPairZeroSet θ p)) ∧
      (∀ n : ℤ, ∀ z ∈ Q, sourceTorusRotate θ n z ∈ Q) := by
  apply exists_source_invariant_conull
  have hf := sourceTorusRepresentative_preserving.quasiMeasurePreserving.ae
    (ae_finiteFloorSupport θ hθ.summable)
  have hc := sourceTorusRepresentative_preserving.quasiMeasurePreserving.ae
    (sourceOperatorField_covariance θ hp)
  filter_upwards [hf,hc,sourceTorusOperatorField_projection θ hp hproj,
    sourceProjection_ordered_orbits θ hθ hp hproj hinv] with z hf hc hp ho
  refine ⟨hf,hp,?_,ho⟩
  intro r k m
  change (sourceOperatorField p (sourceTorusRepresentative (sourceTorusRotate θ r z))
    (lp.single 2 m (1 : ℂ))) k = _
  rw [sourceTorusRepresentative_rotate]
  exact hc r m k

end
end FiniteFactor

end OAI
