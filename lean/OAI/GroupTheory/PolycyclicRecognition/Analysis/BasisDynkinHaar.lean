import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialRightHaar
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalizedGroupLaws
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentHaarInput

namespace OAI

/-! # Lebesgue invariance of actual rescaled Dynkin translations

Every coordinate basis is allowed. Hence the lemma applies directly to the
scale-dependent maximizing bases used by the occupation measures.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Module
open scoped Manifold

/-- The actual exponential-coordinate multiplication preserves coordinate
Lebesgue measure under right translations, in every basis. -/
theorem measurePreserving_basis_dynkin_right
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {n c : ℕ} (b : Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (q : Fin n → ℝ) :
    MeasurePreserving (fun x => dynkinProduct a (basisBracket b) x q) volume volume := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨⟨chart, hchart⟩, hhaar⟩ := haar.2 Exp hExp hnil
  let e : (Fin n → ℝ) ≃ₜ G :=
    b.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart
  let : SecondCountableTopology G := e.symm.secondCountableTopology
  have he (x : Fin n → ℝ) : e x = Exp (b.equivFun.symm x) := hchart _
  have heq : (e : (Fin n → ℝ) → G) = Exp ∘ b.equivFun.symm := funext he
  let μ := Measure.map e volume
  have hμ : μ.IsHaarMeasure := by
    change (Measure.map e volume).IsHaarMeasure
    rw [heq]
    exact hhaar n b
  let := hμ
  have hneg (x : Fin n → ℝ) : e (-x) = (e x)⁻¹ := by
    rw [he, he]
    simpa using hExp.map_neg (b.equivFun.symm x)
  let : μ.IsMulRightInvariant := isMulRightInvariant_map_of_neg volume e
    e.continuous.measurable hneg
  apply coordinate_right_translation_preserving volume μ e.toMeasurableEquiv rfl
    (dynkinProduct a (basisBracket b)) _ q
  intro x y
  change e (dynkinProduct a (basisBracket b) x y) = e x * e y
  rw [he, he, he]
  have h := basis_dynkinProduct b a (b.equivFun.symm x) (b.equivFun.symm y)
  simp only [LinearEquiv.apply_symm_apply] at h
  rw [h, LinearEquiv.symm_apply_apply]
  exact hm _ _

end PolycyclicRecognition

end

end OAI
