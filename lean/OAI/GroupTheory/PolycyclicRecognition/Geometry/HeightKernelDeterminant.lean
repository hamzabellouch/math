import OAI.GroupTheory.PolycyclicRecognition.Geometry.HeightConjugationDifferential
import OAI.GroupTheory.PolycyclicRecognition.Analysis.QuotientSectionRightHaar
import OAI.GroupTheory.PolycyclicRecognition.Analysis.LinearDeterminantMeasure

namespace OAI

/-! # Unimodularity and the determinant of the actual adjoint action

The kernel is measured in exponential coordinates. Conjugation preserves
that measure by the quotient-section argument, and acts as the identity on
the height quotient. The two determinant factors therefore have absolute
value one.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold

variable {E G W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

theorem abs_det_conjugationDifferential_eq_one_of_height_coordinates
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (π : G →* Multiplicative W) (hπ : Continuous π)
    (hπExp : ∀ v, (π (Exp v)).toAdd = q (heightProjection T.character v))
    (s : C(Multiplicative W, G)) (hs : ∀ w, π (s w) = w)
    (b : Basis (Fin (finrank ℝ T.kernelIdeal)) ℝ T.kernelIdeal)
    (c : (Fin (finrank ℝ T.kernelIdeal) → ℝ) ≃ₜ π.ker)
    (hc : ∀ v, (c v : G) = Exp (b.equivFun.symm v))
    (hhaar : (Measure.map c volume).IsHaarMeasure)
    (hright : (Measure.map c volume).IsMulRightInvariant)
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (g : G) :
    |LinearMap.det (conjugationDifferentialHom (E := E) g).toLinearMap| = 1 := by
  let : MeasurableSpace (Multiplicative W) := borel _
  let : BorelSpace (Multiplicative W) := ⟨rfl⟩
  let μQ : Measure (Multiplicative W) := Measure.haar
  let μI := Measure.map c volume
  let : μI.IsHaarMeasure := hhaar
  let : μI.IsMulRightInvariant := hright
  have hconj := quotientKernelConjugate_preserves_of_unimodular
    π hπ s hs μQ μI μ g
  let A := conjugationDifferentialLinearEquiv (E := E) g
  let U := T.kernelIdeal.toSubmodule
  have hU : U ≤ U.comap A.toLinearMap := by
    intro v hv
    exact conjugationDifferential_mem_heightKernel T q hExp π hπExp g hv
  have hquot : U.mapQ U A.toLinearMap hU = LinearMap.id := by
    ext v
    change heightProjection T.character (conjugationDifferentialHom (E := E) g v) =
      heightProjection T.character v
    exact heightProjection_conjugationDifferential T q hExp π hπExp g v
  let B := b.equivFun.conj (A.toLinearMap.restrict hU)
  have hcompat (v : Fin (finrank ℝ T.kernelIdeal) → ℝ) :
      c (B v) = quotientKernelConjugate π g (c v) := by
    apply Subtype.ext
    rw [hc]
    change Exp (b.equivFun.symm (B v) : GroupLieAlgebra (𝓘(ℝ, E)) G) =
      g * (c v : G) * g⁻¹
    have hb : (b.equivFun.symm (B v) : GroupLieAlgebra (𝓘(ℝ, E)) G) =
        conjugationDifferentialHom (E := E) g (b.equivFun.symm v) := by
      simp only [B, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
      rfl
    rw [hb, ← conjugation_exponential hExp, hc]
  have hsem : Function.Semiconj c.symm (quotientKernelConjugate π g) B := by
    intro k
    obtain ⟨v, rfl⟩ := c.surjective k
    rw [← hcompat, c.symm_apply_apply, c.symm_apply_apply]
  have hcMP : MeasurePreserving c.toMeasurableEquiv volume μI :=
    c.toMeasurableEquiv.measurable.measurePreserving volume
  have hB : MeasurePreserving B volume volume :=
    hcMP.symm.of_semiconj hconj hsem B.continuous_of_finiteDimensional.measurable
  exact abs_det_eq_one_of_kernel_volume U A.toLinearMap A.isUnit_det'.ne_zero hU hquot b hB

end PolycyclicRecognition

end

end OAI
