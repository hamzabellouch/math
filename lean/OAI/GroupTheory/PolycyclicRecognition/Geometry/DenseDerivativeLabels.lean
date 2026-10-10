import OAI.GroupTheory.PolycyclicRecognition.Analysis.DenseConvexConstraints
import OAI.GroupTheory.PolycyclicRecognition.Geometry.HorizontalDerivativeLabel

namespace OAI

/-! # Countably many directional derivatives determine one finite label -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory

namespace SupportDatum

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]

omit [Nonempty B] in
theorem continuous_basisSupport (D : SupportDatum W I B) (b : B) :
    Continuous (D.basisSupport b) := by
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (continuous_const.max (D.weight i).continuous_of_finiteDimensional)

theorem continuous_segmentSupport (D : SupportDatum W I B) :
    Continuous D.segmentSupport :=
  Continuous.finset_sup'_apply Finset.univ_nonempty (fun b _ => D.continuous_basisSupport b)

end SupportDatum

theorem ae_template_label_of_dense_derivatives
    {H W Z I B J : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace Z] [Fintype I] [Fintype B] [Nonempty B] [Finite J]
    (μ : Measure Z) (Ω : Set Z) (D : SupportDatum W I B)
    (π : H →L[ℝ] W) (hπ : Function.Surjective π)
    (A : J → templateSymmetryGroup D) (M : Z → H →ₗ[ℝ] W)
    (curve : Z → H → ℝ → W)
    (hc : ∀ z ∈ Ω, ∀ v, Continuous (curve z v))
    (S : Set H) (hSc : S.Countable) (hSd : Dense S)
    (hderiv : ∀ v ∈ S, ∀ᵐ z ∂μ, z ∈ Ω → HasDerivAt (curve z v) (M z v) 0)
    (T : Z → H → ℝ) (hT : ∀ z ∈ Ω, ∀ v ∈ S, 0 < T z v)
    (hinc : ∀ z ∈ Ω, ∀ v ∈ S, ∀ t, 0 < t → t < T z v →
      t⁻¹ • (curve z v t - curve z v 0) ∈ convexHull ℝ (range fun j => (A j).val (π v)))
    (hvol : ∀ z ∈ Ω, ∀ v ∈ S, ∀ t, 0 < t → t < T z v →
      t * D.segmentSupport (π v) ≤ D.templateSupport (curve z v '' Icc 0 t)) :
    ∀ᵐ z ∂μ, z ∈ Ω → ∃ j, M z = (A j).val.toLinearMap.comp π.toLinearMap := by
  filter_upwards [(ae_ball_iff hSc).mpr hderiv] with z hz hzΩ
  have hconvS (v : H) (hv : v ∈ S) :
      M z v ∈ convexHull ℝ (range fun j => (A j).val (π v)) := by
    apply derivative_mem_of_short_increments (curve z v) (M z v) (hz v hv hzΩ)
      (convexHull ℝ (range fun j => (A j).val (π v)))
      ((Set.finite_range _).isClosed_convexHull (𝕜 := ℝ)) (hT z hzΩ v hv)
    exact hinc z hzΩ v hv
  have hlowS (v : H) (hv : v ∈ S) : D.segmentSupport (π v) ≤ D.segmentSupport (M z v) :=
    D.le_segmentSupport_derivative (curve z v) (hc z hzΩ v) (M z v) (hz v hv hzΩ)
      (D.segmentSupport (π v)) (hT z hzΩ v hv) (hvol z hzΩ v hv)
  have hconv := mem_finite_convexHull_of_dense (M z) (M z).continuous_of_finiteDimensional
    (fun j v => (A j).val (π v))
    (fun j => (A j).val.toLinearMap.continuous_of_finiteDimensional.comp π.continuous) hSd hconvS
  have hclosed : IsClosed {v : H | D.segmentSupport (π v) ≤ D.segmentSupport (M z v)} :=
    isClosed_le (D.continuous_segmentSupport.comp π.continuous)
      (D.continuous_segmentSupport.comp (M z).continuous_of_finiteDimensional)
  have hlow (v : H) : D.segmentSupport (π v) ≤ D.segmentSupport (M z v) := by
    apply hclosed.closure_subset_iff.mpr hlowS
    rw [hSd.closure_eq]
    trivial
  exact derivative_eq_one_of_template_labels D π.toLinearMap (M z) hπ A hconv hlow

end PolycyclicRecognition

end

end OAI
