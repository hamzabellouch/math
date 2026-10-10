import OAI.MeasureTheory.Falconer.Slicing.GaussianSpanRows

namespace OAI

/-! # A Gaussian map preserves each fixed independent family almost surely -/
namespace Falconer
open Set Submodule MeasureTheory
open scoped ENNReal
variable {d n : ℕ}

theorem gaussian_preserves_independent_family (v : Fin (n+1) → Space d)
    (hv : LinearIndependent ℝ v) :
    ∀ᵐ A : Fin (n+1) → Space d ∂gaussianRows d (n+1),
      LinearIndependent ℝ (fun i => gaussianRowMap A (v i)) := by
  let V := span ℝ (range v)
  have hdim : Module.finrank ℝ V = n+1 := by
    simpa [V] using finrank_span_eq_card hv
  let b := sliceCoordinates V hdim
  have ha : ∀ᵐ A : Fin (n+1) → Space d ∂gaussianRows d (n+1),
      (euclideanColumnMatrix (projectedGaussianRows V b A)).det ≠ 0 := by
    apply ae_of_ae_map (μ := gaussianRows d (n+1))
      (p := fun C => (euclideanColumnMatrix C).det ≠ 0)
      (projectedGaussianRows_measurable V b).aemeasurable
    rw [projectedGaussianRows_law]
    exact gaussian_square_det_ne_zero_ae
  filter_upwards [ha] with A hA
  have hker (z : Space d) (hz : z ∈ V) (hzero : gaussianRowMap A z = 0) : z = 0 := by
    have he := eq_zero_of_orthogonal_columns (projectedGaussianRows V b A) hA (b ⟨z,hz⟩) (by
      intro i
      rw [inner_projectedGaussianRows]
      have hi := congrArg (fun w : Space (n+1) => w i) hzero
      simpa only [gaussianRowMap_apply,PiLp.zero_apply] using hi)
    have hz' : (⟨z,hz⟩ : V) = 0 := b.injective (by simpa using he)
    exact congrArg Subtype.val hz'
  apply hv.map_injOn (gaussianRowMap A).toLinearMap
  intro x hx y hy hxy
  change gaussianRowMap A x = gaussianRowMap A y at hxy
  exact sub_eq_zero.mp (hker (x-y) (V.sub_mem hx hy) (by
    rw [map_sub,hxy,sub_self]))

end Falconer

end OAI
