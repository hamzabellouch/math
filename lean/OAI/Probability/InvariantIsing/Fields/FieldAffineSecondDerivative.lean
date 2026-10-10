import OAI.Probability.InvariantIsing.Fields.FieldAffineNeighborhood
import OAI.Probability.InvariantIsing.Fields.FieldAdjacentDerivative

namespace OAI

/-! Actual second covariance derivatives of every finite strict scalar
recursion. All derivative data are constructed from the Gaussian integrals. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing
namespace FieldSecondFamily

variable {I : Set ℝ} (F : FieldSecondFamily I)

lemma parameter_tangent_derivative (t z : ℝ) (ht : t ∈ I) :
    HasDerivAt (fun s => F.T (s, z)) (F.TT (t, z)) t := by
  have hmap : HasDerivAt (fun s : ℝ => (s, z)) ((1 : ℝ), (0 : ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
  have hd := (F.derivativeT (t, z) ht).comp_hasDerivAt t hmap
  simpa [IsingPerceptron.pairLinear, Function.comp_def] using hd

lemma parameter_mean_derivative (t z : ℝ) (ht : t ∈ I) :
    HasDerivAt (fun s => F.X (s, z)) (F.TX (t, z)) t := by
  have hmap : HasDerivAt (fun s : ℝ => (s, z)) ((1 : ℝ), (0 : ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
  have hd := (F.derivativeX (t, z) ht).comp_hasDerivAt t hmap
  simpa [IsingPerceptron.pairLinear, Function.comp_def] using hd

end FieldSecondFamily

theorem fieldAffineValue_second_derivative (L : List FieldAffineStep) (t z : ℝ)
    (hpos : ∀ av ∈ L, 0 < av.base + av.slope * t) :
    ∃ D : ℝ, HasDerivAt (fun s => deriv (fun r => fieldAffineValue L (r, z)) s) D t := by
  obtain ⟨I, hI, ht, m, V, hm, hL⟩ := fieldAffine_variance_neighborhood L t hpos
  let F := fieldAffineSecondFamily I hI m V hm L hL
  have hval : F.U = fieldAffineValue L := fieldAffineSecondFamily_value I hI m V hm L hL
  have he : (fun s => deriv (fun r => fieldAffineValue L (r, z)) s) =ᶠ[𝓝 t]
      (fun s => F.T (s, z)) := by
    filter_upwards [hI.mem_nhds ht] with s hs
    have hd := F.toFieldSmoothFamily.parameter_derivative s z hs
    rw [hval] at hd
    exact hd.deriv
  exact ⟨F.TT (t, z), (F.parameter_tangent_derivative t z ht).congr_of_eventuallyEq he⟩

theorem fieldAffineValue_spatial_derivative_parameter_differentiable
    (L : List FieldAffineStep) (t z : ℝ)
    (hpos : ∀ av ∈ L, 0 < av.base + av.slope * t) :
    DifferentiableAt ℝ (fun s => deriv (fun y => fieldAffineValue L (s, y)) z) t := by
  obtain ⟨I, hI, ht, m, V, hm, hL⟩ := fieldAffine_variance_neighborhood L t hpos
  let F := fieldAffineSecondFamily I hI m V hm L hL
  have hval : F.U = fieldAffineValue L := fieldAffineSecondFamily_value I hI m V hm L hL
  have he : (fun s => deriv (fun y => fieldAffineValue L (s, y)) z) =ᶠ[𝓝 t]
      (fun s => F.X (s, z)) := by
    apply Eventually.of_forall
    intro s
    have hd := F.spatial s z
    rw [hval] at hd
    exact hd.deriv
  exact ((F.parameter_mean_derivative t z ht).congr_of_eventuallyEq he).differentiableAt

end InvariantIsing

end

end OAI
