import OAI.Geometry.NodalSets.Charts.SphereEnergyBilinear
import OAI.Geometry.NodalSets.Spectral.SphereRayleighQuotient

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory
open scoped ContDiff
noncomputable section

lemma sphereDirichletForm_add_left (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (u v w : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) :
    sphereDirichletForm A (u+v) w = sphereDirichletForm A u w+sphereDirichletForm A v w := by
  simp only [sphereDirichletForm,sphereDifferential_add u v hu hv,map_add,_root_.add_apply]
  exact integral_add (intrinsic_differential_pair_integrable A hA hs hp u w hu hw)
    (intrinsic_differential_pair_integrable A hA hs hp v w hv hw)

lemma sphereDirichletForm_smul_left (A : IntrinsicTensor) (u v : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (t : ℝ) :
    sphereDirichletForm A (t • u) v = t*sphereDirichletForm A u v := by
  simp only [sphereDirichletForm,sphereDifferential_smul u hu,map_smul,_root_.smul_apply,smul_eq_mul]
  exact integral_const_mul t _

end
end Yau.Target

end OAI
