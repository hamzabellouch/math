import Mathlib.Analysis.InnerProductSpace.Basic
import OAI.Geometry.NodalSets.Charts.SphereDirichletBilinear

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory
open scoped ContDiff
noncomputable section

def sphereSmoothFunctions : Submodule ℝ (Base → ℝ) where
  carrier := {u | ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u}
  zero_mem' := contMDiff_const
  add_mem' := fun hu hv ↦ hu.add hv
  smul_mem' := fun t _ hu ↦ (contMDiff_const (c := t)).mul hu

def sphereSobolevForm (A : IntrinsicTensor) (rho u v : Base → ℝ) : ℝ :=
  sphereWeightedPairing rho u v+sphereDirichletForm A u v

theorem sphereSobolevForm_pos (A : IntrinsicTensor)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho u : Base → ℝ) (hr : Continuous rho) (hrp : ∀ x, 0 < rho x)
    (hu : Continuous u) (hne : u ≠ 0) : 0 < sphereSobolevForm A rho u u :=
  add_pos_of_pos_of_nonneg (sphereWeightedPairing_self_pos rho u hr hrp hu hne)
    (sphereDirichletForm_nonneg A hp u)

@[instance_reducible]
def sphereEnergyInnerCore (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : Continuous rho) (hrp : ∀ x, 0 < rho x) :
    InnerProductSpace.Core ℝ sphereSmoothFunctions where
  inner u v := sphereSobolevForm A rho u v
  conj_inner_symm u v := by
    change sphereSobolevForm A rho v u = sphereSobolevForm A rho u v
    simp only [sphereSobolevForm,sphereWeightedPairing_symm rho v u,sphereDirichletForm_symm A hs v u]
  re_inner_nonneg u := by
    change 0 ≤ sphereWeightedPairing rho u u+sphereDirichletForm A u u
    apply add_nonneg _ (sphereDirichletForm_nonneg A hp u)
    apply integral_nonneg
    intro x
    change 0 ≤ rho x*((u : Base → ℝ) x)*((u : Base → ℝ) x)
    simpa only [mul_assoc] using
      mul_nonneg (hrp x).le (mul_self_nonneg ((u : Base → ℝ) x))
  add_left u v w := by
    change sphereSobolevForm A rho ((u : Base → ℝ)+v) w =
      sphereSobolevForm A rho u w+sphereSobolevForm A rho v w
    rw [sphereSobolevForm,sphereWeightedPairing_add_left rho u v w hr
      u.property.continuous v.property.continuous w.property.continuous,
      sphereDirichletForm_add_left A hA hs hp u v w u.property v.property w.property]
    simp only [sphereSobolevForm]
    ring
  smul_left u v t := by
    change sphereSobolevForm A rho (t • (u : Base → ℝ)) v = t*sphereSobolevForm A rho u v
    rw [sphereSobolevForm,sphereWeightedPairing_smul_left,sphereDirichletForm_smul_left A u v u.property]
    simp only [sphereSobolevForm,mul_add]
  definite u hu := by
    by_contra hne
    have hn : (u : Base → ℝ) ≠ 0 := fun h ↦ hne (Subtype.ext h)
    exact (ne_of_gt (sphereSobolevForm_pos A hp rho u hr hrp u.property.continuous hn)) hu

end
end Yau.Target

end OAI
