import Mathlib
import OAI.Geometry.WeakMTW.Variations.ActionHessian

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Pointwise
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem transverse_hessian_concave (hMTW : HasWeakMTW (n := n) (M := M))
    (x : M) (ξ : TangentSpace (model n) x) {K : Set (TangentSpace (model n) x)}
    (hK : Convex ℝ K) (hI : K ⊆ injectivityDomain x)
    (horth : ∀ u ∈ K, ∀ v ∈ K, inner ℝ ξ (v-u) = 0) :
    ConcaveOn ℝ K (fun v => actionHessian x v ξ ξ) := by
  refine ⟨hK,?_⟩
  intro u hu v hv a b ha hb hab
  have hlineI : ∀ t ∈ Icc (0 : ℝ) 1, u+t•(v-u) ∈ injectivityDomain x := by
    intro t ht
    apply hI
    have hh := hK hu hv (sub_nonneg.mpr ht.2) ht.1 (by ring : (1-t)+t=1)
    convert hh using 1
    module
  have hconc := transverse_action_concave hMTW x u ξ (v-u) (horth u hu v hv) (convex_Icc 0 1) hlineI
  have hh := hconc.2 (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1) ha hb hab
  have huv : a•u+b•v = u+b•(v-u) := by
    have ha' : a = 1-b := by linarith
    rw [ha']
    module
  have hw := hK hu hv ha hb hab
  rw [huv] at hw ⊢
  simp only [zero_smul,add_zero,one_smul,add_sub_cancel,smul_eq_mul,mul_zero,mul_one,zero_add] at hh
  rw [← actionHessian_diag x (hI hu) ξ,← actionHessian_diag x (hI hv) ξ,
    ← actionHessian_diag x (hI hw) ξ] at hh
  exact hh

 theorem transverse_hessian_jensen (hMTW : HasWeakMTW (n := n) (M := M))
    (x : M) (ξ : TangentSpace (model n) x) {K : Set (TangentSpace (model n) x)}
    (hK : Convex ℝ K) (hI : K ⊆ injectivityDomain x)
    (horth : ∀ u ∈ K, ∀ v ∈ K, inner ℝ ξ (v-u) = 0)
    {ι : Type*} (T : Finset ι) (a : ι → TangentSpace (model n) x) (θ : ι → ℝ)
    (hθ : ∀ i ∈ T, 0 ≤ θ i) (hsum : ∑ i ∈ T, θ i = 1)
    (ha : ∀ i ∈ T, a i ∈ K) :
    (∑ i ∈ T, θ i * actionHessian x (a i) ξ ξ) ≤
      actionHessian x (∑ i ∈ T, θ i • a i) ξ ξ := by
  simpa only [smul_eq_mul] using
    (transverse_hessian_concave hMTW x ξ hK hI horth).le_map_sum hθ hsum ha

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
