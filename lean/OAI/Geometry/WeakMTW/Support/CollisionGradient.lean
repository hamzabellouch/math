import Mathlib
import OAI.Geometry.WeakMTW.Variations.ActionBranch
import OAI.Geometry.WeakMTW.Support.CollisionTangentCoordinates

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem branch_gradient_weighted {x z p : M} {κ : Type*} [Fintype κ]
    (a : κ → TangentSpace (model n) p) (θ : κ → ℝ)
    {b : TangentSpace (model n) p} (hsum : ∑ i, θ i = 1)
    (hbary : ∑ i, θ i • a i = b) {s ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (hp : p ∈ (chartAt (Model n) x).source)
    (B : ActionBranch (n := n) x z)
    (hB : stateChart x (⟨p,s•b⟩ : TangentBundle (model n) M) ∈ B.coord.source)
    (zC : κ → M) (C : ∀ i, ActionBranch (n := n) x (zC i))
    (hC : ∀ i, stateChart x (⟨p,ℓ•a i⟩ : TangentBundle (model n) M) ∈ (C i).coord.source)
    (u : Model n) :
    (∑ i, θ i*(fderiv ℝ B.value (chartAt (Model n) x p,chartAt (Model n) z (exp p (s•b))) (u,0) -
      (s/ℓ)*fderiv ℝ (C i).value
        (chartAt (Model n) x p,chartAt (Model n) (zC i) (exp p (ℓ•a i))) (u,0))) = 0 := by
  have hbS : (⟨p,s•b⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
    (stateChart_source x _).mpr hp
  have haS (i : κ) : (⟨p,ℓ•a i⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
    (stateChart_source x _).mpr hp
  rw [B.gradient_state _ hbS hB]
  simp_rw [(C _).gradient_state _ (haS _) (hC _)]
  let T := tangentCoordinateEquiv x p hp
  let L : TangentSpace (model n) p →L[ℝ] ℝ :=
    ((metric x (chartAt (Model n) x p)).flip u).comp T.toContinuousLinearMap
  change (∑ i, θ i*(-L (s•b)-(s/ℓ)*(-L (ℓ•a i)))) = 0
  have heq (i : κ) : θ i*(-L (s•b)-(s/ℓ)*(-L (ℓ•a i))) =
      s*(θ i*L (a i))-s*(θ i*L b) := by
    simp only [map_smul,smul_eq_mul]
    field_simp
    ring
  simp_rw [heq]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,← Finset.sum_mul,hsum,one_mul]
  have hL : ∑ i,θ i*L (a i) = L b := by rw [← hbary]; simp only [map_sum,map_smul,smul_eq_mul]
  rw [hL,sub_self]

 theorem weighted_nonpos_orthogonal {κ : Type*} [Fintype κ]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : κ → E) (θ : κ → ℝ) {b ξ : E}
    (hθ : ∀ i, 0 ≤ θ i) (hsum : ∑ i, θ i = 1)
    (hbary : ∑ i, θ i • a i = b) (hi : ∀ i, inner ℝ ξ (a i-b) ≤ 0) :
    ∀ i, θ i ≠ 0 → inner ℝ ξ (a i-b) = 0 := by
  classical
  have hh : ∑ i, θ i*inner ℝ ξ (a i-b) = 0 := by
    simp only [inner_sub_right,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hsum,one_mul]
    have he : ∑ i, θ i*inner ℝ ξ (a i) = inner ℝ ξ b := by
      rw [← hbary,inner_sum]
      simp only [inner_smul_right]
    rw [he,sub_self]
  have hz := (Finset.sum_eq_zero_iff_of_nonpos (fun i (_ : i ∈ Finset.univ) =>
    mul_nonpos_of_nonneg_of_nonpos (hθ i) (hi i))).mp hh
  intro i hiθ
  exact (mul_eq_zero.mp (hz i (Finset.mem_univ i))).resolve_left hiθ

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
