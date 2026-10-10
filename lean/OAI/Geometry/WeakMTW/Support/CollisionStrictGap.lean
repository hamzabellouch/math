import Mathlib
import OAI.Geometry.WeakMTW.Support.CollisionGradient
import OAI.Geometry.WeakMTW.Support.ActiveRepresentation
import OAI.Geometry.WeakMTW.Support.CriticalHessianGap
import OAI.Geometry.WeakMTW.Variations.ZeroActionHessian

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
  {ι : Type*} [Fintype ι] [Nonempty ι]

 theorem collision_strict_gap (y : ι → M) (h : ι → ℝ)
    (hMTW : HasWeakMTW (n := n) (M := M))
    {p : TangentBundle (model n) M} (R : ActiveRepresentation y h p)
    {ξ : TangentSpace (model n) p.1} (hξ : ξ ≠ 0)
    {s ℓ : ℝ} (hs : 0 ≤ s) (hsℓ : s < ℓ) (hℓ₁ : ℓ < 1)
    (hbelow : ∀ r, 0 ≤ r → r < s → ∀ a ∈ activeHull (n := n) y h p.1, r•a ∈ injectivityDomain p.1)
    (B : ActionBranch (n := n) p.1 (exp p.1 (s•p.2)))
    (hB : stateChart p.1 (mulState s p) ∈ B.coord.source)
    (C : ∀ i, ActionBranch (n := n) p.1 (exp p.1 (ℓ•R.a i)))
    (hC : ∀ i, stateChart p.1 (⟨p.1,ℓ•R.a i⟩ : TangentBundle (model n) M) ∈ (C i).coord.source)
    (hfirst : ∀ i, fderiv ℝ B.value (chartAt (Model n) p.1 p.1,
        chartAt (Model n) (exp p.1 (s•p.2)) (exp p.1 (s•p.2))) (tangentChartLinear p.1 ξ,0) -
      (s/ℓ)*fderiv ℝ (C i).value (chartAt (Model n) p.1 p.1,
        chartAt (Model n) (exp p.1 (ℓ•R.a i)) (exp p.1 (ℓ•R.a i))) (tangentChartLinear p.1 ξ,0) ≤ 0) :
    0 < ∑ i, R.θ i*(fderiv ℝ (fderiv ℝ B.value)
      (chartAt (Model n) p.1 p.1,chartAt (Model n) (exp p.1 (s•p.2)) (exp p.1 (s•p.2)))
      (tangentChartLinear p.1 ξ,0) (tangentChartLinear p.1 ξ,0) -
      (s/ℓ)*fderiv ℝ (fderiv ℝ (C i).value)
        (chartAt (Model n) p.1 p.1,chartAt (Model n) (exp p.1 (ℓ•R.a i)) (exp p.1 (ℓ•R.a i)))
        (tangentChartLinear p.1 ξ,0) (tangentChartLinear p.1 ξ,0)) := by
  have hℓ : 0 < ℓ := lt_of_le_of_lt hs hsℓ
  obtain hs0 | hspos := eq_or_lt_of_le hs
  · have hz : s = 0 := hs0.symm
    subst s
    have hB0 : stateChart p.1 (⟨p.1,0⟩ : TangentBundle (model n) M) ∈ B.coord.source := by
      simpa only [mulState,zero_smul] using hB
    have hzH := branch_zero_raw_hessian B hB0 ξ
    simp only [zero_smul,exp_zero] at hzH
    simp only [zero_div,zero_mul,sub_zero,zero_smul,exp_zero,
      ← Finset.sum_mul,R.sum_one,one_mul]
    rw [hzH]
    exact real_inner_self_pos.mpr hξ
  have hnonpos (i : ActiveIndex n) : inner ℝ ξ (R.a i-p.2) ≤ 0 := by
    have hi := hfirst i
    rw [B.gradient_center hB ξ,(C i).gradient_center (hC i) ξ] at hi
    have heq : -inner ℝ (s•p.2) ξ - (s/ℓ)*(-inner ℝ (ℓ•R.a i) ξ) =
        s*inner ℝ ξ (R.a i-p.2) := by
      simp only [real_inner_smul_left,inner_sub_right]
      rw [real_inner_comm p.2 ξ, real_inner_comm (R.a i) ξ]
      field_simp
      ring
    rw [heq] at hi
    nlinarith
  have horth := weighted_nonpos_orthogonal R.a R.θ R.nonneg R.sum_one R.bary hnonpos
  have ha (i : ActiveIndex n) : R.a i ∈ activeHull (n := n) y h p.1 := subset_convexHull ℝ _ (R.active i)
  have hb : p.2 ∈ activeHull (n := n) y h p.1 := by
    rw [← R.bary]
    exact (convex_convexHull ℝ _).sum_mem (fun i _ => R.nonneg i) R.sum_one (fun i _ => ha i)
  have hgap := critical_hessian_gap hMTW p.1 hξ (convex_convexHull ℝ _) hspos hsℓ hℓ₁
    hbelow R.a R.θ hb ha (fun i => (R.active i).1) R.nonneg R.sum_one R.bary horth B hB
  rw [branch_raw_weighted_eq R.a R.θ R.sum_one R.bary hℓ.ne' B C]
  convert hgap using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [actionHessian_eq_branch p.1 (exp p.1 (ℓ•R.a i)) (C i).coord (C i).map_eq
    (C i).domain (C i).smooth (strict_radial_mem_injectivity (R.active i).1 hℓ.le hℓ₁) (hC i) ξ]

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
