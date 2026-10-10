import Mathlib
import OAI.Geometry.WeakMTW.Variations.RadialComparison
import OAI.Geometry.WeakMTW.Support.CriticalJensen

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

 theorem critical_hessian_gap (hMTW : HasWeakMTW (n := n) (M := M)) (x : M)
    {ξ : TangentSpace (model n) x} (hξ : ξ ≠ 0)
    {S : Set (TangentSpace (model n) x)} (hS : Convex ℝ S)
    {s ℓ : ℝ} (hs : 0 < s) (hsℓ : s < ℓ) (hℓ : ℓ < 1)
    (hbelow : ∀ r, 0 ≤ r → r < s → ∀ a ∈ S, r•a ∈ injectivityDomain x)
    {κ : Type*} [Fintype κ] (a : κ → TangentSpace (model n) x) (θ : κ → ℝ)
    {b : TangentSpace (model n) x} (hb : b ∈ S) (ha : ∀ i, a i ∈ S)
    (haM : ∀ i, a i ∈ minimizingDomain x)
    (hθ : ∀ i, 0 ≤ θ i) (hsum : ∑ i, θ i = 1) (hbary : ∑ i, θ i • a i = b)
    (horth : ∀ i, θ i ≠ 0 → inner ℝ ξ (a i-b) = 0)
    (B : ActionBranch (n := n) x (exp x (s•b)))
    (hB : stateChart x (⟨x,s•b⟩ : TangentBundle (model n) M) ∈ B.coord.source) :
    0 < ∑ i, θ i * (branchHessianDiag x (exp x (s•b)) B.coord (s•b) ξ -
      (s/ℓ)*actionHessian x (ℓ•a i) ξ ξ) := by
  classical
  have hJ := critical_jensen hMTW x ξ hS hs hbelow a θ hb ha hθ hsum hbary horth
    (fun i => strict_radial_mem_injectivity (haM i) hs.le (hsℓ.trans hℓ)) B hB
  have hgap (i : κ) : 0 < actionHessian x (s•a i) ξ ξ -
      (s/ℓ)*actionHessian x (ℓ•a i) ξ ξ := by
    have hh := (div_lt_div_iff₀ (hs.trans hsℓ) hs).mp
      (radial_hessian_strict x (haM i) hs hsℓ hℓ hξ)
    have ht := (div_lt_iff₀ (hs.trans hsℓ)).mpr hh
    have ht' : (s/ℓ)*actionHessian x (ℓ•a i) ξ ξ < actionHessian x (s•a i) ξ ξ := by
      calc
        (s/ℓ)*actionHessian x (ℓ•a i) ξ ξ =
            (actionHessian x (ℓ•a i) ξ ξ * s)/ℓ := by ring
        _ < actionHessian x (s•a i) ξ ξ := ht
    linarith
  have hex : ∃ i, 0 < θ i := by
    by_contra! hn
    have hz : ∑ i, θ i ≤ 0 := Finset.sum_nonpos (fun i _ => hn i)
    linarith
  obtain ⟨i,hi⟩ := hex
  have hpos : 0 < ∑ i, θ i * (actionHessian x (s•a i) ξ ξ -
      (s/ℓ)*actionHessian x (ℓ•a i) ξ ξ) :=
    Finset.sum_pos' (fun i _ => mul_nonneg (hθ i) (hgap i).le)
      ⟨i,Finset.mem_univ i,mul_pos hi (hgap i)⟩
  have heq : (∑ i, θ i * (branchHessianDiag x (exp x (s•b)) B.coord (s•b) ξ -
      (s/ℓ)*actionHessian x (ℓ•a i) ξ ξ)) =
      branchHessianDiag x (exp x (s•b)) B.coord (s•b) ξ -
      ∑ i, θ i*((s/ℓ)*actionHessian x (ℓ•a i) ξ ξ) := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hsum,one_mul]
  rw [heq]
  simp only [mul_sub,Finset.sum_sub_distrib] at hpos
  linarith

 theorem branch_raw_weighted_eq {x : M} {κ : Type*} [Fintype κ]
    (a : κ → TangentSpace (model n) x) (θ : κ → ℝ)
    {b ξ : TangentSpace (model n) x} (hsum : ∑ i, θ i = 1)
    (hbary : ∑ i, θ i • a i = b) {s ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (B : ActionBranch (n := n) x (exp x (s•b)))
    (C : ∀ i, ActionBranch (n := n) x (exp x (ℓ•a i))) :
    (∑ i, θ i * (fderiv ℝ (fderiv ℝ B.value)
      (chartAt (Model n) x x,chartAt (Model n) (exp x (s•b)) (exp x (s•b)))
      (tangentChartLinear x ξ,0) (tangentChartLinear x ξ,0) -
      (s/ℓ)*fderiv ℝ (fderiv ℝ (C i).value)
        (chartAt (Model n) x x,chartAt (Model n) (exp x (ℓ•a i)) (exp x (ℓ•a i)))
        (tangentChartLinear x ξ,0) (tangentChartLinear x ξ,0))) =
    ∑ i, θ i * (branchHessianDiag x (exp x (s•b)) B.coord (s•b) ξ -
      (s/ℓ)*branchHessianDiag x (exp x (ℓ•a i)) (C i).coord (ℓ•a i) ξ) := by
  let L : TangentSpace (model n) x →L[ℝ] ℝ :=
    (lowerChristoffel (fderiv ℝ (metric x) (chartAt (Model n) x x))
      (tangentChartLinear x ξ) (tangentChartLinear x ξ)).comp (tangentChartLinear x)
  have hc : (∑ i, θ i * (L (s•b)-(s/ℓ)*L (ℓ•a i))) = 0 := by
    simp only [map_smul,smul_eq_mul,mul_sub,Finset.sum_sub_distrib]
    rw [← Finset.sum_mul,hsum,one_mul]
    have hla : ∑ i, θ i * L (a i) = L b := by rw [← hbary]; simp only [map_sum,map_smul,smul_eq_mul]
    have heq : (∑ i, θ i * (s/ℓ*(ℓ*L (a i)))) = s*(∑ i, θ i*L (a i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_assoc (s/ℓ) ℓ, div_mul_cancel₀ _ hℓ, mul_left_comm]
    rw [heq,hla,sub_self]
  have halg (i : κ) : θ i * (branchHessianDiag x (exp x (s•b)) B.coord (s•b) ξ -
      (s/ℓ)*branchHessianDiag x (exp x (ℓ•a i)) (C i).coord (ℓ•a i) ξ) =
      θ i * (fderiv ℝ (fderiv ℝ B.value)
        (chartAt (Model n) x x,chartAt (Model n) (exp x (s•b)) (exp x (s•b)))
        (tangentChartLinear x ξ,0) (tangentChartLinear x ξ,0) -
        (s/ℓ)*fderiv ℝ (fderiv ℝ (C i).value)
          (chartAt (Model n) x x,chartAt (Model n) (exp x (ℓ•a i)) (exp x (ℓ•a i)))
          (tangentChartLinear x ξ,0) (tangentChartLinear x ξ,0)) +
      θ i*(L (s•b)-(s/ℓ)*L (ℓ•a i)) := by
    simp only [branchHessianDiag,ActionBranch.value,L,ContinuousLinearMap.comp_apply]
    ring
  simp_rw [halg]
  rw [Finset.sum_add_distrib,hc,add_zero]

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
