import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.MinimizerCompactness
import OAI.Geometry.WeakMTW.Variations.ActionBranch
import OAI.Geometry.WeakMTW.Support.TransverseJensen

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Pointwise
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem actionHessian_continuous (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) (ξ : TangentSpace (model n) x) :
    ContinuousAt (fun w => actionHessian x w ξ ξ) v := by
  apply (actionHessianDiag_smooth x hv ξ).continuousAt.congr_of_eventuallyEq
  filter_upwards [(injectivityDomain_open x).mem_nhds hv] with w hw
  exact actionHessian_diag x hw ξ

 theorem transverse_face_jensen (hMTW : HasWeakMTW (n := n) (M := M)) (x : M)
    (ξ : TangentSpace (model n) x) {S : Set (TangentSpace (model n) x)}
    (hS : Convex ℝ S) (hI : S ⊆ injectivityDomain x)
    {κ : Type*} [Fintype κ] (a : κ → TangentSpace (model n) x) (θ : κ → ℝ)
    {b : TangentSpace (model n) x} (hb : b ∈ S) (ha : ∀ i, a i ∈ S)
    (hθ : ∀ i, 0 ≤ θ i) (hsum : ∑ i, θ i = 1) (hbary : ∑ i, θ i • a i = b)
    (horth : ∀ i, θ i ≠ 0 → inner ℝ ξ (a i-b) = 0) :
    (∑ i, θ i * actionHessian x (a i) ξ ξ) ≤ actionHessian x b ξ ξ := by
  classical
  let aa : κ → TangentSpace (model n) x := fun i => if θ i = 0 then b else a i
  let T : Set (TangentSpace (model n) x) := S ∩ {v | inner ℝ ξ v = inner ℝ ξ b}
  have hT : Convex ℝ T := by
    intro u hu v hv r t hr ht hrt
    refine ⟨hS hu.1 hv.1 hr ht hrt,?_⟩
    change inner ℝ ξ (r•u+t•v) = inner ℝ ξ b
    have hu' : inner ℝ ξ u = inner ℝ ξ b := hu.2
    have hv' : inner ℝ ξ v = inner ℝ ξ b := hv.2
    simp only [inner_add_right,inner_smul_right,hu',hv']
    rw [← add_mul,hrt,one_mul]
  have haa (i : κ) : aa i ∈ T := by
    by_cases hi : θ i = 0
    · simp only [aa,ite_eq_left hi,T,mem_inter_iff,mem_ofPred_eq,and_true]
      exact hb
    · refine ⟨by simpa only [aa,ite_eq_right hi] using ha i,?_⟩
      have hh := horth i hi
      rw [inner_sub_right] at hh
      simpa only [aa,ite_eq_right hi,Set.mem_ofPred_eq] using sub_eq_zero.mp hh
  have horthT : ∀ u ∈ T, ∀ v ∈ T, inner ℝ ξ (v-u) = 0 := by
    intro u hu v hv
    rw [inner_sub_right,hv.2,hu.2,sub_self]
  have hbar : ∑ i, θ i • aa i = b := by
    rw [← hbary]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : θ i = 0 <;> simp [aa,hi]
  have hj := transverse_hessian_jensen hMTW x ξ hT (fun _ h => hI h.1) horthT
    Finset.univ aa θ (fun i _ => hθ i) (by simpa using hsum) (fun i _ => haa i)
  simp only [hbar] at hj
  convert hj using 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : θ i = 0 <;> simp [aa,hi]

 theorem critical_jensen (hMTW : HasWeakMTW (n := n) (M := M)) (x : M)
    (ξ : TangentSpace (model n) x) {S : Set (TangentSpace (model n) x)}
    (hS : Convex ℝ S) {s : ℝ} (hs : 0 < s)
    (hbelow : ∀ r, 0 ≤ r → r < s → ∀ a ∈ S, r•a ∈ injectivityDomain x)
    {κ : Type*} [Fintype κ] (a : κ → TangentSpace (model n) x) (θ : κ → ℝ)
    {b : TangentSpace (model n) x} (hb : b ∈ S) (ha : ∀ i, a i ∈ S)
    (hθ : ∀ i, 0 ≤ θ i) (hsum : ∑ i, θ i = 1) (hbary : ∑ i, θ i • a i = b)
    (horth : ∀ i, θ i ≠ 0 → inner ℝ ξ (a i-b) = 0)
    (haI : ∀ i, s•a i ∈ injectivityDomain x)
    (B : ActionBranch (n := n) x (exp x (s•b)))
    (hB : stateChart x (⟨x,s•b⟩ : TangentBundle (model n) M) ∈ B.coord.source) :
    (∑ i, θ i * actionHessian x (s•a i) ξ ξ) ≤
      branchHessianDiag x (exp x (s•b)) B.coord (s•b) ξ := by
  have hr : ∀ᶠ r : ℝ in 𝓝[<] s, 0 ≤ r ∧ r < s := by
    filter_upwards [(eventually_gt_nhds hs).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with r hr hrs
    exact ⟨hr.le,hrs⟩
  have ht (v : TangentSpace (model n) x) : Tendsto (fun r : ℝ => r•v) (𝓝[<] s) (𝓝 (s•v)) :=
    (continuous_id.smul continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlimB := B.hessian_limit hB ξ (ht b) (hr.mono (fun r hrs => hbelow r hrs.1 hrs.2 b hb))
  have hlimA := tendsto_finsetSum Finset.univ (fun i _ =>
    (((actionHessian_continuous x (haI i) ξ).tendsto.comp (ht (a i))).const_mul (θ i)))
  apply le_of_tendsto_of_tendsto hlimA hlimB
  filter_upwards [hr] with r hr
  have hbar : ∑ i, θ i • (r•a i) = r•b := by
    rw [← hbary,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
  apply transverse_face_jensen hMTW x ξ (hS.smul r)
    (fun _ ⟨v,hv,he⟩ => he ▸ hbelow r hr.1 hr.2 v hv)
    (fun i => r•a i) θ ⟨b,hb,rfl⟩ (fun i => ⟨a i,ha i,rfl⟩) hθ hsum hbar
  intro i hi
  rw [← smul_sub,inner_smul_right,horth i hi,mul_zero]

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
