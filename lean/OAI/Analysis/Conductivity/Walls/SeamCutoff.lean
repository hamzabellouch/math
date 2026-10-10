import Mathlib
import OAI.Analysis.Conductivity.Variational.PhysicalEndLocalLipschitz
import OAI.Analysis.Conductivity.Sobolev.CompactLipschitzH1

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped NNReal

lemma LocalLipAt.mul {E : Type*} [PseudoMetricSpace E]
    {f g : E → ℝ} {x : E} (hf : LocalLipAt f x) (hg : LocalLipAt g x) :
    LocalLipAt (fun y => f y*g y) x := by
  exact (localLipAt_of_contDiffAt
    (show ContDiffAt ℝ 1 (fun p : ℝ×ℝ => p.1*p.2) (f x,g x) by fun_prop)).comp
    (f:=fun y => (f y,g y)) (x:=x) (hf.prodMk hg)

lemma compact_locallyLipschitz {f : R3 → ℝ}
    (hf : ∀ x,LocalLipAt f x) (hc : HasCompactSupport f) :
    ∃ K,LipschitzWith K f := by
  classical
  obtain ⟨R,hR,hzero⟩ := hc.exists_pos_le_norm
  have hlocal : LocallyLipschitz f := hf
  obtain ⟨K,hK⟩ := hlocal.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0:R3) R)
  let S : Set R3 := Metric.closedBall 0 R
  have hclosure : closure S=S := Metric.isClosed_closedBall.closure_eq
  have hmatch : EqOn f (fun _ => (0:ℝ)) (frontier S) := by
    intro x hx
    have hs := Metric.frontier_closedBall_subset_sphere hx
    have hn : ‖x‖=R := by simpa only [Metric.mem_sphere,dist_zero_right] using hs
    exact hzero x hn.ge
  have hlip := lipschitz_piecewise_frontier S
    (show LipschitzOnWith K f (closure S) by rw [hclosure]; exact hK)
    (LipschitzWith.const (0:ℝ)).lipschitzOnWith hmatch
  have he : S.piecewise f (fun _ => 0)=f := by
    funext x
    by_cases hx : x∈S
    · simp only [piecewise_eq_of_mem S _ _ hx]
    · rw [piecewise_eq_of_notMem S _ _ hx]
      have hn : R<‖x‖ := by simpa only [S,Metric.mem_closedBall,dist_zero_right,not_le] using hx
      exact (hzero x hn.le).symm
  rw [he] at hlip
  exact ⟨max K 0,hlip⟩

lemma smoothTransition_lipschitz : ∃ K,LipschitzWith K Real.smoothTransition := by
  obtain ⟨K,hK⟩ := (Real.smoothTransition.contDiff (n:=1)).contDiffOn.exists_lipschitzOnWith
    (by simp) (convex_Icc (0:ℝ) 1) isCompact_Icc
  have hp := hK.comp (LipschitzWith.projIcc (show (0:ℝ)≤1 by norm_num)).lipschitzOnWith
    (s:=univ) (fun x _ => (projIcc (0:ℝ) 1 (by norm_num) x).property)
  refine ⟨K,?_⟩
  simpa only [Function.comp_def,Real.smoothTransition.projIcc,mul_one] using (lipschitzOnWith_univ.mp hp)

def seamCutoff (n : ℕ) (t : ℝ) : ℝ :=
  Real.smoothTransition (((n:ℝ)+1)*t-1)

lemma seamCutoff_smooth (n : ℕ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (seamCutoff n) := by
  unfold seamCutoff
  exact (Real.smoothTransition.contDiff (n:=⊤)).comp (by fun_prop)

lemma seamCutoff_bounds (n : ℕ) (t : ℝ) : 0 ≤ seamCutoff n t ∧ seamCutoff n t≤1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

lemma seamCutoff_zero (n : ℕ) {t : ℝ} (ht : ((n:ℝ)+1)*t≤1) : seamCutoff n t=0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma seamCutoff_one (n : ℕ) {t : ℝ} (ht : 2≤((n:ℝ)+1)*t) : seamCutoff n t=1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma seamCutoff_eventually_one {t : ℝ} (ht : 0<t) : ∀ᶠ n in atTop,seamCutoff n t=1 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (2/t)
  filter_upwards [eventually_ge_atTop N] with n hn
  apply seamCutoff_one
  have hle : (N:ℝ)≤n := by exact_mod_cast hn
  have hmul := (div_lt_iff₀ ht).mp hN
  nlinarith

lemma seamCutoff_deriv (n : ℕ) (t : ℝ) :
    deriv (seamCutoff n) t=deriv Real.smoothTransition (((n:ℝ)+1)*t-1)*((n:ℝ)+1) := by
  have hs := ((Real.smoothTransition.contDiff (n:=1)).differentiable (by simp)).differentiableAt (x:=((n:ℝ)+1)*t-1) |>.hasDerivAt
  have ha : HasDerivAt (fun t : ℝ => ((n:ℝ)+1)*t-1) ((n:ℝ)+1) t := by
    convert! ((hasDerivAt_id t).const_mul ((n:ℝ)+1)).sub_const 1 using 1
    simp
  exact (hs.comp t ha).deriv

lemma seamCutoff_deriv_bound : ∃ D : ℝ,0≤D ∧ ∀ n t,
    |deriv (seamCutoff n) t|≤D*((n:ℝ)+1) := by
  obtain ⟨D,hD⟩ := smoothTransition_lipschitz
  refine ⟨D,D.coe_nonneg,?_⟩
  intro n t
  rw [seamCutoff_deriv,abs_mul,abs_of_nonneg (by positivity : 0≤(n:ℝ)+1)]
  exact mul_le_mul_of_nonneg_right (norm_deriv_le_of_lipschitz hD) (by positivity)

lemma seamCutoff_deriv_zero (n : ℕ) {t : ℝ} (ht : 2<((n:ℝ)+1)*t) :
    deriv (seamCutoff n) t=0 := by
  have he : seamCutoff n=ᶠ[𝓝 t] (fun _ => 1) := by
    filter_upwards [isOpen_lt continuous_const (by fun_prop : Continuous (fun t : ℝ => ((n:ℝ)+1)*t)) |>.mem_nhds ht] with t ht
    exact seamCutoff_one n ht.le
  rw [he.deriv_eq,deriv_const]

lemma seamCutoff_mul_lipschitz {u τ : R3 → ℝ}
    (hτ : LocallyLipschitz τ) (hu : ∀ x,0<τ x → LocalLipAt u x)
    (hc : HasCompactSupport u) (n : ℕ) :
    ∃ K,LipschitzWith K (fun x => seamCutoff n (τ x)*u x) := by
  have hlocal (x : R3) : LocalLipAt (fun x => seamCutoff n (τ x)*u x) x := by
    by_cases ht : 0<τ x
    · exact ((localLipAt_of_contDiffAt ((seamCutoff_smooth n).of_le (by simp)).contDiffAt).comp
        (hτ x)).mul (hu x ht)
    · have hx : ((n:ℝ)+1)*τ x<1 := by nlinarith [le_of_not_gt ht,Nat.cast_nonneg (α:=ℝ) n]
      have he : (fun _ : R3 => (0:ℝ))=ᶠ[𝓝 x] (fun x => seamCutoff n (τ x)*u x) := by
        filter_upwards [isOpen_lt (continuous_const.mul hτ.continuous) continuous_const |>.mem_nhds hx] with y hy
        rw [seamCutoff_zero n hy.le,zero_mul]
      exact (localLipAt_of_contDiffAt contDiffAt_const).congr he
  exact compact_locallyLipschitz hlocal (hc.mul_left)

end ScalarConductivity

end

end OAI
