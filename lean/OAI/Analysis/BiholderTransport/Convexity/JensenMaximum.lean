import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma jensen_C11_select {f : E → ℝ} {g : E → E} {x0 : E} {r eta : ℝ}
    {L : ℝ≥0} (hr : 0 < r) (heta : 0 < eta)
    (hf : ContinuousOn f (Metric.closedBall x0 r))
    (hmax : ∀ x ∈ Metric.closedBall x0 r, f x ≤ f x0)
    (hd : ∀ x ∈ Metric.ball x0 r, HasFDerivAt f ((innerSL ℝ) (g x)) x)
    (hlip : LipschitzOnWith L g (Metric.closedBall x0 r))
    (μ : Measure E) [μ.IsAddHaarMeasure] {P : E → Prop} (hP : ∀ᵐ z ∂μ, P z) :
    ∃ z ∈ Metric.ball x0 r, P z ∧ ‖g z‖ ≤ 2*eta*r ∧
      ∀ x ∈ Metric.closedBall x0 r,
        f x ≤ f z + inner ℝ (g z) (x-z) + eta/2*‖x-z‖^2 := by
  let nu : Measure E := Measure.hausdorffMeasure (Module.finrank ℝ E)
  let psi : E → E := fun x => g x - eta • (x-x0)
  let N : Set E := Metric.closedBall x0 r ∩ {x | ¬P x}
  have hN : μ N = 0 := measure_mono_null inter_subset_right (ae_iff.mp hP)
  have hNnu : nu N = 0 := (Measure.absolutelyContinuous_isAddHaarMeasure nu μ) hN
  have hpsi : LipschitzOnWith (L+⟨eta,heta.le⟩) psi (Metric.closedBall x0 r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have heq : psi x - psi y = (g x-g y)-eta • (x-y) := by
      dsimp [psi]
      simp only [smul_sub]
      abel
    rw [dist_eq_norm,heq]
    calc
      ‖(g x-g y)-eta • (x-y)‖ ≤ ‖g x-g y‖+‖eta • (x-y)‖ := norm_sub_le _ _
      _ ≤ L * dist x y + eta * dist x y := by
        simp only [norm_smul_of_nonneg heta.le,← dist_eq_norm]
        exact add_le_add (hlip.dist_le_mul x hx y hy) le_rfl
      _ = (↑(L+⟨eta,heta.le⟩) : ℝ) * dist x y := by change (L:ℝ)*dist x y+eta*dist x y=((L:ℝ)+eta)*dist x y; ring
  have hnullnu : nu (psi '' N) = 0 := by
    have hh := (hpsi.mono (show N ⊆ Metric.closedBall x0 r from inter_subset_left)).hausdorffMeasure_image_le
      (by positivity : (0:ℝ) ≤ Module.finrank ℝ E)
    simpa only [nu,hNnu,mul_zero,nonpos_iff_eq_zero] using hh
  have hnull : μ (psi '' N) = 0 :=
    (Measure.absolutelyContinuous_isAddHaarMeasure μ nu) hnullnu
  have hdense : Dense {a | a ∉ psi '' N} := μ.dense_of_ae
    (ae_iff.mpr (by simpa only [not_not,Set.ofPred_mem_eq] using hnull))
  obtain ⟨a,ha,han⟩ := hdense.inter_open_nonempty (Metric.ball 0 (eta*r/4))
    Metric.isOpen_ball (Metric.nonempty_ball.mpr (by positivity))
  have hanorm : ‖a‖ < eta*r/4 := by simpa only [Metric.mem_ball,dist_zero_right] using ha
  let F : E → ℝ := fun x => f x - eta/2*‖x-x0‖^2-inner ℝ a (x-x0)
  have hFc : ContinuousOn F (Metric.closedBall x0 r) := by
    exact (hf.sub (by fun_prop)).sub (by fun_prop)
  obtain ⟨z,hz,hzmax⟩ := (isCompact_closedBall x0 r).exists_isMaxOn
    (Metric.nonempty_closedBall.mpr hr.le) hFc
  have hcenter : F x0 ≤ F z := hzmax (Metric.mem_closedBall_self hr.le)
  have hzb : z ∈ Metric.ball x0 r := by
    have hzn : ‖z-x0‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
    have hlin := abs_real_inner_le_norm a (z-x0)
    have hz0 := hmax z hz
    have hanon : -‖a‖*‖z-x0‖ ≤ inner ℝ a (z-x0) := by
      have hh := (abs_le.mp hlin).1
      nlinarith
    by_contra hn
    have hzeq : ‖z-x0‖ = r := by
      have hh : r ≤ ‖z-x0‖ := by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hn
      exact le_antisymm hzn hh
    dsimp [F] at hcenter
    simp only [sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,inner_zero_right,sub_zero] at hcenter
    rw [hzeq] at hcenter hanon
    have hh : ‖a‖*r < eta*r^2/4 := by nlinarith
    have hpos : 0 < eta*r^2 := mul_pos heta (sq_pos_of_pos hr)
    nlinarith
  have hdF : HasFDerivAt F ((innerSL ℝ) (psi z-a)) z := by
    have hdq : HasFDerivAt (fun x:E => eta/2*‖x-x0‖^2)
        ((eta/2) • (2 • ((innerSL ℝ) (z-x0)))) z := by
      simpa only [id_eq,ContinuousLinearMap.comp_id] using
        ((((hasFDerivAt_id (𝕜 := ℝ) z).sub_const x0).norm_sq).const_mul (eta/2))
    have hda : HasFDerivAt (fun x:E => inner ℝ a (x-x0)) ((innerSL ℝ) a) z := by
      simpa only [id_eq,ContinuousLinearMap.comp_id,Function.comp_def,innerSL_apply_apply] using
        (((innerSL ℝ) a).hasFDerivAt.comp z
          ((hasFDerivAt_id (𝕜 := ℝ) z).sub_const x0))
    apply (((hd z hzb).sub hdq).sub hda).congr_fderiv
    ext h
    simp only [psi,sub_apply,smul_apply,innerSL_apply_apply,inner_sub_left,real_inner_smul_left]
    ring
  have hzero := (hzmax.isLocalMax (mem_of_superset
    (Metric.isOpen_ball.mem_nhds hzb) Metric.ball_subset_closedBall)).hasFDerivAt_eq_zero hdF
  have hpsia : psi z = a := by
    have heval := congrArg (fun A : E →L[ℝ] ℝ => A (psi z-a)) hzero
    simp only [innerSL_apply_apply,zero_apply,real_inner_self_eq_norm_sq] at heval
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp heval))
  have hzP : P z := by
    by_contra hn
    exact han ⟨z,⟨hz,hn⟩,hpsia⟩
  have hg : g z = eta • (z-x0)+a := by
    dsimp [psi] at hpsia
    exact (sub_eq_iff_eq_add.mp hpsia).trans (add_comm _ _)
  refine ⟨z,hzb,hzP,?_,?_⟩
  · have hzn : ‖z-x0‖ < r := by simpa only [Metric.mem_ball,dist_eq_norm] using hzb
    calc
      ‖g z‖ ≤ eta*‖z-x0‖+‖a‖ := by rw [hg]; simpa only [norm_smul_of_nonneg heta.le] using norm_add_le (eta • (z-x0)) a
      _ ≤ 2*eta*r := by nlinarith
  · intro x hx
    have hm := hzmax hx
    have hnorm : ‖x-x0‖^2 = ‖x-z‖^2+2*inner ℝ (x-z) (z-x0)+‖z-x0‖^2 := by
      have heq : x-x0 = (x-z)+(z-x0) := by abel
      rw [heq]
      simp only [← real_inner_self_eq_norm_sq,inner_add_left,inner_add_right]
      have hcom : inner ℝ (z-x0) (x-z) = inner ℝ (x-z) (z-x0) := real_inner_comm _ _
      rw [hcom]
      ring
    have hinner : inner ℝ a (x-x0) = inner ℝ a (x-z)+inner ℝ a (z-x0) := by
      rw [show x-x0 = (x-z)+(z-x0) by abel,inner_add_right]
    dsimp [F] at hm
    rw [hnorm,hinner] at hm
    rw [hg,inner_add_left,real_inner_smul_left]
    have hcom : inner ℝ (x-z) (z-x0) = inner ℝ (z-x0) (x-z) := real_inner_comm _ _
    rw [hcom] at hm
    linarith

end WeakMTWTransport

end

end OAI
