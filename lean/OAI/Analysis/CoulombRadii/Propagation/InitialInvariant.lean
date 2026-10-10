import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.PropagationDatumRegularity
import OAI.Analysis.CoulombRadii.Propagation.InitializationBranch

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma propagationRHS_ball_bounds {r Z : ℝ} {u μ p : Position → ℝ} (hr : 0<r)
    (hu : Continuous u)
    (hbμ : ∀ D : ℝ,∃ M : ℝ,∀ x∈Metric.closedBall 0 D,|μ x| ≤ M)
    (hbp : ∀ D : ℝ,∃ P : ℝ,∀ x∈Metric.closedBall 0 D,|p x| ≤ P) :
    ∀ D : ℝ,∃ K : ℝ,∀ x∈Metric.closedBall 0 D,
      |propagationRHS r ‖x‖ (μ x) (p x) (Z*coulombKernel x+u x)| ≤ K := by
  intro D
  obtain ⟨A,hA⟩ := propagationCoreSource_ball_bounds (r:=r) hbμ hbp D
  obtain ⟨K,hK⟩ := cutoffReaction_offset_ball_bound (Z:=Z) hr hu D
  refine ⟨A+K,fun x hx => ?_⟩
  rw [propagationRHS_eq]
  exact (abs_add_le _ _).trans (add_le_add (hA x hx) (hK x hx))

structure InitialPropagationData (bad : Prop) (B C Z r a L : ℝ) (H μ : Position → ℝ) : Prop where
  B_pos : 0<B
  Z_nonneg : 0 ≤ Z
  r_pos : 0<r
  a_nonneg : 0 ≤ a
  L_large : 2 ≤ L
  BZ : B ≤ (1/10:ℝ)*Z*r^3
  C_B : B ≤ C
  C_Z : 32*Z*r^3 ≤ C
  quadratic : 4*a*r^2 ≤ (1/20:ℝ)*Z/r
  reaction : tfReaction (2*Z/r) ≤ 6*a
  barrier_small : 4*Real.pi*kTF*Real.sqrt B ≤ 19/2
  H_cont : Continuous H
  H_nonpos : ∀ x,H x ≤ 0
  H_lower : ¬bad → ∀ x,r ≤ ‖x‖ → ‖x‖ ≤ 2*r → -(1/10:ℝ)*Z/r ≤ H x
  mu_measurable : Measurable μ
  mu_nonneg : ∀ x,0 ≤ μ x
  mu_bounds : ∀ D : ℝ,∃ M : ℝ,∀ x∈Metric.closedBall 0 D,|μ x| ≤ M
  nuclear : WeakNuclearSubsolution (fun x => Z*coulombKernel x+H x) Z univ (fun x => 4*Real.pi*μ x)

namespace InitialPropagationData
variable {bad : Prop} {B C Z r a L : ℝ} {H μ : Position → ℝ}
variable (d : InitialPropagationData bad B C Z r a L H μ)
include d

lemma next_continuous : Continuous (initialNextOffset bad B Z r a H) :=
  initialNextOffset_continuous d.B_pos d.Z_nonneg d.r_pos d.a_nonneg d.BZ d.quadratic d.H_cont d.H_nonpos d.H_lower

lemma branch_weak : WeakNuclearSubsolution
    (fun x => Z*coulombKernel x+initialPropagationOffset bad Z r a H x) Z {x | ‖x‖<2*r}
    (fun x => propagationRHS r ‖x‖ (μ x) (initialPropagationError bad r μ x)
      (Z*coulombKernel x+initialPropagationOffset bad Z r a H x)) :=
  initialPropagationOffset_weak d.Z_nonneg d.r_pos d.a_nonneg d.quadratic d.reaction d.H_cont d.H_nonpos
    d.mu_measurable d.mu_nonneg d.mu_bounds d.nuclear

lemma barrier_weak : WeakNuclearSubsolution
    (fun x => Z*coulombKernel x+propagationBarrierOffset B r Z x) Z {x | r<‖x‖}
    (fun x => propagationRHS r ‖x‖ (μ x) (initialPropagationError bad r μ x)
      (Z*coulombKernel x+propagationBarrierOffset B r Z x)) := by
  apply (propagationBarrier_weak (Z:=Z) d.B_pos d.r_pos d.barrier_small).congr_on
  · intro x hx; rfl
  · intro x hx
    have hrx : r ≤ ‖x‖ := le_of_lt hx
    simp [propagationRHS,propagationCoreSource,initialPropagationError,not_lt_of_ge hrx,hrx,
      propagationBarrierOffset_eq hrx]

lemma middle_weak : WeakNuclearSubsolution
    (fun x => Z*coulombKernel x+max (initialPropagationOffset bad Z r a H x) (propagationBarrierOffset B r Z x))
    Z {x | r<‖x‖ ∧ ‖x‖<2*r}
    (fun x => propagationRHS r ‖x‖ (μ x) (initialPropagationError bad r μ x)
      (Z*coulombKernel x+max (initialPropagationOffset bad Z r a H x) (propagationBarrierOffset B r Z x))) := by
  have hc := initialPropagationOffset_continuous bad Z r a d.H_cont
  have hb := propagationBarrierOffset_continuous B Z d.r_pos
  have he := initialPropagationError_measurable bad r d.mu_measurable
  have heK := initialPropagationError_ball_bounds (bad:=bad) (r:=r) d.mu_bounds
  have Hmax := WeakNuclearSubsolution.max_reaction
    (Z:=Z) (b:=fun _ => 0) (F:=fun x v => propagationRHS r ‖x‖ (μ x) (initialPropagationError bad r μ x) v)
    (U:={x | r<‖x‖ ∧ ‖x‖<2*r})
    ((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const))
    hc hb
    (by simpa only [zero_add] using propagationRHS_locallyIntegrable (Z:=Z) d.r_pos hc d.mu_measurable he d.mu_bounds heK)
    (by simpa only [zero_add] using propagationRHS_locallyIntegrable (Z:=Z) d.r_pos hb d.mu_measurable he d.mu_bounds heK)
    (by simpa only [zero_add] using propagationRHS_ball_bounds (Z:=Z) d.r_pos hc d.mu_bounds heK)
    (by simpa only [zero_add] using propagationRHS_ball_bounds (Z:=Z) d.r_pos hb d.mu_bounds heK)
    (by simpa only [zero_add] using d.branch_weak.mono_domain (fun x hx => hx.2))
    (by simpa only [zero_add] using d.barrier_weak.mono_domain (fun x hx => hx.1))
  simpa only [zero_add] using Hmax

lemma next_weak : WeakNuclearSubsolution
    (fun x => Z*coulombKernel x+initialNextOffset bad B Z r a H x) Z univ
    (fun x => propagationRHS r ‖x‖ (μ x) (initialPropagationError bad r μ x)
      (Z*coulombKernel x+initialNextOffset bad B Z r a H x)) := by
  apply WeakNuclearSubsolution.radialMaxSplice (a:=(53/50)*r) (b:=r) (e:=(19/10)*r) (c:=2*r)
    (q:=fun x v => propagationRHS r ‖x‖ (μ x) (initialPropagationError bad r μ x) (Z*coulombKernel x+v))
  · linarith only [d.r_pos]
  · linarith only [d.r_pos]
  · linarith only [d.r_pos]
  · linarith only [d.r_pos]
  · linarith only [d.r_pos]
  · exact initialPropagationOffset_continuous bad Z r a d.H_cont
  · exact propagationBarrierOffset_continuous B Z d.r_pos
  · exact fun x hx hx' => initialPropagationOffset_low_overlap d.B_pos d.Z_nonneg d.r_pos d.a_nonneg d.BZ d.H_lower hx hx'
  · exact fun x hx hx' => initialPropagationOffset_high_overlap d.B_pos d.Z_nonneg d.r_pos d.a_nonneg d.quadratic d.H_nonpos hx hx'
  · exact propagationRHS_locallyIntegrable d.r_pos d.next_continuous d.mu_measurable
      (initialPropagationError_measurable bad r d.mu_measurable) d.mu_bounds (initialPropagationError_ball_bounds d.mu_bounds)
  · exact d.branch_weak.mono_domain (fun x hx => by
      change ‖x‖<(53/50)*r at hx
      change ‖x‖<2*r
      linarith only [hx,d.r_pos])
  · exact d.middle_weak
  · exact d.barrier_weak.mono_domain (fun x hx => by
      change (19/10)*r<‖x‖ at hx
      change r<‖x‖
      linarith only [hx,d.r_pos])

end InitialPropagationData
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
namespace InitialPropagationData
variable {bad : Prop} {B C Z r a L : ℝ} {H μ : Position → ℝ}
variable (d : InitialPropagationData bad B C Z r a L H μ)
include d

lemma branch_cap {x : Position} (hx : r ≤ ‖x‖) (hx' : ‖x‖ ≤ 2*r) :
    Z*coulombKernel x+initialPropagationOffset bad Z r a H x ≤ C/‖x‖^4 := by
  have hd := d.r_pos.trans_le hx
  have H := initialPropagationOffset_upper (bad:=bad) d.Z_nonneg d.r_pos d.a_nonneg d.quadratic d.H_nonpos hx hx'
  have hp := pow_le_pow_left₀ (norm_nonneg x) hx' 4
  have hpre : (2*Z/r)*‖x‖^4 ≤ C := by
    have hmul := mul_le_mul_of_nonneg_left hp (div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) d.Z_nonneg) d.r_pos.le)
    calc
      _ ≤ (2*Z/r)*(2*r)^4 := hmul
      _ = 32*Z*r^3 := by field_simp; ring
      _ ≤ C := d.C_Z
  exact H.trans ((le_div_iff₀ (pow_pos hd 4)).mpr hpre)

lemma next_caps {x : Position} (hx : r ≤ ‖x‖) :
    propagationBarrier B r x ≤ Z*coulombKernel x+initialNextOffset bad B Z r a H x ∧
    Z*coulombKernel x+initialNextOffset bad B Z r a H x ≤ C/‖x‖^4 := by
  have hd := d.r_pos.trans_le hx
  have hbar := (propagationBarrier_two_sided d.B_pos.le d.r_pos hx).2.trans
    (div_le_div_of_nonneg_right d.C_B (pow_pos hd 4).le)
  have he := propagationBarrierOffset_eq (B:=B) (Z:=Z) hx
  unfold initialNextOffset radialMaxSplice
  split_ifs with hα hβ
  · have hlow := initialPropagationOffset_low_overlap d.B_pos d.Z_nonneg d.r_pos d.a_nonneg d.BZ d.H_lower hx
      (show ‖x‖ ≤ (53/50)*r by linarith only [hα,d.r_pos])
    refine ⟨?_,d.branch_cap hx (by linarith only [hα,d.r_pos])⟩
    linarith only [hlow,he]
  · have hlow := le_max_right (initialPropagationOffset bad Z r a H x) (propagationBarrierOffset B r Z x)
    refine ⟨by linarith only [hlow,he],?_⟩
    rw [add_max]
    exact max_le (d.branch_cap hx (by linarith only [hβ,d.r_pos])) (by simpa only [he] using hbar)
  · simpa only [he] using And.intro le_rfl hbar

lemma next_outer {x : Position} (hx : L*r<‖x‖) :
    Z*coulombKernel x+initialNextOffset bad B Z r a H x=propagationBarrier B r x := by
  have h2 : 2*r ≤ L*r := mul_le_mul_of_nonneg_right d.L_large d.r_pos.le
  have h1 : r ≤ ‖x‖ := by linarith only [hx,h2,d.r_pos]
  have hα : ¬‖x‖<(103/100)*r := by linarith only [hx,h2,d.r_pos]
  have hβ : ¬‖x‖<(39/20)*r := by linarith only [hx,h2,d.r_pos]
  simpa only [initialNextOffset,radialMaxSplice,ite_eq_right hα,ite_eq_right hβ] using
    (propagationBarrierOffset_eq (B:=B) (Z:=Z) h1)

theorem invariant : PropagationInvariant B C r Z L (initialNextOffset bad B Z r a H) μ
    (initialPropagationError bad r μ) :=
  ⟨d.next_continuous,initialPropagationError_nonneg d.mu_nonneg,
    fun _ hx => initialPropagationError_support bad r μ hx,d.next_weak,
    fun _ hx => d.next_caps hx,fun _ hx => d.next_outer hx⟩

end InitialPropagationData
end NeutralAtom
end

end

end OAI
