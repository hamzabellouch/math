import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.PropagationMaximum

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma propagationCoreSource_measurable {r : ℝ} {μ p : Position → ℝ}
    (hμ : Measurable μ) (hp : Measurable p) :
    Measurable (fun x => propagationCoreSource r ‖x‖ (μ x) (p x)) := by
  exact measurable_const.mul ((hμ.ite (isOpen_lt continuous_norm continuous_const).measurableSet measurable_const).sub hp)

lemma propagationStepError_measurable (bad : Prop) (r R : ℝ) {μ p : Position → ℝ}
    (hμ : Measurable μ) (hp : Measurable p) :
    Measurable (fun x => propagationStepError bad r R ‖x‖ (μ x) (p x)) := by
  unfold propagationStepError
  by_cases hb : bad
  · simp only [hb,true_and]
    exact hp.add (hμ.ite ((isClosed_le continuous_const continuous_norm).measurableSet.inter
      (isOpen_lt continuous_norm continuous_const).measurableSet) measurable_const)
  · simpa only [hb,false_and,ite_false,add_zero] using hp

lemma propagationCoreSource_abs_bound {r d μ p M P : ℝ} (hμ : |μ|≤M) (hp : |p|≤P) :
    |propagationCoreSource r d μ p|≤4*Real.pi*(M+P) := by
  have hm : |if d<r then μ else 0|≤M := by
    split_ifs
    · exact hμ
    · simpa only [abs_zero] using (abs_nonneg μ).trans hμ
  unfold propagationCoreSource
  rw [abs_mul,abs_of_pos (by positivity : 0<4*Real.pi)]
  exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hm hp)) (by positivity)

lemma propagationStepError_abs_bound {bad : Prop} {r R d μ p M P : ℝ}
    (hμ : |μ|≤M) (hp : |p|≤P) : |propagationStepError bad r R d μ p|≤P+M := by
  unfold propagationStepError
  split_ifs
  · exact (abs_add_le _ _).trans (add_le_add hp hμ)
  · simp only [add_zero]
    have : 0≤M := (abs_nonneg μ).trans hμ
    linarith only [hp,this]

lemma propagationCoreSource_ball_bounds {r : ℝ} {μ p : Position → ℝ}
    (hμ : ∀ D : ℝ,∃ M : ℝ,∀ x∈Metric.closedBall 0 D,|μ x|≤M)
    (hp : ∀ D : ℝ,∃ P : ℝ,∀ x∈Metric.closedBall 0 D,|p x|≤P) :
    ∀ D : ℝ,∃ K : ℝ,∀ x∈Metric.closedBall 0 D,|propagationCoreSource r ‖x‖ (μ x) (p x)|≤K := by
  intro D
  obtain ⟨M,hM⟩ := hμ D
  obtain ⟨P,hP⟩ := hp D
  exact ⟨4*Real.pi*(M+P),fun x hx => propagationCoreSource_abs_bound (hM x hx) (hP x hx)⟩

lemma propagationStepError_ball_bounds {bad : Prop} {r R : ℝ} {μ p : Position → ℝ}
    (hμ : ∀ D : ℝ,∃ M : ℝ,∀ x∈Metric.closedBall 0 D,|μ x|≤M)
    (hp : ∀ D : ℝ,∃ P : ℝ,∀ x∈Metric.closedBall 0 D,|p x|≤P) :
    ∀ D : ℝ,∃ K : ℝ,∀ x∈Metric.closedBall 0 D,|propagationStepError bad r R ‖x‖ (μ x) (p x)|≤K := by
  intro D
  obtain ⟨M,hM⟩ := hμ D
  obtain ⟨P,hP⟩ := hp D
  exact ⟨P+M,fun x hx => propagationStepError_abs_bound (hM x hx) (hP x hx)⟩

lemma propagationRHS_locallyIntegrable {r Z : ℝ} {u μ p : Position → ℝ} (hr : 0<r)
    (hu : Continuous u) (hμ : Measurable μ) (hp : Measurable p)
    (hbμ : ∀ D : ℝ,∃ M : ℝ,∀ x∈Metric.closedBall 0 D,|μ x|≤M)
    (hbp : ∀ D : ℝ,∃ P : ℝ,∀ x∈Metric.closedBall 0 D,|p x|≤P) :
    LocallyIntegrable (fun x => propagationRHS r ‖x‖ (μ x) (p x) (Z*coulombKernel x+u x)) volume := by
  have H : LocallyIntegrable (fun x => propagationCoreSource r ‖x‖ (μ x) (p x)+
      cutoffReaction r (fun y => Z*coulombKernel y+u y) x) volume := (locallyIntegrable_of_ball_bounds (propagationCoreSource_measurable (r:=r) hμ hp)
    (propagationCoreSource_ball_bounds (r:=r) hbμ hbp)).add (cutoffReaction_offset_locallyIntegrable (Z:=Z) hr hu)
  simpa only [propagationRHS_eq] using H

end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

theorem WeakNuclearSubsolution.radialMaxSplice {α β a b c e Z : ℝ}
    {f g : Position → ℝ} {q : Position → ℝ → ℝ}
    (hbα : b<α) (hαa : α<a) (hae : a≤e) (heβ : e<β) (hβc : β<c)
    (hf : Continuous f) (hg : Continuous g)
    (hlow : ∀ x,b≤‖x‖ → ‖x‖≤a → g x≤f x)
    (hupp : ∀ x,e≤‖x‖ → ‖x‖≤c → f x≤g x)
    (hqi : LocallyIntegrable (fun x => q x (radialMaxSplice α β f g x)) volume)
    (hinner : WeakNuclearSubsolution (fun x => Z*coulombKernel x+f x) Z {x | ‖x‖<a} (fun x => q x (f x)))
    (hmiddle : WeakNuclearSubsolution (fun x => Z*coulombKernel x+max (f x) (g x)) Z
      {x | b<‖x‖ ∧ ‖x‖<c} (fun x => q x (max (f x) (g x))))
    (houter : WeakNuclearSubsolution (fun x => Z*coulombKernel x+g x) Z {x | e<‖x‖} (fun x => q x (g x))) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+radialMaxSplice α β f g x) Z univ
      (fun x => q x (radialMaxSplice α β f g x)) := by
  apply WeakNuclearSubsolution.of_local
    (continuous_radialMaxSplice hbα hαa hae heβ hβc hf hg hlow hupp) hqi
  intro x hx
  by_cases hxa : ‖x‖<a
  · refine ⟨{y | ‖y‖<a},hxa,isOpen_lt continuous_norm continuous_const,?_⟩
    apply hinner.congr_on
    · intro y hy
      rw [radialMaxSplice_inner hbα.le (hae.trans heβ.le) hlow hy]
    · intro y hy
      rw [radialMaxSplice_inner hbα.le (hae.trans heβ.le) hlow hy]
  · by_cases hex : e<‖x‖
    · refine ⟨{y | e<‖y‖},hex,isOpen_lt continuous_const continuous_norm,?_⟩
      apply houter.congr_on
      · intro y hy
        rw [radialMaxSplice_outer (hαa.le.trans hae) hβc.le hupp hy]
      · intro y hy
        rw [radialMaxSplice_outer (hαa.le.trans hae) hβc.le hupp hy]
    · have hxb : b<‖x‖ := (hbα.trans hαa).trans_le (le_of_not_gt hxa)
      have hxc : ‖x‖<c := (le_of_not_gt hex).trans_lt (heβ.trans hβc)
      refine ⟨{y | b<‖y‖ ∧ ‖y‖<c},⟨hxb,hxc⟩,
        (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const),?_⟩
      apply hmiddle.congr_on
      · intro y hy
        rw [radialMaxSplice_middle hαa.le heβ.le hlow hupp hy]
      · intro y hy
        rw [radialMaxSplice_middle hαa.le heβ.le hlow hupp hy]

end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

structure PropagationStepHypotheses (bad : Prop) (B C r R Z L l1 l2 e ξ hl hh : ℝ)
    (u H μ p : Position → ℝ) : Prop where
  B_pos : 0<B
  r_pos : 0<r
  R_eq : R=2*r
  L_large : 2<L
  l2_nonneg : 0≤l2
  l2_le_l1 : l2≤l1
  l1_le_gamma : l1≤propagationGamma B
  cap_large : B≤C
  upper_overlap : C≤l2*L^4
  e_pos : 0<e
  xi_nonneg : 0≤ξ
  xi_lt_l2 : ξ<l2
  gain_gap : 16*ξ+2*e<l1-l2
  height_lower : hl≤(7/8:ℝ)*B-2*e*(2*L)^4
  height_upper : C≤hh
  u_cont : Continuous u
  H_cont : Continuous H
  mu_nonneg : ∀ x,0≤μ x
  p_nonneg : ∀ x,0≤p x
  mu_measurable : Measurable μ
  p_measurable : Measurable p
  mu_bounds : ∀ D : ℝ,∃ M : ℝ,∀ x∈Metric.closedBall 0 D,|μ x|≤M
  p_bounds : ∀ D : ℝ,∃ P : ℝ,∀ x∈Metric.closedBall 0 D,|p x|≤P
  u_weak : WeakNuclearSubsolution (fun x => Z*coulombKernel x+u x) Z univ
    (fun x => propagationRHS r ‖x‖ (μ x) (p x) (Z*coulombKernel x+u x))
  H_weak : WeakNuclearSubsolution (fun x => Z*coulombKernel x+H x) Z univ (fun x => 4*Real.pi*μ x)
  barrier_small : 4*Real.pi*kTF*Real.sqrt B≤19/2
  old_caps : ∀ x,r≤‖x‖ → propagationBarrier B r x≤Z*coulombKernel x+u x ∧
    Z*coulombKernel x+u x≤C/‖x‖^4
  physical_cap : ¬bad → ∀ x,r≤‖x‖ → ‖x‖≤2*L*R → Z*coulombKernel x+H x≤C/‖x‖^4
  inverse : ¬bad → ∀ x,r≤‖x‖ → ‖x‖≤2*L*R → ∀ h∈Icc hl hh,
    (‖x‖^6*μ x≤Coulomb.tfScalarDensity h → ‖x‖^4*(Z*coulombKernel x+H x)≤h+ξ) ∧
    (Coulomb.tfScalarDensity h≤‖x‖^6*μ x → h-ξ≤‖x‖^4*(Z*coulombKernel x+H x))

namespace PropagationStepHypotheses
variable {bad : Prop} {B C r R Z L l1 l2 e ξ hl hh : ℝ} {u H μ p : Position → ℝ}
variable (d : PropagationStepHypotheses bad B C r R Z L l1 l2 e ξ hl hh u H μ p)
include d

lemma R_pos : 0<R := by rw [d.R_eq]; exact mul_pos (by norm_num) d.r_pos
lemma L_pos : 0<L := lt_trans (by norm_num) d.L_large
lemma old_le_new : r≤R := by rw [d.R_eq]; linarith only [d.r_pos]

lemma next_continuous : Continuous (propagationNextOffset bad B R Z L l1 l2 u H) :=
  propagationNextOffset_continuous d.B_pos d.r_pos d.R_eq d.L_large d.l2_nonneg d.l2_le_l1
    d.l1_le_gamma d.upper_overlap d.u_cont d.H_cont d.old_caps d.physical_cap

lemma step_error_measurable : Measurable (fun x => propagationStepError bad r R ‖x‖ (μ x) (p x)) :=
  propagationStepError_measurable bad r R d.mu_measurable d.p_measurable
lemma step_error_bounds : ∀ D : ℝ,∃ K : ℝ,∀ x∈Metric.closedBall 0 D,
    |propagationStepError bad r R ‖x‖ (μ x) (p x)|≤K :=
  propagationStepError_ball_bounds d.mu_bounds d.p_bounds

lemma finite_step {U : Set Position} (s : Finset (Fin 3)) (h0 : 0∈s)
    (h1 : 1∈s ↔ ¬bad) (h2 : 2∈s → ∀ x∈U,R<‖x‖)
    (hU : IsOpen U) (hUb : ∀ x∈U,‖x‖≤2*L*R)
    (hlo : ∀ x∈U,R≤‖x‖ → propagationBarrier B R x≤Z*coulombKernel x+
      s.sup' ⟨0,h0⟩ (fun i => propagationCandidates B R Z l1 l2 u H i x)) :
    WeakNuclearSubsolution
      (fun x => Z*coulombKernel x+s.sup' ⟨0,h0⟩ (fun i => propagationCandidates B R Z l1 l2 u H i x)) Z U
      (fun x => propagationRHS R ‖x‖ (μ x) (propagationStepError bad r R ‖x‖ (μ x) (p x))
        (Z*coulombKernel x+s.sup' ⟨0,h0⟩ (fun i => propagationCandidates B R Z l1 l2 u H i x))) := by
  have hqi : ∀ i∈s,LocallyIntegrable
      (propagationCandidateSources r R Z u μ p (propagationBarrierOffset B R Z) i) volume := by
    intro i hi
    fin_cases i
    · exact propagationRHS_locallyIntegrable d.r_pos d.u_cont d.mu_measurable d.p_measurable d.mu_bounds d.p_bounds
    · exact (locallyIntegrable_of_ball_bounds d.mu_measurable d.mu_bounds).smul (4*Real.pi)
    · exact cutoffReaction_offset_locallyIntegrable d.R_pos (propagationBarrierOffset_continuous B Z d.R_pos)
  exact propagation_finite_max_step s h0 h1 h2 d.B_pos d.r_pos d.R_eq d.L_pos.le
    d.l2_nonneg d.l2_le_l1 d.e_pos d.xi_nonneg d.xi_lt_l2 d.gain_gap d.height_lower d.height_upper
    hU hUb d.u_cont d.H_cont d.mu_nonneg d.p_nonneg hqi
    (propagationCoreSource_measurable d.mu_measurable d.step_error_measurable)
    (propagationCoreSource_ball_bounds d.mu_bounds d.step_error_bounds)
    (d.u_weak.mono_domain (subset_univ _)) (d.H_weak.mono_domain (subset_univ _))
    d.barrier_small d.old_caps d.physical_cap d.inverse hlo

end PropagationStepHypotheses
end NeutralAtom
end

end

end OAI
