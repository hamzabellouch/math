import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.PropagationBarrierBounds

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

def propagationBarrierOffset (B R Z : ℝ) (x : Position) : ℝ :=
  B/(max R ‖x‖)^4*(1-R/(8*max R ‖x‖))-Z/(max R ‖x‖)

lemma propagationBarrierOffset_continuous (B Z : ℝ) {R : ℝ} (hR : 0<R) :
    Continuous (propagationBarrierOffset B R Z) := by
  have hD : Continuous (fun x : Position => max R ‖x‖) := continuous_const.max continuous_norm
  have hne (x : Position) : max R ‖x‖≠0 := ne_of_gt (hR.trans_le (le_max_left _ _))
  exact ((continuous_const.div (hD.pow 4) (fun x => pow_ne_zero 4 (hne x))).mul
    (continuous_const.sub (continuous_const.div (continuous_const.mul hD)
      (fun x => mul_ne_zero (by norm_num) (hne x))))).sub (continuous_const.div hD hne)

lemma propagationBarrierOffset_eq {B R Z : ℝ} {x : Position} (hx : R≤‖x‖) :
    Z*coulombKernel x+propagationBarrierOffset B R Z x=propagationBarrier B R x := by
  rw [propagationBarrierOffset,max_eq_right hx,propagationBarrier_eq]
  unfold coulombKernel
  ring

lemma propagationBarrier_weak {B R Z : ℝ} (hB : 0<B) (hR : 0<R)
    (hsmall : 4*Real.pi*kTF*Real.sqrt B≤19/2) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+propagationBarrierOffset B R Z x) Z
      {x | R<‖x‖} (fun x => tfReaction (propagationBarrier B R x)) := by
  have hU : IsOpen {x : Position | R<‖x‖} := isOpen_lt continuous_const continuous_norm
  have hsub : {x : Position | R<‖x‖} ⊆ punctured := by
    intro x hx
    exact norm_pos_iff.mp (hR.trans hx)
  have hp : ContDiffOn ℝ 2 (propagationBarrier B R) {x | R<‖x‖} :=
    (contDiffOn_propagationBarrier B R 2).mono hsub
  have hf : ∀ x ∈ {x : Position | R<‖x‖},ContDiffAt ℝ 2 (propagationBarrier B R) x :=
    fun x hx => hp.contDiffAt (hU.mem_nhds hx)
  have hq : LocallyIntegrableOn (fun x => tfReaction (propagationBarrier B R x)) {x | R<‖x‖} :=
    (tfReaction_continuous.comp_continuousOn hp.continuousOn).locallyIntegrableOn hU.measurableSet
  have H := WeakLaplacianGE.of_classical hf hq
    (fun x hx => propagationBarrier_laplacian_ge_reaction hB hR hsmall hx.le)
  apply (H.to_nuclear_away (by simp [not_lt_of_ge hR.le]) Z).congr_on
  · intro x hx
    exact (propagationBarrierOffset_eq hx.le).symm
  · intro x hx
    rfl

end NeutralAtom

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
namespace NeutralAtom

def propagationCoreSource (r d μ p : ℝ) : ℝ := 4*Real.pi*((if d<r then μ else 0)-p)
def propagationRHS (r d μ p u : ℝ) : ℝ :=
  propagationCoreSource r d μ p+(if r≤d then tfReaction u else 0)
def propagationStepError (bad : Prop) (r R d μ p : ℝ) : ℝ :=
  p+if bad ∧ r≤d ∧ d<R then μ else 0

lemma propagationStepError_nonneg {bad : Prop} {r R d μ p : ℝ}
    (hμ : 0≤μ) (hp : 0≤p) : 0≤propagationStepError bad r R d μ p := by
  unfold propagationStepError
  split_ifs <;> positivity

lemma propagation_old_source {bad : Prop} {r R d μ p u l : ℝ}
    (hrR : r≤R) (hR : 0<R) (hl : 0≤l)
    (hgain : ¬bad → r≤d → d<R → 4*Real.pi*μ≤tfReaction u) :
    propagationRHS R d μ (propagationStepError bad r R d μ p) (u-l/R^4)≤
      propagationRHS r d μ p u := by
  classical
  by_cases hdr : d<r
  · have hdR : d<R := hdr.trans_le hrR
    simp [propagationRHS,propagationCoreSource,propagationStepError,hdr,hdR,
      not_le_of_gt hdr,not_le_of_gt hdR]
  · have hrd : r≤d := le_of_not_gt hdr
    by_cases hdR : d<R
    · by_cases hb : bad
      · simp [propagationRHS,propagationCoreSource,propagationStepError,hdr,hdR,hrd,
          not_le_of_gt hdR,hb]
        nlinarith only [tfReaction_nonneg u]
      · have H := hgain hb hrd hdR
        simp only [propagationRHS,propagationCoreSource,propagationStepError,hb,false_and,
          ite_false,add_zero,hdR,ite_eq_left,not_le_of_gt hdR,hdr,hrd]
        nlinarith only [H]
    · have hRd : R≤d := le_of_not_gt hdR
      have H := tfReaction_monotone (show u-l/R^4≤u by
        have : 0≤l/R^4 := div_nonneg hl (pow_pos hR 4).le
        linarith only [this])
      simp only [propagationRHS,propagationCoreSource,propagationStepError,hdR,and_false,
        ite_false,add_zero,hdr,hRd,hrd,ite_eq_left]
      linarith only [H]

lemma propagation_physical_source {r R d μ p H l : ℝ} {_ : ℝ} {bad : Prop}
    (hμ : 0≤μ) (hp : 0≤p)
    (houter : R≤d → tfReaction (H-l/R^4)≤4*Real.pi*μ) :
    propagationRHS R d μ (propagationStepError bad r R d μ p) (H-l/R^4)≤4*Real.pi*μ := by
  have he := propagationStepError_nonneg (bad:=bad) (r:=r) (R:=R) (d:=d) hμ hp
  have hπ : 0<4*Real.pi := by positivity
  by_cases hdR : d<R
  · simp only [propagationRHS,propagationCoreSource,hdR,ite_eq_left,not_le_of_gt hdR,ite_false,add_zero]
    nlinarith only [he,hπ]
  · have hRd := le_of_not_gt hdR
    have H := houter hRd
    simp only [propagationRHS,propagationCoreSource,hdR,ite_false,hRd,ite_eq_left,zero_sub]
    nlinarith only [he,hπ,H]

lemma propagation_barrier_source {r R d μ p v : ℝ} {bad : Prop}
    (hRd : R≤d) (hμ : 0≤μ) (hp : 0≤p) :
    propagationRHS R d μ (propagationStepError bad r R d μ p) v≤tfReaction v := by
  have he := propagationStepError_nonneg (bad:=bad) (r:=r) (R:=R) (d:=d) hμ hp
  have hπ : 0<4*Real.pi := by positivity
  simp only [propagationRHS,propagationCoreSource,hRd,ite_eq_left,not_lt_of_ge hRd,ite_false,zero_sub]
  nlinarith only [he,hπ]

lemma propagationRHS_eq {r Z : ℝ} (f μ p : Position → ℝ) (x : Position) :
    propagationRHS r ‖x‖ (μ x) (p x) (Z*coulombKernel x+f x)=
      propagationCoreSource r ‖x‖ (μ x) (p x)+
        cutoffReaction r (fun y => Z*coulombKernel y+f y) x := by
  simp [propagationRHS,cutoffReaction,Set.indicator]

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma normalized_cap {d C v : ℝ} (hd : 0<d) (hcap : v≤C/d^4) : d^4*v≤C := by
  have H := (le_div_iff₀ (pow_pos hd 4)).mp hcap
  nlinarith only [H]

lemma normalized_barrier_lower {B r u : ℝ} (hB : 0≤B) (hr : 0<r)
    {x : Position} (hx : r≤‖x‖) (hu : propagationBarrier B r x≤u) : (7/8:ℝ)*B≤‖x‖^4*u := by
  have hd := hr.trans_le hx
  have H := (propagationBarrier_two_sided hB hr hx).1.trans hu
  exact le_trans (by rw [div_mul_cancel₀ _ (ne_of_gt (pow_pos hd 4))])
    (mul_le_mul_of_nonneg_right H (pow_pos hd 4).le) |>.trans_eq (mul_comm _ _)

lemma normalized_near_barrier_lower {B R L e v : ℝ} (hB : 0≤B) (hR : 0<R)
    (_ : 0≤L) (he : 0≤e) {x : Position} (hx : R≤‖x‖) (hx' : ‖x‖≤2*L*R)
    (hv : propagationBarrier B R x-2*e/R^4≤v) :
    (7/8:ℝ)*B-2*e*(2*L)^4≤‖x‖^4*v := by
  have hd := hR.trans_le hx
  have hl := (propagationBarrier_two_sided hB hR hx).1
  have H := mul_le_mul_of_nonneg_left hv (pow_pos hd 4).le
  have H' := mul_le_mul_of_nonneg_left hl (pow_pos hd 4).le
  have hh : ‖x‖^4*((7/8:ℝ)*B/‖x‖^4)=(7/8:ℝ)*B := by field_simp
  rw [hh] at H'
  have hp := pow_le_pow_left₀ hd.le hx' 4
  have he' : ‖x‖^4*(2*e/R^4)≤2*e*(2*L)^4 := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (pow_pos hR 4)).mpr
    calc
      _≤(2*L*R)^4*(2*e) := mul_le_mul_of_nonneg_right hp (by positivity)
      _=2*e*(2*L)^4*R^4 := by ring
  nlinarith only [H,H',he']

lemma near_active_old_field {u H M R l1 l2 e : ℝ} (_ : 0<R)
    (hcandidate : H-l2/R^4≤M) (hnear : M-(u-l1/R^4)<2*e/R^4) :
    H≤u-(l1-l2-2*e)/R^4 := by
  have he : (l1-l2-2*e)/R^4=l1/R^4-l2/R^4-2*e/R^4 := by ring
  rw [he]
  linarith only [hcandidate,hnear]

lemma near_active_physical_lower {v M B R e : ℝ} {x : Position}
    (hlower : propagationBarrier B R x≤M) (hnear : M-v<2*e/R^4) :
    propagationBarrier B R x-2*e/R^4≤v := by linarith only [hlower,hnear]

lemma propagation_near_old_gain {B C r R u H μ M l1 l2 e ξ hl hh : ℝ}
    (hB : 0≤B) (hr : 0<r) (hR : R=2*r) {x : Position}
    (hx : r≤‖x‖) (hhl : hl≤(7/8:ℝ)*B) (hhh : C≤hh)
    (hu : propagationBarrier B r x≤u ∧ u≤C/‖x‖^4)
    (hξ : 0≤ξ) (hgap : 16*ξ+2*e<l1-l2)
    (hinv : ∀ h∈Icc hl hh,Coulomb.tfScalarDensity h≤‖x‖^6*μ → h-ξ≤‖x‖^4*H)
    (hcandidate : H-l2/R^4≤M) (hnear : M-(u-l1/R^4)<2*e/R^4) :
    4*Real.pi*μ≤tfReaction u := by
  have hd := hr.trans_le hx
  have hRp : 0<R := by rw [hR]; positivity
  apply propagation_gain_density hd hRp (by rw [hR]; linarith only [hx]) hξ hgap
  · exact ⟨hhl.trans (normalized_barrier_lower hB hr hx hu.1),
      (normalized_cap hd hu.2).trans hhh⟩
  · exact hinv
  · exact near_active_old_field hRp hcandidate hnear

lemma propagation_near_physical_reaction {B C R L H μ M l2 e ξ hl hh : ℝ}
    (hB : 0≤B) (hR : 0<R) (hL : 0≤L) (he : 0≤e) {x : Position}
    (hx : R≤‖x‖) (hx' : ‖x‖≤2*L*R)
    (hhl : hl≤(7/8:ℝ)*B-2*e*(2*L)^4) (hhh : C≤hh)
    (hcap : H≤C/‖x‖^4) (hξ : 0≤ξ) (hl2 : 0≤l2) (hξl : ξ<l2)
    (hlower : propagationBarrier B R x≤M) (hnear : M-(H-l2/R^4)<2*e/R^4)
    (hinv : ∀ h∈Icc hl hh,‖x‖^6*μ≤Coulomb.tfScalarDensity h → ‖x‖^4*H≤h+ξ) :
    tfReaction (H-l2/R^4)≤4*Real.pi*μ := by
  have hd := hR.trans_le hx
  apply propagation_outer_reaction hR hx hξ hξl
  · constructor
    · exact hhl.trans (normalized_near_barrier_lower hB hR hL he hx hx'
        (near_active_physical_lower hlower hnear))
    · apply (normalized_cap hd ?_).trans hhh
      exact (sub_le_self _ (div_nonneg hl2 (pow_pos hR 4).le)).trans hcap
  · exact hinv

end NeutralAtom

end

end OAI
