import OAI.Geometry.SurfaceImmersion.Atlas.ConvexQuadraticPhase
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace OAI

/-! Flat cutoffs for the actual circular disks in primitive preparation.
Their centers and radii are smooth parameters. -/
noncomputable section
open Set Function Filter
open scoped Topology
open scoped ContDiff

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

def circularRadiusSquared (c p : Base) : ℝ := (p.1-c.1)^2 + (p.2-c.2)^2

def circularFlatBump (c : Base) (r : ℝ) (p : Base) : ℝ :=
  expNegInvGlue (r^2 - circularRadiusSquared c p)

lemma circularRadiusSquared_smooth (c : Base) :
    ContDiff ℝ ∞ (circularRadiusSquared c) := by
  unfold circularRadiusSquared
  fun_prop

lemma circularFlatBump_joint_smooth :
    ContDiff ℝ ∞ (fun z : (Base × ℝ) × Base => circularFlatBump z.1.1 z.1.2 z.2) := by
  apply expNegInvGlue.contDiff.comp
  unfold circularRadiusSquared
  fun_prop

lemma circularFlatBump_smooth (c : Base) (r : ℝ) :
    ContDiff ℝ ∞ (circularFlatBump c r) := by
  exact expNegInvGlue.contDiff.comp (contDiff_const.sub (circularRadiusSquared_smooth c))

lemma circularFlatBump_nonneg (c : Base) (r : ℝ) (p : Base) :
    0 ≤ circularFlatBump c r p := expNegInvGlue.nonneg _

lemma circularFlatBump_zero_iff (c : Base) (r : ℝ) (p : Base) :
    circularFlatBump c r p = 0 ↔ r^2 ≤ circularRadiusSquared c p := by
  simp only [circularFlatBump, expNegInvGlue.zero_iff_nonpos, sub_nonpos]

lemma circularFlatBump_pos_iff (c : Base) (r : ℝ) (p : Base) :
    0 < circularFlatBump c r p ↔ circularRadiusSquared c p < r^2 := by
  constructor
  · intro hp
    apply lt_of_not_ge
    intro hge
    exact (ne_of_gt hp) ((circularFlatBump_zero_iff c r p).mpr hge)
  · intro hp
    exact expNegInvGlue.pos_of_pos (sub_pos.mpr hp)

lemma circularFlatBump_support (c : Base) (r : ℝ) :
    support (circularFlatBump c r) = {p | circularRadiusSquared c p < r^2} := by
  ext p
  change ¬ circularFlatBump c r p = 0 ↔ circularRadiusSquared c p < r^2
  rw [circularFlatBump_zero_iff,not_le]

lemma circularRadiusSquared_le_norm {c p : Base} {r : ℝ}
    (hp : circularRadiusSquared c p ≤ r^2) : ‖p-c‖ ≤ |r| := by
  have h₁ : |p.1-c.1| ≤ |r| := by
    apply sq_le_sq.mp
    unfold circularRadiusSquared at hp
    nlinarith [sq_nonneg (p.2-c.2)]
  have h₂ : |p.2-c.2| ≤ |r| := by
    apply sq_le_sq.mp
    unfold circularRadiusSquared at hp
    nlinarith [sq_nonneg (p.1-c.1)]
  simpa only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs, max_le_iff]
    using And.intro h₁ h₂

lemma circularFlatBump_hasCompactSupport (c : Base) (r : ℝ) :
    HasCompactSupport (circularFlatBump c r) := by
  apply (isCompact_closedBall c |r|).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal
  · intro p hp
    rw [circularFlatBump_support] at hp
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact circularRadiusSquared_le_norm hp.le
  · exact Metric.isClosed_closedBall

lemma circularRadiusSquared_derivative (c p v : Base) :
    coordDeriv v (circularRadiusSquared c) p =
      2*((p.1-c.1)*v.1 + (p.2-c.2)*v.2) := by
  have h₁ := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := p) |>.sub_const c.1
  have h₂ := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := p) |>.sub_const c.2
  have hd := (h₁.pow 2).add (h₂.pow 2)
  have he : circularRadiusSquared c =
      ((fun x : Base => ((ContinuousLinearMap.fst ℝ ℝ ℝ) x-c.1)^2) +
        fun x : Base => ((ContinuousLinearMap.snd ℝ ℝ ℝ) x-c.2)^2) := rfl
  change (fderiv ℝ (circularRadiusSquared c) p) v = _
  rw [he,hd.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', two_smul, smul_eq_mul]
  ring

lemma circularRadiusSquared_boundary_regular (c : Base) {r : ℝ} (hr : 0 < r)
    {p : Base} (hp : circularRadiusSquared c p = r^2) :
    phaseDerivative (circularRadiusSquared c) p ≠ 0 := by
  intro hz
  have hx := congrArg Prod.fst hz
  have hy := congrArg Prod.snd hz
  change coordDeriv dx (circularRadiusSquared c) p = 0 at hx
  change coordDeriv dy (circularRadiusSquared c) p = 0 at hy
  rw [circularRadiusSquared_derivative] at hx hy
  simp only [dx, dy] at hx hy
  unfold circularRadiusSquared at hp
  nlinarith [sq_pos_of_pos hr]

lemma circularFlatBump_spatial_derivative (q : Base × ℝ) (p : Base) :
    fderiv ℝ (circularFlatBump q.1 q.2) p =
      (fderiv ℝ (fun z : (Base × ℝ) × Base => circularFlatBump z.1.1 z.1.2 z.2) (q,p)).comp
        (ContinuousLinearMap.inr ℝ (Base × ℝ) Base) := by
  have hi : HasFDerivAt (fun x : Base => (q,x))
      (ContinuousLinearMap.inr ℝ (Base × ℝ) Base) p := by
    exact (hasFDerivAt_const q p).prodMk (hasFDerivAt_id p)
  exact (circularFlatBump_joint_smooth.differentiable (by simp) (q,p) |>.hasFDerivAt.comp p hi).fderiv

lemma circularFlatBump_spatial_derivative_continuous :
    Continuous (fun z : (Base × ℝ) × Base => fderiv ℝ (circularFlatBump z.1.1 z.1.2) z.2) := by
  have hc := (circularFlatBump_joint_smooth.continuous_fderiv (by simp)).clm_comp
    (continuous_const : Continuous (fun _ : (Base × ℝ) × Base =>
      ContinuousLinearMap.inr ℝ (Base × ℝ) Base))
  simpa only [circularFlatBump_spatial_derivative] using hc

private lemma compact_parameter_nearby {E : Type*} [NormedAddCommGroup E]
    (f : (Base × ℝ) × Base → E) (hf : Continuous f)
    {K : Set Base} (hK : IsCompact K) (q : Base × ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ q' : Base × ℝ, ‖q'-q‖ < delta → ∀ p ∈ K,
      ‖f (q',p)-f (q,p)‖ < eps := by
  have hc : Continuous (fun z : (Base × ℝ) × Base => ‖f z-f (q,z.2)‖) :=
    (hf.sub (hf.comp (continuous_const.prodMk continuous_snd))).norm
  have hev : ∀ᶠ q' in 𝓝 q, ∀ p ∈ K, ‖f (q',p)-f (q,p)‖ < eps := by
    apply hK.eventually_forall_of_forall_eventually
    intro p _
    have he : ‖f (q,p)-f (q,p)‖ < eps := by simpa only [sub_self,norm_zero] using heps
    exact (hc.continuousAt (x := (q,p))).eventually (gt_mem_nhds he)
  obtain ⟨delta,hdelta,hnear⟩ := Metric.eventually_nhds_iff.mp hev
  exact ⟨delta,hdelta,fun q' hq' => hnear (by simpa only [dist_eq_norm] using hq')⟩

/-- Moving a center or radius changes its actual flat cutoff by an
arbitrarily small amount in C¹ on any fixed compact coordinate set. -/
theorem circularFlatBump_compact_C1 {K : Set Base} (hK : IsCompact K)
    (q : Base × ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ q' : Base × ℝ, ‖q'-q‖ < delta → ∀ p ∈ K,
      |circularFlatBump q'.1 q'.2 p - circularFlatBump q.1 q.2 p| < eps ∧
      ‖fderiv ℝ (circularFlatBump q'.1 q'.2) p -
        fderiv ℝ (circularFlatBump q.1 q.2) p‖ < eps := by
  let f : (Base × ℝ) × Base → ℝ × (Base →L[ℝ] ℝ) := fun z =>
    (circularFlatBump z.1.1 z.1.2 z.2, fderiv ℝ (circularFlatBump z.1.1 z.1.2) z.2)
  have hf : Continuous f :=
    circularFlatBump_joint_smooth.continuous.prodMk circularFlatBump_spatial_derivative_continuous
  obtain ⟨delta,hdelta,hnear⟩ := compact_parameter_nearby f hf hK q heps
  refine ⟨delta,hdelta,fun q' hq' p hp => ?_⟩
  have hh := hnear q' hq' p hp
  constructor
  · exact (norm_fst_le (f (q',p)-f (q,p))).trans_lt hh
  · exact (norm_snd_le (f (q',p)-f (q,p))).trans_lt hh

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
