import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.RadialCutoff

namespace OAI

section
section

section

section
noncomputable section
namespace TamingCompatibility.RadialPotential
open Set
open scoped ContDiff RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def logGradientProfile (s : ℝ) (z v : E) : ℝ :=
  (s^2+‖z‖^2)⁻¹ * ⟪z,v⟫
def sqrtGradientProfile (s : ℝ) (z v : E) : ℝ :=
  (Real.sqrt (s^2+‖z‖^2))⁻¹ * ⟪z,v⟫

lemma logGradientProfile_eq_fderiv {s : ℝ} (hs : 0 < s) (z v : E) :
    logGradientProfile s z v = fderiv ℝ (logPotential s) z v := by
  rw [logPotential_fderiv hs]
  rfl
lemma sqrtGradientProfile_eq_fderiv {s : ℝ} (hs : 0 < s) (z v : E) :
    sqrtGradientProfile s z v = fderiv ℝ (sqrtPotential s) z v := by
  rw [sqrtPotential_fderiv hs]
  rfl

lemma logGradientProfile_joint_smooth_at (v : E) {p : ℝ × E}
    (hp : 0 < p.1^2+‖p.2‖^2) :
    ContDiffAt ℝ ∞ (fun q : ℝ × E => logGradientProfile q.1 q.2 v) p := by
  have h : ContDiffAt ℝ ∞ (fun q : ℝ × E => q.1^2+‖q.2‖^2) p :=
    (contDiff_fst.pow 2).contDiffAt.add ((contDiff_norm_sq ℝ).comp contDiff_snd).contDiffAt
  exact (h.inv (ne_of_gt hp)).mul
    ((contDiff_id.inner ℝ contDiff_const).comp contDiff_snd).contDiffAt

lemma sqrtGradientProfile_joint_smooth_at (v : E) {p : ℝ × E}
    (hp : 0 < p.1^2+‖p.2‖^2) :
    ContDiffAt ℝ ∞ (fun q : ℝ × E => sqrtGradientProfile q.1 q.2 v) p := by
  have h : ContDiffAt ℝ ∞ (fun q : ℝ × E => q.1^2+‖q.2‖^2) p :=
    (contDiff_fst.pow 2).contDiffAt.add ((contDiff_norm_sq ℝ).comp contDiff_snd).contDiffAt
  exact ((h.sqrt (ne_of_gt hp)).inv (ne_of_gt (Real.sqrt_pos.mpr hp))).mul
    ((contDiff_id.inner ℝ contDiff_const).comp contDiff_snd).contDiffAt

lemma cutoff_log_gradient_derivatives_bounded (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (h0 : (0:E) ∉ tsupport χ) (v : E) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) 1, ∀ z : E,
      ‖iteratedFDeriv ℝ n (fun x => χ x*logGradientProfile s x v) z‖ ≤ C := by
  apply cutoff_slice_derivatives_bounded χ hχc (fun s z => logGradientProfile s z v) _ n
  apply cutoff_joint_smooth χ hχ h0 (fun s z => logGradientProfile s z v)
  intro p hp
  apply logGradientProfile_joint_smooth_at
  have hz : 0 < ‖p.2‖ := norm_pos_iff.mpr hp
  nlinarith [sq_nonneg p.1]

lemma cutoff_sqrt_gradient_derivatives_bounded (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (h0 : (0:E) ∉ tsupport χ) (v : E) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) 1, ∀ z : E,
      ‖iteratedFDeriv ℝ n (fun x => χ x*sqrtGradientProfile s x v) z‖ ≤ C := by
  apply cutoff_slice_derivatives_bounded χ hχc (fun s z => sqrtGradientProfile s z v) _ n
  apply cutoff_joint_smooth χ hχ h0 (fun s z => sqrtGradientProfile s z v)
  intro p hp
  apply sqrtGradientProfile_joint_smooth_at
  have hz : 0 < ‖p.2‖ := norm_pos_iff.mpr hp
  nlinarith [sq_nonneg p.1]

lemma logGradientProfile_scale {r s : ℝ} (hr : 0 < r) (z v : E) :
    r * logGradientProfile (r*s) (r • z) v = logGradientProfile s z v := by
  simp only [logGradientProfile,norm_smul,Real.norm_of_nonneg (le_of_lt hr),real_inner_smul_left]
  rw [show (r*s)^2+(r*‖z‖)^2 = r^2*(s^2+‖z‖^2) by ring,mul_inv_rev]
  field_simp

lemma sqrtGradientProfile_scale {r s : ℝ} (hr : 0 < r) (z v : E) :
    sqrtGradientProfile (r*s) (r • z) v = sqrtGradientProfile s z v := by
  simp only [sqrtGradientProfile,norm_smul,Real.norm_of_nonneg (le_of_lt hr),real_inner_smul_left]
  rw [show (r*s)^2+(r*‖z‖)^2 = r^2*(s^2+‖z‖^2) by ring,
    Real.sqrt_mul (sq_nonneg r),Real.sqrt_sq_eq_abs,abs_of_pos hr,mul_inv_rev]
  field_simp
end TamingCompatibility.RadialPotential
end
end

end

section

noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Function Metric
open scoped ContDiff Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]

def unitCutoff : E → ℝ := (⟨1, 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : E))

def scaledCutoff (r : ℝ) (z : E) : ℝ := unitCutoff (r⁻¹ • z)

def shellCutoff (r : ℝ) (z : E) : ℝ := scaledCutoff (2*r) z - scaledCutoff r z

lemma unitCutoff_smooth : ContDiff ℝ ∞ (unitCutoff : E → ℝ) :=
  ContDiffBump.contDiff _

lemma unitCutoff_one {z : E} (hz : ‖z‖ ≤ 1) : unitCutoff z = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, dist_zero_right] using hz

lemma unitCutoff_zero {z : E} (hz : 2 ≤ ‖z‖) : unitCutoff z = 0 := by
  apply ContDiffBump.zero_of_le_dist
  simpa only [dist_zero_right] using hz

lemma unitCutoff_nonneg (z : E) : 0 ≤ unitCutoff z := ContDiffBump.nonneg _
lemma unitCutoff_le_one (z : E) : unitCutoff z ≤ 1 := ContDiffBump.le_one _

lemma scaledCutoff_smooth (r : ℝ) : ContDiff ℝ ∞ (scaledCutoff r : E → ℝ) :=
  unitCutoff_smooth.comp (contDiff_const.smul contDiff_id)

lemma scaledCutoff_one {r : ℝ} (hr : 0 < r) {z : E} (hz : ‖z‖ ≤ r) :
    scaledCutoff r z = 1 := by
  apply unitCutoff_one
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  exact (inv_mul_le_iff₀ hr).mpr (by simpa using hz)

lemma scaledCutoff_zero {r : ℝ} (hr : 0 < r) {z : E} (hz : 2*r ≤ ‖z‖) :
    scaledCutoff r z = 0 := by
  apply unitCutoff_zero
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  exact (le_inv_mul_iff₀ hr).mpr (by simpa [mul_comm] using hz)

lemma scaledCutoff_nonneg (r : ℝ) (z : E) : 0 ≤ scaledCutoff r z := unitCutoff_nonneg _
lemma scaledCutoff_le_one (r : ℝ) (z : E) : scaledCutoff r z ≤ 1 := unitCutoff_le_one _

lemma scaledCutoff_tsupport {r : ℝ} (hr : 0 < r) :
    tsupport (scaledCutoff r : E → ℝ) ⊆ Metric.closedBall 0 (2*r) := by
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  simp only [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  exact hz (scaledCutoff_zero hr (le_of_lt (lt_of_not_ge h)))

lemma scaledCutoff_compact [ProperSpace E] {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (scaledCutoff r : E → ℝ) :=
  (isCompact_closedBall (0:E) (2*r)).of_isClosed_subset (isClosed_tsupport _) (scaledCutoff_tsupport hr)

lemma shellCutoff_smooth (r : ℝ) : ContDiff ℝ ∞ (shellCutoff r : E → ℝ) :=
  (scaledCutoff_smooth _).sub (scaledCutoff_smooth _)

lemma shellCutoff_zero_inner {r : ℝ} (hr : 0 < r) {z : E} (hz : ‖z‖ ≤ r) :
    shellCutoff r z = 0 := by
  rw [shellCutoff, scaledCutoff_one (by positivity : 0 < 2*r) (by linarith),
    scaledCutoff_one hr hz, sub_self]

lemma shellCutoff_tsupport {r : ℝ} (hr : 0 < r) :
    tsupport (shellCutoff r : E → ℝ) ⊆ Metric.closedBall 0 (4*r) \ Metric.ball 0 r := by
  apply closure_minimal _ (isClosed_closedBall.sdiff isOpen_ball)
  intro z hz
  constructor
  · simp only [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    have hz2 : 2*r ≤ ‖z‖ := by linarith [lt_of_not_ge h]
    have hz4 : 2*(2*r) ≤ ‖z‖ := by linarith [lt_of_not_ge h]
    apply hz
    rw [shellCutoff, scaledCutoff_zero (by positivity : 0 < 2*r) hz4,
      scaledCutoff_zero hr hz2, sub_self]
  · simp only [Metric.mem_ball, dist_zero_right, not_lt]
    by_contra h
    exact hz (shellCutoff_zero_inner hr (le_of_lt (lt_of_not_ge h)))

lemma shellCutoff_compact [ProperSpace E] {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (shellCutoff r : E → ℝ) :=
  (isCompact_closedBall (0:E) (4*r)).of_isClosed_subset (isClosed_tsupport _)
    (fun _z hz => (shellCutoff_tsupport hr hz).1)

lemma shellCutoff_abs_le_one (r : ℝ) (z : E) : |shellCutoff r z| ≤ 1 := by
  rw [abs_le]
  constructor <;> dsimp only [shellCutoff] <;>
    linarith [scaledCutoff_nonneg r z, scaledCutoff_le_one r z,
      scaledCutoff_nonneg (2*r) z, scaledCutoff_le_one (2*r) z]

lemma scaledCutoff_scale {r : ℝ} (hr : r ≠ 0) (a : ℝ) (z : E) :
    scaledCutoff (r*a) (r • z) = scaledCutoff a z := by
  dsimp only [scaledCutoff]
  congr 1
  rw [smul_smul, mul_inv_rev]
  field_simp

lemma shellCutoff_scale {r : ℝ} (hr : r ≠ 0) (z : E) :
    shellCutoff r (r • z) = shellCutoff 1 z := by
  dsimp only [shellCutoff]
  rw [mul_comm (2:ℝ) r, scaledCutoff_scale hr]
  have h := scaledCutoff_scale hr (1:ℝ) z
  simpa using congrArg (fun a => scaledCutoff (2:ℝ) z - a) h

lemma dyadic_cutoff_telescope (r : ℝ) (N : ℕ) (z : E) :
    scaledCutoff r z + ∑ j ∈ Finset.range N, shellCutoff (r*2^j) z =
      scaledCutoff (r*2^N) z := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    simp only [shellCutoff, pow_succ]
    rw [show 2*(r*2^N) = r*(2^N*2) by ring]
    ring

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def sourcePiece (χ : E → ℝ) (f : E → V) : E → V := fun z => χ z • f z

lemma source_finite_reconstruction (f : E → V) {r R : ℝ} (hr : 0 < r)
    (hf : ∀ z, R < ‖z‖ → f z = 0) (N : ℕ) (hN : R ≤ r*2^N) :
    f = sourcePiece (scaledCutoff r) f +
      ∑ j ∈ Finset.range N, sourcePiece (shellCutoff (r*2^j)) f := by
  ext z
  change f z = scaledCutoff r z • f z +
    (∑ j ∈ Finset.range N, sourcePiece (shellCutoff (r*2^j)) f) z
  simp only [Finset.sum_apply, sourcePiece]
  rw [← Finset.sum_smul, ← add_smul, dyadic_cutoff_telescope]
  by_cases hz : ‖z‖ ≤ r*2^N
  · rw [scaledCutoff_one (mul_pos hr (by positivity)) hz, one_smul]
  · rw [hf z (lt_of_le_of_lt hN (lt_of_not_ge hz)), smul_zero]

lemma exists_dyadic_reconstruction_scale {r : ℝ} (hr : 0 < r) (R : ℝ) :
    ∃ N : ℕ, R ≤ r*2^N := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (R/r) (by norm_num : (1:ℝ) < 2)
  exact ⟨N, by simpa [mul_comm] using (div_le_iff₀ hr).mp (le_of_lt hN)⟩

lemma map_source_finite_reconstruction {W : Type*} [AddCommGroup W] [Module ℝ W]
    (B : (E → V) →ₗ[ℝ] W) (f : E → V) {r R : ℝ} (hr : 0 < r)
    (hf : ∀ z, R < ‖z‖ → f z = 0) (N : ℕ) (hN : R ≤ r*2^N) :
    B f = B (sourcePiece (scaledCutoff r) f) +
      ∑ j ∈ Finset.range N, B (sourcePiece (shellCutoff (r*2^j)) f) := by
  conv_lhs => rw [source_finite_reconstruction f hr hf N hN]
  rw [map_add, map_sum]

end TamingCompatibility.RadialPotential

end
end

end
end

end OAI
