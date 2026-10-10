import Mathlib

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert.LocalTaylor
open Metric Set Filter
open scoped ContDiff Topology
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma quadratic_bound {f : V → W} (hf : ContDiffAt ℝ 2 f 0)
    (hzero : fderiv ℝ f 0 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧ ∀ z : V, ‖z‖ ≤ r →
      ‖f z - f 0‖ ≤ C*‖z‖^2 ∧ ‖fderiv ℝ f z‖ ≤ C*‖z‖ := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ f) 0 := hf.fderiv_right (by norm_num)
  obtain ⟨K, s, hs, hK⟩ := (hd.hasStrictFDerivAt (by norm_num)).exists_lipschitzOnWith
  have he : ∀ᶠ z in 𝓝 (0 : V), DifferentiableAt ℝ f z :=
    (hf.eventually (by norm_num)).mono fun z hz => hz.differentiableAt (by norm_num)
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (inter_mem hs he)
  have h0 : (0 : V) ∈ closedBall 0 r := by simpa using hr.le
  have hder (z : V) (hz : ‖z‖ ≤ r) : ‖fderiv ℝ f z‖ ≤ (K : ℝ)*‖z‖ := by
    have hzm : z ∈ closedBall 0 r := by simpa using hz
    simpa [dist_eq_norm, hzero] using hK.norm_sub_le (hball hzm).1 (hball h0).1
  refine ⟨K, K.coe_nonneg, r, hr, fun z hz => ⟨?_, hder z hz⟩⟩
  have hsub : closedBall (0 : V) ‖z‖ ⊆ closedBall 0 r := closedBall_subset_closedBall hz
  have hb : ∀ y ∈ closedBall (0 : V) ‖z‖, ‖fderiv ℝ f y‖ ≤ (K : ℝ)*‖z‖ := by
    intro y hy
    have hnorm : ‖y‖ ≤ ‖z‖ := by simpa using hy
    exact (hder y (hnorm.trans hz)).trans (mul_le_mul_of_nonneg_left hnorm K.coe_nonneg)
  have hm := (convex_closedBall (0 : V) ‖z‖).norm_image_sub_le_of_norm_fderiv_le
    (fun y hy => (hball (hsub hy)).2) hb
    (show (0 : V) ∈ closedBall 0 ‖z‖ by simp)
    (show z ∈ closedBall 0 ‖z‖ by simp)
  simpa [pow_two, mul_assoc] using hm

lemma linear_bound {f : V → W} (hf : ContDiffAt ℝ 1 f 0) (hzero : f 0 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧ ∀ z : V, ‖z‖ ≤ r → ‖f z‖ ≤ C*‖z‖ := by
  obtain ⟨K, s, hs, hK⟩ := (hf.hasStrictFDerivAt (by norm_num)).exists_lipschitzOnWith
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hs
  refine ⟨K, K.coe_nonneg, r, hr, fun z hz => ?_⟩
  have h0 : (0 : V) ∈ closedBall 0 r := by simpa using hr.le
  have hz' : z ∈ closedBall 0 r := by simpa using hz
  simpa [dist_eq_norm, hzero] using hK.norm_sub_le (hball hz') (hball h0)

end TamingCompatibility.GeometricHilbert.LocalTaylor

end

end OAI
