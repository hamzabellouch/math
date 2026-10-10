import Mathlib.Analysis.Calculus.MeanValue
import OAI.Geometry.NodalSets.Charts.BallGeometry

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma choose_sign_subball_radius {tau L : ℝ} (ht : 0 < tau) (ht1 : tau < 1) (hL : 0 ≤ L) :
    ∃ r > 0, r < tau/4 ∧ r < (1-tau)/2 ∧ 4*L*r < 1 := by
  let r := min (tau/8) (min ((1-tau)/4) (1/(16*(L+1))))
  have hr : 0 < r := by dsimp [r]; positivity
  have h1 : r ≤ tau/8 := min_le_left _ _
  have h2 : r ≤ (1-tau)/4 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : r ≤ 1/(16*(L+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hprod : 16*(L+1)*r ≤ 1 := by
    have h := (le_div_iff₀ (by positivity : 0 < 16*(L+1))).mp h3
    nlinarith
  refine ⟨r,hr,by linarith,by linarith,?_⟩
  nlinarith [mul_nonneg hL hr.le]

lemma strict_sign_subballs (f : Coord → ℝ) (hf : ContDiff ℝ ∞ f)
    {tau r L : ℝ} (ht : 0 ≤ tau) (hr : 0 ≤ r) (hL : 0 ≤ L)
    (htr : tau+r ≤ 1) (hsmall : 4*L*r < 1) (j : Fin 4)
    (hpos : 1 ≤ f 0) (hneg : f (tau • Pi.single j 1) ≤ -1)
    (hgrad : ∀ x : Coord, sourceEuclideanNorm x ≤ 1 →
      sourceEuclideanNorm (fun i ↦ fderiv ℝ f x (Pi.single i 1)) ≤ L) :
    (∀ v : Coord, sourceEuclideanNorm v ≤ r → sourceEuclideanNorm v ≤ 1 ∧ 0 < f v) ∧
    (∀ v : Coord, sourceEuclideanNorm (v-tau • Pi.single j 1) ≤ r →
      sourceEuclideanNorm v ≤ 1 ∧ f v < 0) := by
  have hdiff : ∀ x ∈ {x : Coord | sourceEuclideanNorm x ≤ 1}, DifferentiableAt ℝ f x :=
    fun x _ ↦ hf.differentiable (by simp) x
  have hb : ∀ x ∈ {x : Coord | sourceEuclideanNorm x ≤ 1}, ‖fderiv ℝ f x‖ ≤ 4*L := by
    intro x hx
    exact (covector_norm_le_source _).trans (by linarith [hgrad x hx])
  have hc := sourceEuclideanBall_convex 1
  obtain ⟨hinside0,hinside1⟩ := source_sign_subballs_inside ht hr htr j
  constructor
  · intro v hv
    have hv1 := hinside0 v hv
    have hh := hc.norm_image_sub_le_of_norm_fderiv_le hdiff hb
      (show (0:Coord) ∈ {x | sourceEuclideanNorm x ≤ 1} by simp [sourceEuclideanNorm]) hv1
    have hnv : ‖v-(0:Coord)‖ ≤ r := by simpa using (norm_le_sourceEuclideanNorm v).trans hv
    have hb' : |f v-f 0| ≤ 4*L*r := by
      exact hh.trans (mul_le_mul_of_nonneg_left hnv (by positivity))
    refine ⟨hv1,?_⟩
    have hh' := (abs_le.mp hb').1
    linarith
  · intro v hv
    have hv1 := hinside1 v hv
    have ht1 : sourceEuclideanNorm (tau • Pi.single j (1:ℝ)) ≤ 1 := by
      rw [sourceEuclideanNorm_single,abs_of_nonneg ht]
      linarith
    have hh := hc.norm_image_sub_le_of_norm_fderiv_le hdiff hb ht1 hv1
    have hnv := (norm_le_sourceEuclideanNorm (v-tau • Pi.single j 1)).trans hv
    have hb' : |f v-f (tau • Pi.single j 1)| ≤ 4*L*r :=
      hh.trans (mul_le_mul_of_nonneg_left hnv (by positivity))
    refine ⟨hv1,?_⟩
    have hh' := (abs_le.mp hb').2
    linarith

end
end Yau.Geometry

end OAI
