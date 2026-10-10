import OAI.Geometry.NodalSets.Charts.TargetWarpedMetric

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

def roundProductMetric : SmoothMetric :=
  ambientWeightedMetric (fun _ ↦ innerSL ℝ) contMDiff_const
    (fun _ v w ↦ by change @inner ℝ AmbientBase _ v w = @inner ℝ AmbientBase _ w v; exact real_inner_comm w v)
    (fun _ v hv ↦ by
      change 0 < @inner ℝ AmbientBase _ v v
      rw [real_inner_self_eq_norm_sq]
      exact sq_pos_of_pos (norm_pos_iff.mpr hv))
    (fun _ ↦ 1) contMDiff_const (fun _ ↦ zero_lt_one)

lemma roundProductMetric_inner (x : Manifold5) (v : TangentSpace modelWithCorners x) :
    roundProductMetric.inner x v v =
      ‖(mfderiv (𝓡 4) 𝓘(ℝ,AmbientBase) (Subtype.val : Base → AmbientBase) x.1 v.1 : AmbientBase)‖^2 +
      ‖(mfderiv (𝓡 1) 𝓘(ℝ,ℂ) (fun z : Circle ↦ (z : ℂ)) x.2 v.2 : ℂ)‖^2 := by
  rw [roundProductMetric,ambientWeightedMetric_inner]
  let vb : AmbientBase := mfderiv (𝓡 4) 𝓘(ℝ,AmbientBase)
    (Subtype.val : Base → AmbientBase) x.1 v.1
  let vc : ℂ := mfderiv (𝓡 1) 𝓘(ℝ,ℂ) (fun z : Circle ↦ (z : ℂ)) x.2 v.2
  change innerSL ℝ vb vb + 1^2 * inner ℝ vc vc = ‖vb‖^2 + ‖vc‖^2
  have he (w : AmbientBase) : innerSL ℝ w w = ‖w‖^2 := by
    change @inner ℝ AmbientBase _ w w = _
    exact real_inner_self_eq_norm_sq w
  rw [he]
  simp only [one_pow, one_mul, real_inner_self_eq_norm_sq]

lemma ambientWeightedMetric_comparison
    (B : Base → AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ)
    (hB : ContMDiff (𝓡 4) 𝓘(ℝ,AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ) ∞ B)
    (hs : ∀ x v w, B x v w = B x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < B x v v)
    (q : Base → ℝ) (hq : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ q) (hpos : ∀ x, 0 < q x)
    (c C : ℝ)
    (hlo : ∀ x v, c*‖v‖^2 ≤ B x v v)
    (hhi : ∀ x v, B x v v ≤ C*‖v‖^2)
    (hql : ∀ x, c ≤ (q x)^2) (hqu : ∀ x, (q x)^2 ≤ C)
    (x : Manifold5) (v : TangentSpace modelWithCorners x) :
    c * roundProductMetric.inner x v v ≤
      (ambientWeightedMetric B hB hs hp q hq hpos).inner x v v ∧
    (ambientWeightedMetric B hB hs hp q hq hpos).inner x v v ≤
      C * roundProductMetric.inner x v v := by
  rw [ambientWeightedMetric_inner,roundProductMetric_inner]
  let vb : AmbientBase := mfderiv (𝓡 4) 𝓘(ℝ,AmbientBase)
    (Subtype.val : Base → AmbientBase) x.1 v.1
  let vc : ℂ := mfderiv (𝓡 1) 𝓘(ℝ,ℂ) (fun z : Circle ↦ (z : ℂ)) x.2 v.2
  change c * (‖vb‖^2 + ‖vc‖^2) ≤ B x.1 vb vb + q x.1 ^ 2 * inner ℝ vc vc ∧
    B x.1 vb vb + q x.1 ^ 2 * inner ℝ vc vc ≤ C * (‖vb‖^2 + ‖vc‖^2)
  rw [real_inner_self_eq_norm_sq]
  constructor
  · calc
      _ = c * _ + c * _ := mul_add _ _ _
      _ ≤ _ := add_le_add (hlo _ _) (mul_le_mul_of_nonneg_right (hql _) (sq_nonneg _))
  · calc
      _ ≤ C * _ + C * _ := add_le_add (hhi _ _)
          (mul_le_mul_of_nonneg_right (hqu _) (sq_nonneg _))
      _ = _ := (mul_add _ _ _).symm

lemma ambientWeightedMetric_lower_comparison
    (B : Base → AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ)
    (hB : ContMDiff (𝓡 4) 𝓘(ℝ,AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ) ∞ B)
    (hs : ∀ x v w, B x v w = B x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < B x v v)
    (q : Base → ℝ) (hq : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ q) (hpos : ∀ x, 0 < q x)
    (L : ℝ)
    (hlo : ∀ x v, ‖v‖^2 ≤ L^2 * B x v v)
    (hql : ∀ x, 1 ≤ L^2 * (q x)^2)
    (x : Manifold5) (v : TangentSpace modelWithCorners x) :
    roundProductMetric.inner x v v ≤
      L^2 * (ambientWeightedMetric B hB hs hp q hq hpos).inner x v v := by
  rw [ambientWeightedMetric_inner,roundProductMetric_inner]
  let vb : AmbientBase := mfderiv (𝓡 4) 𝓘(ℝ,AmbientBase)
    (Subtype.val : Base → AmbientBase) x.1 v.1
  let vc : ℂ := mfderiv (𝓡 1) 𝓘(ℝ,ℂ) (fun z : Circle ↦ (z : ℂ)) x.2 v.2
  change ‖vb‖^2 + ‖vc‖^2 ≤ L^2 * (B x.1 vb vb + q x.1 ^ 2 * inner ℝ vc vc)
  rw [real_inner_self_eq_norm_sq, mul_add]
  apply add_le_add (hlo _ _)
  have hh := mul_le_mul_of_nonneg_right (hql x.1)
    (sq_nonneg ‖vc‖)
  simpa only [one_mul,mul_assoc] using hh

end
end Yau.Target

end OAI
