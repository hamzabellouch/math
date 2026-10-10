import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialHeckeWeight

namespace OAI

/-! Mellin identities of the actual compact radial tests. -/
noncomputable section
open Set
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadialWeight_mellinConvergent (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0) (s : ℂ) : MellinConvergent (star W : ℝ → ℂ) s := by
  have hs : tsupport (star W)⊆Ici (2:ℝ) := by
    apply closure_minimal ?_ isClosed_Ici
    intro v hv
    by_contra hn
    apply hv
    change star (W v)=0
    rw [hW v (le_of_not_ge hn),star_zero]
  exact smooth_mellin_convergent (star W) (star W).hasCompactSupport
    (fun v hv => lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (hs hv)) (star W).continuous s

lemma cubicThetaZeroRadialTest_add (W V : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0) (hV : ∀ v≤(2:ℝ),V v=0) (s : ℂ) :
    cubicThetaZeroRadialTest (W+V) s=cubicThetaZeroRadialTest W s+cubicThetaZeroRadialTest V s := by
  have hsum : ∀ v≤(2:ℝ),(W+V) v=0 := by
    intro v hv
    change W v+V v=0
    rw [hW v hv,hV v hv,add_zero]
  rw [cubicThetaZeroRadialWindow_mellin _ hsum,cubicThetaZeroRadialWindow_mellin W hW,
    cubicThetaZeroRadialWindow_mellin V hV]
  have he : star (↑(W+V) : ℝ → ℂ)=(fun v => (star W : ℝ → ℂ) v+(star V : ℝ → ℂ) v) := by
    funext v
    change star (W v+V v)=star (W v)+star (V v)
    exact star_add _ _
  rw [he]
  exact (hasMellin_add (cubicThetaRadialWeight_mellinConvergent W hW (-s))
    (cubicThetaRadialWeight_mellinConvergent V hV (-s))).2

lemma cubicThetaZeroRadialTest_smul (c : ℂ) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0) (s : ℂ) :
    cubicThetaZeroRadialTest (c • W) s=star c*cubicThetaZeroRadialTest W s := by
  have hc : ∀ v≤(2:ℝ),(c • W) v=0 := by
    intro v hv
    change c*W v=0
    rw [hW v hv,mul_zero]
  rw [cubicThetaZeroRadialWindow_mellin _ hc,cubicThetaZeroRadialWindow_mellin W hW]
  have he : star (↑(c • W) : ℝ → ℂ)=(fun v => star c • (star W : ℝ → ℂ) v) := by
    funext v
    change star (c*W v)=star c*star (W v)
    rw [star_mul,mul_comm]
  rw [he,mellin_const_smul]
  rfl

lemma cubicThetaZeroRadialTest_scale (r : ℝ) (hr : 0<r) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0)
    (hS : ∀ v≤(2:ℝ),cubicThetaRadialWeightScale r hr W v=0) (s : ℂ) :
    cubicThetaZeroRadialTest (cubicThetaRadialWeightScale r hr W) s=
      (r:ℂ)^s*cubicThetaZeroRadialTest W s := by
  rw [cubicThetaZeroRadialWindow_mellin _ hS,cubicThetaZeroRadialWindow_mellin W hW,
    cubicThetaRadialWeightScale_mellin,neg_neg]

lemma cubicThetaZeroRadialTest_hecke (r : ℝ) (hr : 0<r) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0)
    (hA : ∀ v≤(2:ℝ),cubicThetaRadialWeightScale r⁻¹ (inv_pos.mpr hr) W v=0)
    (hB : ∀ v≤(2:ℝ),cubicThetaRadialWeightScale r hr W v=0) (s : ℂ) :
    cubicThetaZeroRadialTest (cubicThetaRadialHeckeWeight r hr W) s=
      ((r:ℂ)^2*(r⁻¹:ℝ)^s+(r:ℂ)^s)*cubicThetaZeroRadialTest W s := by
  unfold cubicThetaRadialHeckeWeight
  rw [cubicThetaZeroRadialTest_add _ _ (by
    intro v hv
    change (r:ℂ)^2*cubicThetaRadialWeightScale r⁻¹ (inv_pos.mpr hr) W v=0
    rw [hA v hv,mul_zero]) hB,
    cubicThetaZeroRadialTest_smul _ _ hA,
    cubicThetaZeroRadialTest_scale _ _ W hW hA,
    cubicThetaZeroRadialTest_scale _ _ W hW hB]
  simp only [star_pow,Complex.star_def,Complex.conj_ofReal]
  ring

end CubicFirstMoment

end

end OAI
