import Mathlib
import OAI.Combinatorics.KMedian.Projection.Expansion
import OAI.Combinatorics.KMedian.Projection.MassNormalize
import OAI.Combinatorics.KMedian.Projection.Rounding

namespace OAI

section Inline_PCPProjectionContraction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B T : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B] [Fintype T]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
variable (G : BiProjection U V D S A B)

noncomputable def collisionNorm (f : U → A → T → ℝ) : ℝ :=
  MixedNorm.norm (fun v (p : B × T) => G.push f v p.1 p.2)

omit [Fintype U] [Fintype D] [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B] in
lemma collisionNorm_sq (f : U → A → T → ℝ) : G.collisionNorm f^2=G.collision f :=
  MixedNorm.norm_sq _
omit [Fintype U] [Fintype D] [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B] in
lemma collisionNorm_nonneg (f : U → A → T → ℝ) : 0 ≤ G.collisionNorm f :=
  MixedNorm.norm_nonneg _
omit [Fintype U] [Fintype D] [Nonempty U] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B] in
lemma collisionNorm_difference (f g : U → A → T → ℝ) :
    G.collisionNorm f ≤ G.collisionNorm g+G.collisionNorm (fun u a t => f u a t-g u a t) := by
  unfold collisionNorm
  rw [G.push_sub]
  exact MixedNorm.difference_bound _ _
omit [Fintype U] [Fintype D] [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B] in
lemma collisionNorm_le (f : U → A → T → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (h : G.collision f≤b^2) : G.collisionNorm f≤b := MixedNorm.norm_le_of_sq hb h

theorem collision_contraction (s γ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hs : G.Sound s) (hG : G.Expands γ)
    (f : U → A → T → ℝ) (hf : ∀ u a t, 0 ≤ f u a t) (M : ℝ) (hM : 0 ≤ M)
    (hm : ∀ u, ∑ t, (∑ a, f u a t)^2≤M^2) :
    G.collision f ≤ (1-γ*((1-s)/4)^2)*M^2 := by
  let : Inhabited A := ⟨Classical.choice inferInstance⟩
  let H : T → ℝ := fun t => 𝔼 u, ∑ a, f u a t
  let g : U → A → T → ℝ := fun u a t => MassNormalize.normalized (fun a => f u a t) (H t) a
  let W : ℝ := MixedNorm.sq (fun u t => (∑ a, f u a t)-H t)
  have hH (t : T) : 0 ≤ H t := expect_nonneg (fun u _ => sum_nonneg (fun a _ => hf u a t))
  have hg (u : U) (a : A) (t : T) : 0 ≤ g u a t := MassNormalize.nonneg _ (fun a => hf u a t) _ (hH t) a
  have hgt (u : U) (t : T) : ∑ a, g u a t=H t := MassNormalize.total _ _
  have hmean : ∑ t, H t^2≤M^2 := (MixedNorm.sq_mean_le (fun u t => ∑ a, f u a t)).trans
    (MixedNorm.sq_le_uniform _ _ hm)
  have hcg : G.collision g≤ s *M^2 := (G.collision_sound s hs g hg H hH hgt).trans
    (mul_le_mul_of_nonneg_left hmean hs0)
  have herr : G.collision (fun u a t => f u a t-g u a t)≤W := by
    have hh := G.collision_le_abs_total (fun u a t => f u a t-g u a t)
    have he (u : U) (t : T) : (∑ a, |f u a t-g u a t|)=|(∑ a, f u a t)-H t| :=
      MassNormalize.l1_error _ (fun a => hf u a t) _ (hH t)
    simp only [MixedNorm.sq,he,sq_abs] at hh
    exact hh
  have hvar : γ*W≤M^2-G.collision f := G.variance_bound γ hG f hf M hm
  let θ : ℝ := (1-s)/4
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hθ1 : θ ≤ 1/4 := by dsimp [θ]; linarith
  by_cases hw : W ≤ θ^2*M^2
  · have hnerr : G.collisionNorm (fun u a t => f u a t-g u a t)≤θ*M := by
      apply G.collisionNorm_le _ _ (mul_nonneg hθ hM)
      simpa only [mul_pow] using herr.trans hw
    have hng : G.collisionNorm g≤((1+s)/2)*M := by
      apply G.collisionNorm_le _ _ (mul_nonneg (by positivity) hM)
      apply hcg.trans
      have hp : s≤((1+s)/2)^2 := by nlinarith [sq_nonneg (1-s)]
      simpa only [mul_pow] using mul_le_mul_of_nonneg_right hp (sq_nonneg M)
    have hn : G.collisionNorm f≤(1-θ)*M := by
      have hh := G.collisionNorm_difference f g
      dsimp [θ] at *
      linarith
    have hq : G.collision f≤((1-θ)*M)^2 := by
      rw [← G.collisionNorm_sq]
      exact pow_le_pow_left₀ (G.collisionNorm_nonneg f) hn 2
    have hc : (1-θ)^2≤1-γ*θ^2 := by
      have hh : γ*θ^2≤θ^2 := mul_le_of_le_one_left (sq_nonneg θ) hγ1
      nlinarith [mul_nonneg hθ (show 0 ≤ 1-θ by linarith)]
    have hfinal : ((1-θ)*M)^2 ≤ (1-γ*θ^2)*M^2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hc (sq_nonneg M)
    exact hq.trans hfinal
  · have hh := mul_le_mul_of_nonneg_left (le_of_not_ge hw) hγ0
    dsimp [θ] at hh
    nlinarith only [hvar,hh]

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionContraction

end OAI
