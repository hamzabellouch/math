import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.ContinuationCollisionRemainderTendsto

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma pmfMean_affine_sq_bound {α : Type*} [Fintype α] (P : PMF α)
    (f : α → ℝ) (a b : ℝ) :
    pmfMean P (fun x => (a*f x+b)^2) ≤ 2*a^2*pmfMean P (fun x => (f x)^2)+2*b^2 := by
  calc
    _ ≤ pmfMean P (fun x => (2*a^2)*(f x)^2+2*b^2) := by
      apply pmfMean_mono
      intro x _
      nlinarith [sq_nonneg (a*f x-b)]
    _ = _ := by rw [pmfMean_add,pmfMean_const_mul,pmfMean_const]

theorem goodPrefix_normalized_l2 (c C : ℝ) (hc : 0 < c) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      ∀ (G : Graph n), GoodPrefixGraph n c C G →
        pmfMean (finish G) (fun H => (normalizedLeave n H-sharpConstant)^2) < δ := by
  intro δ hδ
  let s : ℕ → ℝ := fun n => prefixM n*cavityReference (prefixD n) 1/normalization n
  have hs : Tendsto s atTop (𝓝 sharpConstant) := prefix_terminal_scale_tendsto
  have hs2 : ∀ᶠ n : ℕ in atTop, s n ^ 2 ≤ 1 := by
    have hh := hs.pow 2
    rw [sharpConstant_sq] at hh
    exact (hh.eventually (gt_mem_nhds (by norm_num : (1/8 : ℝ) < 1))).mono (fun _ h => h.le)
  have hbias : Tendsto (fun n => 2*(s n-sharpConstant)^2) atTop (𝓝 (0 : ℝ)) := by
    simpa using ((hs.sub_const sharpConstant).pow 2).const_mul (2 : ℝ)
  filter_upwards [goodPrefix_relative_l2 c C hc (δ/4) (by positivity),hs2,
    hbias.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < δ/2)),
    prefix_scales_eventually_pos,eventually_ge_atTop (1 : ℕ)] with n hr hsqr hb hp hn
  intro G hG
  have hn0 : 0 < n := by omega
  have hnorm : 0 < normalization n := normalization_pos hn0
  have hm0 : 0 < (G.card : ℝ) := by rw [hG.2.1]; unfold prefixM; have := hp.1; positivity
  have hq : 0 < cavityReference (prefixD n) 1 :=
    cavityReference_pos (by linarith [hp.2]) (by norm_num)
  let f : Graph n → ℝ := fun H => (H.card : ℝ)/((G.card : ℝ)*cavityReference (prefixD n) 1)-1
  have heq : (fun H => (normalizedLeave n H-sharpConstant)^2) =
      (fun H => (s n*f H+(s n-sharpConstant))^2) := by
    funext H
    congr 1
    dsimp only [s,f,normalizedLeave]
    rw [← hG.2.1]
    field_simp [ne_of_gt hm0, ne_of_gt hq, ne_of_gt hnorm]
    ring
  have hnon : 0 ≤ pmfMean (finish G) (fun H => f H^2) := pmfMean_nonneg _ (fun _ _ => sq_nonneg _)
  rw [heq]
  calc
    _ ≤ 2*(s n)^2*pmfMean (finish G) (fun H => f H^2)+2*(s n-sharpConstant)^2 :=
      pmfMean_affine_sq_bound _ f _ _
    _ ≤ 2*pmfMean (finish G) (fun H => f H^2)+2*(s n-sharpConstant)^2 := by
      have hh := mul_le_mul_of_nonneg_right hsqr hnon
      nlinarith
    _ < δ := by have hh := hr G hG; change pmfMean (finish G) (fun H => f H^2) < δ/4 at hh; linarith

end SharpTerminalLeave

end

end OAI
