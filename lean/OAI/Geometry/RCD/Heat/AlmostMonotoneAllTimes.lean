import OAI.Geometry.RCD.Sobolev.RemoveExceptionalTimes

namespace OAI

/-! # Uniform convergence at every time from a vanishing one-sided error

Good times bracket any prescribed interior time. The common Lipschitz
bound of the limit and the vanishing monotonicity error squeeze every
spatial value with the same error.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem almost_monotone_uniform_all_times {Y : Type*}
    {a b : ℝ} (N : Set ℝ) (hN : N.Countable)
    (f : ℕ → ℝ → Y → ℝ) (H : ℝ → Y → ℝ) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) (L : ℝ) (hL : 0 ≤ L)
    (hH : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, ∀ x,
      |H s x-H t x| ≤ L*|s-t|)
    (ho : ∀ k s t, a ≤ s → s ≤ t → t ≤ b → ∀ x,
      f k s x-f k t x ≤ e k*(t-s))
    (hlim : ∀ s ∈ Ioo a b, s ∉ N → TendstoUniformly (fun k => f k s) (H s) atTop)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    TendstoUniformly (fun k => f k t) (H t) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  let d := ε/(4*(L+1))
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdε : (L+1)*d = ε/4 := by dsimp only [d]; field_simp
  have hden : Dense Nᶜ := volume.dense_of_ae (hN.ae_notMem volume)
  obtain ⟨s,hs,hsN⟩ := hden.inter_open_nonempty (Ioo (max a (t-d)) t)
    isOpen_Ioo (nonempty_Ioo.mpr (max_lt ht.1 (by linarith)))
  obtain ⟨u,hu,huN⟩ := hden.inter_open_nonempty (Ioo t (min b (t+d)))
    isOpen_Ioo (nonempty_Ioo.mpr (lt_min ht.2 (by linarith)))
  have hsab : s ∈ Ioo a b := ⟨(le_max_left _ _).trans_lt hs.1,hs.2.trans ht.2⟩
  have huab : u ∈ Ioo a b := ⟨ht.1.trans hu.1,hu.2.trans_le (min_le_left _ _)⟩
  have hsd : t-s < d := by have := (le_max_right a (t-d)).trans_lt hs.1; linarith
  have hud : u-t < d := by have := hu.2.trans_le (min_le_right b (t+d)); linarith
  have hsmall : ∀ᶠ k in atTop, e k < 1 := he.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hsmall,
    (Metric.tendstoUniformly_iff.mp (hlim s hsab hsN)) (ε/2) (by positivity),
    (Metric.tendstoUniformly_iff.mp (hlim u huab huN)) (ε/2) (by positivity)] with k hk hks hku
  intro x
  have hlow := ho k s t hsab.1.le hs.2.le ht.2.le x
  have hupp := ho k t u ht.1.le hu.1.le huab.2.le x
  have hHs := hH s hsab t ht x
  have hHu := hH u huab t ht x
  rw [abs_of_neg (sub_neg.mpr hs.2)] at hHs
  rw [abs_of_pos (sub_pos.mpr hu.1)] at hHu
  have hes : e k*(t-s) ≤ t-s := by
    simpa using mul_le_mul_of_nonneg_right hk.le (sub_nonneg.mpr hs.2.le)
  have heu : e k*(u-t) ≤ u-t := by
    simpa using mul_le_mul_of_nonneg_right hk.le (sub_nonneg.mpr hu.1.le)
  have hls : L*(t-s)+(t-s) < ε/4 := by nlinarith
  have hlu : L*(u-t)+(u-t) < ε/4 := by nlinarith
  have hfs := hks x
  have hfu := hku x
  rw [Real.dist_eq] at hfs hfu ⊢
  rcases abs_lt.mp hfs with ⟨hfs₁,hfs₂⟩
  rcases abs_lt.mp hfu with ⟨hfu₁,hfu₂⟩
  rcases abs_le.mp hHs with ⟨hHs₁,hHs₂⟩
  rcases abs_le.mp hHu with ⟨hHu₁,hHu₂⟩
  apply abs_lt.mpr
  constructor <;> linarith

end RegularPointCoordinates

end

end OAI
