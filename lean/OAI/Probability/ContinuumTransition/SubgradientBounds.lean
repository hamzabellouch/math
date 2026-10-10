import OAI.Probability.ContinuumTransition.CompactSequences

namespace OAI

universe u_1

section
open scoped Topology NNReal
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma supportOn_norm_le {S : Set Parameter} {F : Parameter → ℝ} {x v : Parameter}
    {r : ℝ} (hr : 0 < r) (hball : ball x r ⊆ S) {C : ℝ≥0}
    (hL : LipschitzOnWith C F (ball x r)) (hv : SupportOn S F x v) : ‖v‖ ≤ C := by
  let δ := r/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : δ < r := by dsimp [δ]; linarith
  have htest : ∀ e : Parameter, ‖e‖ = 1 → pDot v e ≤ C := by
    intro e he
    have hz : x+δ • e ∈ ball x r := by
      rw [mem_ball,dist_eq_norm_sub,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hδ,he,mul_one]
      exact hδr
    have hs := hv _ (hball hz)
    have hl := hL.dist_le_mul _ hz _ (mem_ball_self hr)
    rw [Real.dist_eq] at hl
    have hle := (le_abs_self (F (x+δ • e)-F x)).trans hl
    have hdist : dist (x+δ • e) x = δ := by
      rw [dist_eq_norm_sub,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hδ,he,mul_one]
    rw [hdist] at hle
    have heq : pDot v (x+δ • e-x) = δ*pDot v e := by dsimp [pDot]; ring
    rw [heq] at hs
    nlinarith
  have h1 := htest (1,0) (by simp [Prod.norm_def])
  have h2 := htest (-1,0) (by simp [Prod.norm_def])
  have h3 := htest (0,1) (by simp [Prod.norm_def])
  have h4 := htest (0,-1) (by simp [Prod.norm_def])
  rw [Prod.norm_def,max_le_iff,Real.norm_eq_abs,Real.norm_eq_abs]
  simp only [pDot,mul_one,mul_zero,mul_neg_one,zero_add,add_zero] at h1 h2 h3 h4
  exact ⟨abs_le.mpr ⟨by linarith,h1⟩,abs_le.mpr ⟨by linarith,h3⟩⟩

lemma supports_near_norm_le {S : Set Parameter} {F : Parameter → ℝ} {x y v : Parameter}
    {r : ℝ} (hr : 0 < r) (hball : ball x r ⊆ S) {C : ℝ≥0}
    (hL : LipschitzOnWith C F (ball x r)) (hy : y ∈ ball x (r/2))
    (hv : SupportOn S F y v) : ‖v‖ ≤ C := by
  have hsub : ball y (r/2) ⊆ ball x r := by
    intro z hz
    exact lt_of_le_of_lt (dist_triangle z y x) (by change dist y x < r/2 at hy; change dist z y < r/2 at hz; linarith)
  exact supportOn_norm_le (by positivity : 0 < r/2) (hsub.trans hball) (hL.mono hsub) hv

lemma eventually_subgradients_bounded {ι : Type u_1} {l : Filter ι}
    {S : Set Parameter} (hS : IsOpen S) {F : ι → Parameter → ℝ} {f : Parameter → ℝ}
    (hconv : ∀ᶠ i in l, ConvexOn ℝ S (F i))
    (hlim : ∀ x ∈ S, Tendsto (fun i => F i x) l (𝓝 (f x)))
    {X : ι → Parameter} {x : Parameter} (hx : x ∈ S) (hX : Tendsto X l (𝓝 x)) :
    ∃ C : ℝ≥0, ∀ᶠ i in l, ∀ v, SupportOn S (F i) (X i) v → ‖v‖ ≤ C := by
  obtain ⟨r,hr,hb,C,hC⟩ := eventually_convex_lipschitz hS hconv hlim hx
  refine ⟨C,?_⟩
  filter_upwards [hC,hX.eventually (ball_mem_nhds x (show 0 < r/2 by positivity))] with i hi hXi
  intro v hv
  exact supports_near_norm_le hr hb hi hXi hv

lemma supportOn_varying_limit {ι : Type u_1} {l : Filter ι} [l.NeBot]
    {S : Set Parameter} (hS : IsOpen S) {F : ι → Parameter → ℝ} {f : Parameter → ℝ}
    (hlim : TendstoLocallyUniformlyOn F f l S) (hf : ContinuousOn f S)
    {X V : ι → Parameter} {x v : Parameter} (hx : x ∈ S)
    (hX : Tendsto X l (𝓝 x)) (hV : Tendsto V l (𝓝 v))
    (h : ∀ᶠ i in l, SupportOn S (F i) (X i) (V i)) : SupportOn S f x v := by
  intro y hy
  have hfx := hlim.tendsto_comp (hf x hx) hx
    (tendsto_nhdsWithin_iff.2 ⟨hX,hX.eventually (hS.mem_nhds hx)⟩)
  have hd : Tendsto (fun i => pDot (V i) (y-X i)) l (𝓝 (pDot v (y-x))) := by
    exact (show Continuous (fun p : Parameter × Parameter => pDot p.1 (y-p.2)) by unfold pDot; fun_prop).tendsto
      (v,x) |>.comp (hV.prodMk_nhds hX)
  exact le_of_tendsto_of_tendsto (hfx.add hd) (hlim.tendsto_at hy)
    (h.mono fun i hi => hi y hy)

end ContinuumTemperature
end
end

end OAI
