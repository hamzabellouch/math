import OAI.Probability.ContinuumTransition.ActiveLimits

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma active_uniform_near {Q : ℕ → Parameter → ℝ} {q : Parameter → ℝ}
    {P : ℕ → Parameter → ℝ} {p : Parameter → ℝ} {a : ℝ}
    (hQ : TendstoLocallyUniformlyOn Q q atTop pressureDomain)
    (hconv : ∀ n, ConvexOn ℝ pressureDomain (Q n)) (hq : ContinuousOn q pressureDomain)
    (hP : ∀ n, IsMeanField (Q n) a (P n)) (hp : IsMeanField q a p)
    {x : Parameter} (hx : x ∈ pressureDomain) {r : ℝ} (hr : 0 < r)
    (hball : ball x r ⊆ pressureDomain) {D : ℝ}
    (hD : ∀ n, ∀ y ∈ ball x r, ∀ w ∈ activeLifts (Q n) a (P n) y, w.2 ∈ Icc 0 D)
    {U : Set Parameter} (hU : IsOpen U) (hAU : activeLifts q a p x ⊆ U) :
    ∃ δ > 0, δ < r ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ y ∈ ball x δ, activeLifts (Q n) a (P n) y ⊆ U := by
  by_contra hn
  push Not at hn
  have hex : ∀ m : ℕ, ∃ n ≥ m, ∃ y ∈ ball x (min (r/2) ((1/2 : ℝ)^m)),
      ∃ w ∈ activeLifts (Q n) a (P n) y, w ∉ U := by
    intro m
    have hd : 0 < min (r/2) ((1/2 : ℝ)^m) := lt_min (by positivity) (pow_pos (by norm_num) _)
    have hdr : min (r/2) ((1/2 : ℝ)^m) < r := (min_le_left _ _).trans_lt (by linarith)
    obtain ⟨n,hn,y,hy,hbad⟩ := hn _ hd hdr m
    obtain ⟨w,hw,hwu⟩ := Set.not_subset.mp hbad
    exact ⟨n,hn,y,hy,w,hw,hwu⟩
  choose k hk X hX W hW hbad using hex
  have hk' : Tendsto k atTop atTop := tendsto_atTop_mono hk tendsto_id
  have hXr : ∀ n, X n ∈ ball x r := fun n => (hX n).trans_le ((min_le_left _ _).trans (show r/2 ≤ r by linarith))
  have hXt : Tendsto X atTop (𝓝 x) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hX n).le.trans (min_le_right _ _))
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  obtain ⟨φ,_,w,hw,hwt⟩ := active_subseq_of_density_bound (locallyUniform_reindex hQ hk')
    (fun n => hconv (k n)) hq tendsto_const_nhds (fun n => hP (k n)) hp hx hXt
    (fun n => hball (hXr n)) hW (fun n => hD (k n) _ (hXr n) _ (hW n))
  obtain ⟨n,hn⟩ := (hwt.eventually (hU.mem_nhds (hAU hw))).exists
  exact hbad (φ n) hn

end ContinuumTemperature
end
end

end OAI
