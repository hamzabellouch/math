import OAI.Probability.ContinuumTransition.ScaledBounded

namespace OAI

universe u_1

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma scaled_localization {F : Parameter → ℝ} (hF : ConvexOn ℝ pressureDomain F)
    {x : Parameter} (hx : x ∈ pressureDomain) {r : ℝ} (hr : 0 < r)
    (hball : ball x r ⊆ pressureDomain)
    {κ : Type u_1} (K : κ → Set Parameter) (hc : ∀ i, Convex ℝ (K i))
    (hsep : ∀ i j, i ≠ j → Disjoint (Prod.snd '' K i) (Prod.snd '' K j))
    (hK : subgradients pressureDomain F x = convexHull ℝ (⋃ i, K i))
    {U : Set Parameter} (hU : IsOpen U) (hKU : (⋃ i, K i) ⊆ U) (S D : ℝ) :
    ∃ δ > 0, ∀ a : ℝ, 0 < a → a < δ → ∀ Q P : Parameter → ℝ,
      ConvexOn ℝ pressureDomain Q → IsMeanField Q a P →
      (∀ y ∈ ball x r, |Q y-F y| ≤ a^2) →
      ∀ Ξ : Parameter, ‖Ξ‖ ≤ S → x+a • Ξ ∈ pressureDomain →
      ∀ w ∈ activeLifts Q a P (x+a • Ξ), |w.2| ≤ D → w ∈ U := by
  by_contra hn
  push Not at hn
  have hex : ∀ n : ℕ, ∃ a : ℝ, 0 < a ∧ a < (1/2 : ℝ)^n ∧
      ∃ Q P : Parameter → ℝ, ConvexOn ℝ pressureDomain Q ∧ IsMeanField Q a P ∧
      (∀ y ∈ ball x r, |Q y-F y| ≤ a^2) ∧ ∃ Ξ : Parameter, ‖Ξ‖ ≤ S ∧
      x+a • Ξ ∈ pressureDomain ∧ ∃ w ∈ activeLifts Q a P (x+a • Ξ), |w.2| ≤ D ∧ w ∉ U :=
    fun n => hn _ (pow_pos (by norm_num) n)
  choose a ha ha' Q P hQ hP happ Ξ hΞ hXS W hW hD hbad using hex
  have ha0 : Tendsto a atTop (𝓝 0) :=
    squeeze_zero (fun n => (ha n).le) (fun n => (ha' n).le)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  obtain ⟨φ,_,ξ,v,_,hv,hs,hm⟩ := scaled_active_subseq hF ha ha0 hQ hP hx hr hball happ hΞ hXS hW hD
  have hvs : v ∈ convexHull ℝ (⋃ i, K i) := by rw [← hK]; exact hs
  have hu := hKU (quadratic_maximizer_mem_group K hc hsep hx hvs (fun u hu => hm u (by change u ∈ subgradients pressureDomain F x; rw [hK]; exact hu)))
  obtain ⟨n,hn⟩ := (hv.eventually (hU.mem_nhds hu)).exists
  exact hbad (φ n) hn

end ContinuumTemperature
end
end

end OAI
