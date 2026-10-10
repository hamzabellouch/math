import OAI.Probability.InvariantIsing.Magnetic.MagneticGridProjection

namespace OAI

/-! Fixed interior targets round to converging attainable group profiles. -/
noncomputable section
open Filter
open scoped Topology
namespace InvariantIsing

lemma group_size_tendsto_atTop (N G : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    {γ : ℝ} (hγ : 0<γ)
    (hG : Tendsto (fun k => (G k:ℝ)/(N k:ℝ)) atTop (𝓝 γ)) :
    Tendsto G atTop atTop := by
  have hpos : ∀ᶠ k in atTop, 0<N k := hN.eventually (eventually_gt_atTop 0)
  have hg : ∀ᶠ k in atTop, γ/2<(G k:ℝ)/(N k:ℝ) :=
    hG.eventually (Ioi_mem_nhds (by linarith : γ/2<γ))
  apply tendsto_atTop.2
  intro B
  have hn : ∀ᶠ k in atTop, (B:ℝ)*2/γ < (N k:ℝ) :=
    (tendsto_natCast_atTop_atTop.comp hN).eventually (eventually_gt_atTop _)
  filter_upwards [hpos,hg,hn] with k hk hg hn
  have hkn : (0:ℝ)<N k := Nat.cast_pos.mpr hk
  have hg' := (lt_div_iff₀ hkn).mp hg
  have hn' := (div_lt_iff₀ hγ).mp hn
  have hB : (B:ℝ)<G k := by nlinarith
  exact Nat.le_of_lt (Nat.cast_lt.mp hB)

lemma rounded_group_magnetizations_tendsto {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (group : ∀ k, Fin (N k) → A)
    (γ mag : A → ℝ) (hγ : ∀ a, 0<γ a) (hmag : ∀ a, |mag a|≤1)
    (hgroup : Tendsto (fun k a => (spinGroupSize (group k) a:ℝ)/(N k:ℝ)) atTop (𝓝 γ)) :
    Tendsto (fun k a => magneticRoundedValue (spinGroupSize (group k) a) (mag a)) atTop (𝓝 mag) := by
  apply tendsto_pi_nhds.mpr
  intro a
  exact magneticRoundedValue_tendsto (fun k => spinGroupSize (group k) a)
    (group_size_tendsto_atTop N _ hN (hγ a) ((tendsto_pi_nhds.mp hgroup) a)) (hmag a)

end InvariantIsing

end

end OAI
