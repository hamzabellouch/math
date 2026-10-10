import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularFiniteLimit

namespace OAI

/-! Propagate a remote uniform limit down to a fixed exterior endpoint. -/

open Set Filter Topology
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem circularSolutions_tail_uniform_limit
    (νp νm : ℕ → ℂ) (μp μm η : ℂ)
    (hp : Tendsto νp atTop (𝓝 μp)) (hn : Tendsto νm atTop (𝓝 μm))
    (m : ℕ → ℕ) (hm : ∀ᶠ n in atTop, 1 ≤ m n) (q : ℕ → ℝ → ℂ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (L T : ℝ) (Z : ℕ → ℝ → E₄) (Y : ℝ → E₄)
    (hd : ∀ᶠ n in atTop, ∀ t ∈ Ici L, HasDerivAt (Z n)
      (circularLeadingField t (Z n t)+circularBoundedField (νp n) (νm n) η (m n) (q n t) (Z n t)) t)
    (hdy : ∀ t ∈ Ici L, HasDerivAt Y
      (circularLeadingField t (Y t)+circularBoundedField μp μm η 1 0 (Y t)) t)
    (hq : ∀ᶠ n in atTop, ∀ t ∈ Ici L,
      ‖spectralDiagonalCoefficient (m n) (q n t)‖+‖spectralCrossCoefficient (m n) (q n t)‖ ≤ ε n)
    (htail : TendstoUniformlyOn Z Y atTop (Ici T)) :
    TendstoUniformlyOn Z Y atTop (Ici L) := by
  let R := max L T
  have hfinite : TendstoUniformlyOn Z Y atTop (Icc L R) := by
    apply circularSolutions_backward_uniform_limit νp νm μp μm η hp hn m hm q ε hε hεlim L R Z Y
    · exact hd.mono (fun n h => fun t ht => (h t ht.1).continuousAt.continuousWithinAt)
    · exact fun t ht => (hdy t ht.1).continuousAt.continuousWithinAt
    · exact hd.mono (fun n h => fun t ht => h t ht.1)
    · exact fun t ht => hdy t ht.1
    · exact hq.mono (fun n h => fun t ht => h t ht.1)
    · exact htail.tendsto_at (le_max_right L T)
  rw [Metric.tendstoUniformlyOn_iff] at hfinite htail ⊢
  intro δ hδ
  filter_upwards [hfinite δ hδ,htail δ hδ] with n hfn htn t ht
  by_cases hr : t ≤ R
  · exact hfn t ⟨ht,hr⟩
  · exact htn t ((le_max_right L T).trans (le_of_not_ge hr))

end DefocusingNLS

end OAI
