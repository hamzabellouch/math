import OAI.Geometry.NodalSets.Spectral.MetricProjectionBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

theorem metric_projection_uniform_stability {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧
      ∀ (g h : Coord →L[ℝ] Coord →L[ℝ] ℝ) (e e₀ t : Coord) (ε : ℝ),
      ‖g‖ ≤ M → ‖e‖ ≤ K → ‖e₀‖ ≤ K → ‖t‖ ≤ K →
      g e e = 1 → h t t = 1 → h e₀ t = 0 →
      ‖e-e₀‖ ≤ ε → ‖g-h‖ ≤ ε → ε ≤ ε₀ →
      let q := metricPerpProjection g e t
      q ≠ 0 ∧ g (metricNormalize g q) (metricNormalize g q) = 1 ∧
        g e (metricNormalize g q) = 0 ∧ ‖metricNormalize g q-t‖ ≤ C*ε := by
  let P : ℝ := (M*K+K^2)*K
  let H : ℝ := 2*M*(K+1)*P+(K+1)^2
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  let ε₀ : ℝ := min (1/(P+1)) (1/(2*(H+1)))
  let C : ℝ := 2*P+8*(K+1)*H+1
  have hε₀ : 0 < ε₀ := lt_min (by positivity) (by positivity)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨ε₀,C,hε₀,hC,?_⟩
  intro g h e e₀ t ε hg he he₀ ht heunit htunit horth hd hm hε
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hd
  have hε1 := hε.trans (min_le_left _ _)
  have hε2 := hε.trans (min_le_right _ _)
  have hsmall1 : P*ε ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < P+1)).mp hε1
    nlinarith
  have hsmall2 : H*ε ≤ 1/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(H+1))).mp hε2
    nlinarith
  have h1 : (M*ε*K+ε*K^2)*K ≤ 1 := by convert hsmall1 using 1; dsimp [P]; ring
  have h2 : 2*M*(K+1)*((M*ε*K+ε*K^2)*K)+ε*(K+1)^2 ≤ 1/2 := by
    convert hsmall2 using 1
    dsimp [H,P]
    ring
  obtain ⟨hn,hu,ho,hb⟩ := normalized_projection_stability g h e e₀ t hM hK hg he he₀ ht
    heunit htunit horth hd hm h1 h2
  refine ⟨hn,hu,ho,hb.trans ?_⟩
  dsimp [C,H,P]
  nlinarith only [hε0]

end
end Yau.Geometry

end OAI
