import OAI.Geometry.NodalSets.Elliptic.CompactSourceRepresentatives
import OAI.Geometry.NodalSets.Waves.CompactSourceWaves
import OAI.Geometry.NodalSets.Waves.LocalSourceWaveTransfer
import OAI.Geometry.NodalSets.Waves.WaveSecondJet

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

structure LocalCompactWaveData
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w S : Coord → ℝ)
    (D : Set Coord) (m J K k0 : ℕ) where
  G : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ
  W : Coord → ℝ
  A : Coord → ℝ
  E : Set Coord
  smooth_G : ContDiff ℝ ∞ G
  smooth_W : ContDiff ℝ ∞ W
  smooth_A : ContDiff ℝ ∞ A
  symmetric_G : ∀ x u v, G x u v = G x v u
  positive_G : ∀ x v, v ≠ 0 → 0 < G x v v
  open_E : IsOpen E
  centers_E : D ⊆ E
  germ : ∀ x ∈ E, (G =ᶠ[𝓝 x] g) ∧ (W =ᶠ[𝓝 x] w) ∧ (A =ᶠ[𝓝 x] S)
  nonzero_gradient : ∀ x ∈ D, metricGradient G A x ≠ 0
  cover : SourceCompactFrameCover G A D
  beams : TripleSourceWaveData G W A (coverSourceCenter cover) cover.triple m J K k0
  estimates : ∀ᶠ n : ℕ in atTop, ∀ t : cover.Parameter × Fin 3,
    ContDiff ℝ ∞ (beams.wave (n:ℝ) t) ∧ HasCompactSupport (beams.wave (n:ℝ) t) ∧
    tsupport (beams.wave (n:ℝ) t) ⊆ E ∧
    tsupport (beams.wave (n:ℝ) t) ⊆
      {z | sourceEuclideanNorm (z-coverSourceCenter cover t.1) ≤ beams.R*(n:ℝ)^(-1/3:ℝ)} ∧
    ∀ z : Coord,
      (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val (beams.wave (n:ℝ) t) z‖ ≤
        beams.Cw*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S z-beams.c*(n:ℝ)*(sourceEuclideanNorm (z-coverSourceCenter cover t.1))^2)) ∧
      DerivativeBound k0 (fun z ↦ sourceWeightedOperator g w (beams.wave (n:ℝ) t) z +
        ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*beams.wave (n:ℝ) t z) z
          (beams.Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S z))

theorem construct_local_compact_waves {D U : Set Coord} (hD : IsCompact D)
    (hU : IsOpen U) (hDU : D ⊆ U) (hUn : U.Nonempty)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w S : Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hS : ContDiffOn ℝ ∞ S U)
    (hwp : ∀ x ∈ U, 0 < w x) (hp0 : ∀ x ∈ D, metricGradient g S x ≠ 0)
    (hdir : ∀ x ∈ D, ∃ v : Coord, g x (metricGradient g S x) v = 0 ∧ g x v v = 1 ∧
      0 < sourceHessian g S x (metricGradient g S x) (metricGradient g S x)+
        (g x (metricGradient g S x) (metricGradient g S x)+4)*sourceHessian g S x v v)
    (m J K k0 : ℕ) (hm : 3*K+4*k0+6 < m+1) (hJ : K+k0+1 ≤ J) :
    Nonempty (LocalCompactWaveData g w S D m J K k0) := by
  obtain ⟨G,W,A,E,hG,hW,hA,hGs,hGp,hE,hDE,hEU,hWp,he⟩ :=
    compact_source_representatives hD hU hDU hUn g hg hs hp w S hw hS hwp
  have hn (x : Coord) (hx : x ∈ D) : metricGradient G A x ≠ 0 := by
    rw [(he x (hDE hx)).2.2.2.1]
    exact hp0 x hx
  have hd (x : Coord) (hx : x ∈ D) : ∃ v : Coord,
      G x (metricGradient G A x) v = 0 ∧ G x v v = 1 ∧
      0 < sourceHessian G A x (metricGradient G A x) (metricGradient G A x)+
        (G x (metricGradient G A x) (metricGradient G A x)+4)*sourceHessian G A x v v := by
    obtain ⟨hge,_,_,hpEq,hHEq⟩ := he x (hDE hx)
    rw [hge.self_of_nhds,hpEq,hHEq]
    exact hdir x hx
  obtain ⟨d,⟨b⟩,_⟩ := construct_compact_source_waves G hG hGs hGp W hW A hA
    hD hE hDE hWp hn hd m J K k0 hm hJ
  have hest := local_source_wave_transfer g G w W S A
    (fun t : d.Parameter × Fin 3 ↦ coverSourceCenter d t.1)
    ((continuous_coverSourceCenter d).comp continuous_fst) hE
    (fun t ↦ hDE (d.center t.1).property)
    (fun x hx ↦ ⟨(he x hx).1,(he x hx).2.1,(he x hx).2.2.1.self_of_nhds⟩)
    (fun n t ↦ b.wave (n:ℝ) t) k0 K b.c b.Cw b.Cr b.R b.Cw_pos b.Cr_pos b.estimates
  exact ⟨⟨G,W,A,E,hG,hW,hA,hGs,hGp,hE,hDE,
    (fun x hx ↦ ⟨(he x hx).1,(he x hx).2.1,(he x hx).2.2.1⟩),hn,d,b,hest⟩⟩

end
end Yau.Geometry

end OAI
