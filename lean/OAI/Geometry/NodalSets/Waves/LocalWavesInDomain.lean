import OAI.Geometry.NodalSets.Waves.LocalCompactWaves

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

theorem construct_local_compact_waves_in_domain {D U : Set Coord} (hD : IsCompact D)
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
    ∃ a : LocalCompactWaveData g w S D m J K k0, a.E ⊆ U := by
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
  refine ⟨⟨G,W,A,E,hG,hW,hA,hGs,hGp,hE,hDE,
    (fun x hx ↦ ⟨(he x hx).1,(he x hx).2.1,(he x hx).2.2.1⟩),hn,d,b,hest⟩,hEU⟩

end
end Yau.Geometry

end OAI
