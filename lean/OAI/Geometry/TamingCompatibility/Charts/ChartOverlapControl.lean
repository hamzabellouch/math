import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.Dpos2

namespace OAI

section

noncomputable section
namespace TamingCompatibility
open Set Filter GeometricHilbert
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma compact_chart_overlap_control (p q : X) {K : Set X} (hK : IsCompact K)
    (hp : K ⊆ (extChartAt Model p).source) (hq : K ⊆ (extChartAt Model q).source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ∀ y : X,
      y ∈ (extChartAt Model p).source →
      ‖extChartAt Model p y-extChartAt Model p x‖ ≤ ε →
      y ∈ (extChartAt Model q).source ∧
      ‖extChartAt Model q y-extChartAt Model q x‖ ≤ C*‖extChartAt Model p y-extChartAt Model p x‖ := by
  let U : Set Space := (extChartAt Model p).target ∩
    (extChartAt Model p).symm ⁻¹' (extChartAt Model q).source
  have hU : IsOpen U := (continuousOn_extChartAt_symm p).isOpen_inter_preimage
    (isOpen_extChartAt_target p) (isOpen_extChartAt_source q)
  let f : Space → Space := extChartAt Model q ∘ (extChartAt Model p).symm
  have hf : ∀ z ∈ U, ContDiffAt ℝ ∞ f z := by
    intro z hz
    exact ((contDiffOn_ext_coord_change (I := Model) (n := ∞) q p) z hz).contDiffAt (hU.mem_nhds hz)
  let L : Set Space := extChartAt Model p '' K
  have hL : IsCompact L := hK.image_of_continuousOn ((continuousOn_extChartAt p).mono hp)
  have hLU : L ⊆ U := by
    rintro z ⟨x,hx,rfl⟩
    exact ⟨(extChartAt Model p).map_source (hp hx),by simpa only [mem_preimage,(extChartAt Model p).left_inv (hp hx)] using hq hx⟩
  let O : Set (Space × Space) := (fun z => z.1+z.2) ⁻¹' U
  have hO : IsOpen O := hU.preimage (continuous_fst.add continuous_snd)
  have hLO : L ×ˢ {(0 : Space)} ⊆ O := by
    rintro ⟨z,w⟩ ⟨hz,rfl⟩
    simpa only [O,mem_preimage,add_zero] using hLU hz
  obtain ⟨C,hC,ε,hε,hsub,hbound⟩ := UniformJets.local_linear_bound
    (fun z : Space × Space => f (z.1+z.2)) L hL O hO hLO
    (fun z hz => ContDiffAt.comp (g := f) (f := fun a : Space × Space => a.1+a.2) z
      (hf _ hz) (contDiffAt_fst.add contDiffAt_snd))
  refine ⟨C,hC,ε,hε,fun x hx y hy hxy => ?_⟩
  have hxL : extChartAt Model p x ∈ L := ⟨x,hx,rfl⟩
  have hz : extChartAt Model p x + (extChartAt Model p y-extChartAt Model p x) = extChartAt Model p y := by abel
  have hyU : extChartAt Model p y ∈ U := by
    simpa only [O,mem_preimage,hz] using hsub
      (show (extChartAt Model p x,extChartAt Model p y-extChartAt Model p x) ∈ L ×ˢ Metric.closedBall 0 ε from
        ⟨hxL,by simpa only [Metric.mem_closedBall,dist_zero_right] using hxy⟩)
  refine ⟨by simpa only [U,mem_inter_iff,mem_preimage,(extChartAt Model p).left_inv hy] using hyU.2,?_⟩
  have hb := hbound _ hxL (extChartAt Model p y-extChartAt Model p x) hxy
  simpa only [hz,add_zero,f,Function.comp_apply,(extChartAt Model p).left_inv hy,
    (extChartAt Model p).left_inv (hp hx)] using hb
end TamingCompatibility

end
end

end OAI
