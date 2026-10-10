import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.GraphOpen

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

section
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

def subgradientGraph (u : M → ℝ) : Set (TangentBundle 𝓘(ℝ,Model n) M) :=
  {z | z.2∈normalSubdifferential (n := n) u z.1}

def graphProjection (u : M → ℝ) (t : ℝ) (z : subgradientGraph (n := n) u) : M :=
  riemannianExp z.1.1 (t • z.1.2)

variable [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma continuous_graphProjection (u : M → ℝ) (t : ℝ) :
    Continuous (graphProjection (n := n) u t) :=
  (contMDiff_riemannianExp (n := n) (M := M)).continuous.comp
    ((contMDiff_tangentScale (E := Model n) (M := M)).continuous.comp
      (continuous_const.prodMk continuous_subtype_val))

lemma WeakMTW.isOpenMap_graphProjection (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (hID : ∀ x : M, ∀ q∈normalSubdifferential (n := n) (cTransform v) x,
      t • q∈injectivityDomain x) :
    IsOpenMap (graphProjection (n := n) (cTransform v) t) := by
  intro O hO
  obtain ⟨U,hU,hUO⟩ := isOpen_induced_iff.mp hO
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨z,hz,rfl⟩
  have hzU : z.1∈U := by
    have : z∈Subtype.val ⁻¹' U := by rw [hUO]; exact hz
    exact this
  have H := hmtw.local_projection_surjective hv z.2 ht ht1 (hID z.1.1) U (hU.mem_nhds hzU)
  filter_upwards [H] with y hy
  obtain ⟨p,hp,hpG,hpy⟩ := hy
  refine ⟨⟨p,hpG⟩,?_,hpy⟩
  rw [←hUO]
  exact hp
end

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma global_min_divided_cost_subgradient {u : M → ℝ} {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈minimizingVectors x)
    {t : ℝ} (ht : 0<t)
    (hmin : ∀ z : M, u x+cost x (riemannianExp x p)/t≤
      u z+cost z (riemannianExp x p)/t) :
    t⁻¹ • p∈normalSubdifferential (n := n) u x := by
  have hs : (0:ℝ)<1/2 := by norm_num
  have hs1 : (1/2:ℝ)<1 := by norm_num
  have htne : t≠0 := ht.ne'
  have hscale : (t/2) • (t⁻¹ • p)=(1/2:ℝ) • p := by
    rw [smul_smul]
    congr 1
    field_simp
  apply local_min_divided_cost_subgradient (t := t/2) (by positivity)
  · rw [hscale]
    exact contracted_minimizer_mem_injectivityDomain hp hs hs1
  · rw [hscale]
    apply Filter.Eventually.of_forall
    intro z
    have hh := hmin z
    have hu := (div_le_div_iff_of_pos_right ht).mpr
      (minimizing_split_upper_support hp hs hs1 z)
    have hc := minimizing_split_contact hp hs hs1
    have hx : cost x (riemannianExp x p)/t =
        cost x (riemannianExp x ((1/2:ℝ) • p))/(t/2)+(1-1/2)*‖p‖^2/2/t := by
      rw [←hc]
      field_simp
    have hz : (cost z (riemannianExp x ((1/2:ℝ) • p))/(1/2)+(1-1/2)*‖p‖^2/2)/t =
        cost z (riemannianExp x ((1/2:ℝ) • p))/(t/2)+(1-1/2)*‖p‖^2/2/t := by
      field_simp
    rw [hx] at hh
    rw [hz] at hu
    linarith

lemma surjective_graphProjection {u : M → ℝ} (hu : Continuous u) {t : ℝ} (ht : 0<t) :
    Function.Surjective (graphProjection (n := n) u t) := by
  intro y
  let : Nonempty M := ⟨y⟩
  obtain ⟨x,_,hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty
    (hu.add ((continuous_cost_left y).div_const t)).continuousOn
  obtain ⟨p,hp,hpy⟩ := exists_minimizing_vector (n := n) x y
  have hsub := global_min_divided_cost_subgradient hp ht
    (show ∀ z : M, u x+cost x (riemannianExp x p)/t≤
      u z+cost z (riemannianExp x p)/t by
      intro z
      rw [hpy]
      exact hmin (mem_univ z))
  refine ⟨⟨⟨x,t⁻¹ • p⟩,hsub⟩,?_⟩
  dsimp only [graphProjection]
  rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul,hpy]

end WeakMTWTransport

end

end OAI
