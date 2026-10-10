import OAI.Geometry.EinsteinFour.GeodesicGeometry13
import Mathlib.Topology.Sequences

namespace OAI


section

/-! A local length bound extends across a finite union of complex-parametrized thin sets. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped _root_.Topology NNReal
noncomputable section

theorem dist_le_of_complexThinSet {Y : Type*} [PseudoMetricSpace Y]
    (f : FourSpace → Y) (p : Fin 2 → ℂ → FourSpace) (U : Fin 2 → Set ℂ)
    (hp : ∀ i z, z ∈ U i → ∃ K : ℝ≥0, ∃ V ∈ 𝓝 z, LipschitzOnWith K (p i) V)
    (V : Set FourSpace) (hV : IsOpen V) (hconv : Convex ℝ V) (K : ℝ) (hK : 0 ≤ K)
    (hf : ContinuousOn f (V \ ⋃ i, p i '' U i))
    (hlocal : ∀ x ∈ V \ ⋃ i, p i '' U i,
      ∀ᶠ y in 𝓝[V \ ⋃ i, p i '' U i] x, dist (f x) (f y) ≤ K * dist x y)
    (a b : FourSpace) (ha : a ∈ V \ ⋃ i, p i '' U i) (hb : b ∈ V \ ⋃ i, p i '' U i) :
    dist (f a) (f b) ≤ K * dist a b := by
  have hseg (x y : FourSpace) (hxy : segment ℝ x y ⊆ V \ ⋃ i, p i '' U i) :
      dist (f x) (f y) ≤ K * dist x y := by
    apply dist_le_of_segment_local_bound f x y K (hf.mono hxy)
    intro z hz
    exact nhdsWithin_mono z hxy (hlocal z (hxy hz))
  have hε (ε : ℝ) (hε : 0 < ε) : dist (f a) (f b) ≤ K*(dist a b+2*ε) := by
    obtain ⟨z,hz,havoid⟩ := exists_complexParametrized_detour p U hp a b
      (fun i hi => ha.2 (mem_iUnion.mpr ⟨i,hi⟩))
      (fun i hi => hb.2 (mem_iUnion.mpr ⟨i,hi⟩))
      (V ∩ Metric.ball b ε) (inter_mem (hV.mem_nhds hb.1) (Metric.ball_mem_nhds b hε))
    have hleft : segment ℝ a z ⊆ V \ ⋃ i, p i '' U i := by
      intro w hw
      refine ⟨hconv.segment_subset ha.1 hz.1 hw,?_⟩
      intro hwB
      obtain ⟨i,hi⟩ := mem_iUnion.mp hwB
      exact Set.disjoint_left.mp (havoid i).1 hw hi
    have hright : segment ℝ z b ⊆ V \ ⋃ i, p i '' U i := by
      intro w hw
      refine ⟨hconv.segment_subset hz.1 hb.1 hw,?_⟩
      intro hwB
      obtain ⟨i,hi⟩ := mem_iUnion.mp hwB
      exact Set.disjoint_left.mp (havoid i).2 hw hi
    calc
      _ ≤ dist (f a) (f z)+dist (f z) (f b) := dist_triangle _ _ _
      _ ≤ K*dist a z+K*dist z b := add_le_add (hseg a z hleft) (hseg z b hright)
      _ = K*(dist a z+dist z b) := by ring
      _ ≤ K*(dist a b+2*ε) := by
        apply mul_le_mul_of_nonneg_left _ hK
        have hzb : dist z b < ε := hz.2
        linarith [dist_triangle a b z,dist_comm b z]
  have ht : Tendsto (fun ε : ℝ => K*(dist a b+2*ε)) (𝓝[>] 0) (𝓝 (K*dist a b)) := by
    have h : Continuous (fun ε : ℝ => K*(dist a b+2*ε)) := by fun_prop
    simpa only [mul_zero,add_zero] using h.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  exact ge_of_tendsto ht (Filter.Eventually.mono self_mem_nhdsWithin (fun ε hpos => hε ε hpos))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Density and continuous extension of the distance bound across the thin chart sets. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped _root_.Topology NNReal ENNReal
noncomputable section

theorem complexParametrizedImage_compl_dense (p : Fin 2 → ℂ → FourSpace) (U : Fin 2 → Set ℂ)
    (hp : ∀ i z, z ∈ U i → ∃ K : ℝ≥0, ∃ V ∈ 𝓝 z, LipschitzOnWith K (p i) V) :
    Dense (⋃ i, p i '' U i)ᶜ := by
  have hdim : dimH (⋃ i, p i '' U i) ≤ 3 := by
    rw [dimH_iUnion]
    apply iSup_le
    intro i
    apply le_trans (dimH_mono ?_) (complexParametrizedCone_dimH_le 0 (p i) (U i) (hp i))
    rintro x ⟨z,hz,rfl⟩
    refine ⟨(z,1),⟨hz,mem_univ _⟩,?_⟩
    simp
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨y,hy,hnot⟩ := exists_not_mem_of_dimH_le_three _ hdim x (Metric.ball x ε)
    (Metric.ball_mem_nhds x hε)
  exact ⟨y,hnot,by simpa only [Metric.mem_ball,dist_comm] using hy⟩

theorem dist_le_on_open_of_dense {Y : Type*} [PseudoMetricSpace Y]
    (D : Set FourSpace) (hD : Dense D) (V : Set FourSpace) (hV : IsOpen V)
    (f : FourSpace → Y) (hf : ContinuousOn f V) (K : ℝ)
    (hbound : ∀ x ∈ V, x ∈ D → ∀ y ∈ V, y ∈ D → dist (f x) (f y) ≤ K*dist x y)
    (x y : FourSpace) (hx : x ∈ V) (hy : y ∈ V) :
    dist (f x) (f y) ≤ K * dist x y := by
  obtain ⟨u,hu,hux⟩ := mem_closure_iff_seq_limit.mp (hD x)
  obtain ⟨v,hv,hvy⟩ := mem_closure_iff_seq_limit.mp (hD y)
  have huV : ∀ᶠ n in atTop, u n ∈ V := hux (hV.mem_nhds hx)
  have hvV : ∀ᶠ n in atTop, v n ∈ V := hvy (hV.mem_nhds hy)
  have huf : Tendsto (fun n => f (u n)) atTop (𝓝 (f x)) :=
    (show Tendsto f (𝓝[V] x) (𝓝 (f x)) from hf x hx).comp
      (tendsto_nhdsWithin_iff.mpr ⟨hux,huV⟩)
  have hvf : Tendsto (fun n => f (v n)) atTop (𝓝 (f y)) :=
    (show Tendsto f (𝓝[V] y) (𝓝 (f y)) from hf y hy).comp
      (tendsto_nhdsWithin_iff.mpr ⟨hvy,hvV⟩)
  apply le_of_tendsto_of_tendsto
    (continuous_dist.continuousAt.tendsto.comp (huf.prodMk_nhds hvf))
    (tendsto_const_nhds.mul (continuous_dist.continuousAt.tendsto.comp (hux.prodMk_nhds hvy)))
  filter_upwards [huV,hvV] with n hun hvn
  exact hbound (u n) hun (hu n) (v n) hvn (hv n)

end
end PositiveEinsteinFour.Geometry
end

end OAI
