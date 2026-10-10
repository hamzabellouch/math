import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.UniformConvergence

namespace OAI

/-!
# Compact observables under small group translations

A compactly supported continuous observable changes uniformly little
under a group element tending to the identity. This remains true along
arbitrary moving base points, including points leaving compact sets.
It supplies the topological contraction step in the Hopf argument on a
noncompact homogeneous space.
-/

open Filter Set
open scoped Topology

namespace DukePrimeDegree

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [TopologicalSpace X] [MulAction G X]
  [ContinuousSMul G X]

/-- Small translations act uniformly continuously on a compactly
supported continuous real observable. -/
theorem compact_observable_smul_tendstoUniformly
    (f : X → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    TendstoUniformly (fun a : G => fun x : X => f (a • x)) f (𝓝 1) := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds (1 : G)
  let C : Set X := tsupport f ∪
    (fun z : G × X => z.1⁻¹ • z.2) '' (V ×ˢ tsupport f)
  have hCc : IsCompact C := hc.union
    ((hVc.prod hc).image (continuous_fst.inv.smul continuous_snd))
  have hcont : Continuous (fun z : G × X => f (z.1 • z.2)) := by
    fun_prop
  obtain ⟨W, hW, hsmallW⟩ := hCc.mem_uniformity_of_prod
    (f := fun a : G => fun x : X => f (a • x))
    (s := Set.univ) hcont.continuousOn (show (1 : G) ∈ Set.univ from Set.mem_univ _)
    (Metric.dist_mem_uniformity hε)
  have hsmall : ∀ᶠ a : G in 𝓝 1,
      ∀ x : C, dist (f (a • (x : X))) (f x) < ε := by
    have hW' : W ∈ 𝓝 (1 : G) := by simpa only [nhdsWithin_univ] using hW
    filter_upwards [hW'] with a ha x
    simpa only [one_smul, Set.mem_ofPred_eq] using hsmallW a ha x x.property
  filter_upwards [hV, hsmall] with a ha hs x
  by_cases hx : x ∈ C
  · simpa only [dist_comm] using hs ⟨x, hx⟩
  · have hx0 : f x = 0 := by
      by_contra hne
      exact hx (Or.inl (subset_tsupport f hne))
    have hax0 : f (a • x) = 0 := by
      by_contra hne
      apply hx
      exact Or.inr ⟨(a, a • x), ⟨ha, subset_tsupport f hne⟩, inv_smul_smul a x⟩
    simpa only [hx0, hax0, dist_self] using hε

/-- The base point may vary arbitrarily while the translating element
tends to the identity. -/
theorem compact_observable_moving_smul_difference
    (f : X → ℝ) (hf : Continuous f) (hc : HasCompactSupport f)
    {ι : Type*} {l : Filter ι} (x : ι → X) (a : ι → G)
    (ha : Tendsto a l (𝓝 1)) :
    Tendsto (fun n => |f (a n • x n) - f (x n)|) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hh := Metric.tendstoUniformly_iff.mp
    (compact_observable_smul_tendstoUniformly (G := G) f hf hc) ε hε
  filter_upwards [ha.eventually hh] with n hn
  simpa only [Real.dist_eq, sub_zero, abs_abs, abs_sub_comm] using hn (x n)

end DukePrimeDegree

end OAI
