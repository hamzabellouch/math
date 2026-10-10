import Mathlib
import OAI.Geometry.WeakMTW.Support.ActiveSupports
import OAI.Geometry.WeakMTW.Coordinates.TangentScaling
import OAI.Geometry.WeakMTW.Support.ActiveGraphLimits
import OAI.Geometry.WeakMTW.Support.TangentHullCompact
import OAI.Geometry.WeakMTW.Coordinates.CostFirstTaylor

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
  {ι : Type*} [Fintype ι] [Nonempty ι]

 theorem minimizing_pole_direction (y : ι → M) (h : ι → ℝ)
    {x : M} {w : TangentSpace (model n) x} (hw : w ∈ minimizingDomain x)
    {s : ℝ} (hs : 0 < s)
    (hmin : ∀ z, cost x (exp x w) + s*finitePotential y h x ≤
      cost z (exp x w) + s*finitePotential y h z)
    (ξ : TangentSpace (model n) x) :
    ∃ a ∈ activeVelocities y h x, inner ℝ w ξ ≤ s*inner ℝ a ξ := by
  let c := chartAt (Model n) x
  let l : ℕ → ℝ := fun j => 1/((j:ℝ)+1)
  have hl : Tendsto l atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlpos (j : ℕ) : 0 < l j := one_div_pos.mpr (by positivity)
  let p : ℕ → M := fun j => c.symm (c x+l j•tangentChartLinear x ξ)
  have hp : Tendsto p atTop (𝓝 x) := by
    have hc := (c.symm.continuousAt (c.map_source (mem_chart_source (Model n) x))).tendsto
    have hh := (tendsto_const_nhds (x := c x)).add (hl.smul_const (tangentChartLinear x ξ))
    simp only [zero_smul,add_zero] at hh
    simpa only [p,Function.comp_def,c.left_inv (mem_chart_source (Model n) x)] using hc.comp hh
  choose a ha using fun j => activeVelocities_nonempty (n := n) y h (p j)
  obtain ⟨a₀,ha₀,ρ,hρ,hlim⟩ := active_velocity_subseq y h hp a ha
  have hz : Tendsto (fun j => exp (p (ρ j)) ((1/2:ℝ)•a (ρ j))) atTop (𝓝 (exp x ((1/2:ℝ)•a₀))) :=
    scaledExp_continuous.continuousAt.tendsto.comp (tendsto_const_nhds.prodMk_nhds hlim)
  have hne : ∀ᶠ j in atTop, l (ρ j) ≠ 0 := Eventually.of_forall (fun j => (hlpos (ρ j)).ne')
  have htW := cost_first_limit x (strict_radial_mem_injectivity hw (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)) ξ (tendsto_const_nhds (x := exp x ((1/2:ℝ)•w)))
      (hl.comp hρ.tendsto_atTop) hne
  have htA := cost_first_limit x (strict_radial_mem_injectivity ha₀.1 (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)) ξ hz (hl.comp hρ.tendsto_atTop) hne
  have hineq (j : ℕ) : 0 ≤
      (cost (p (ρ j)) (exp x ((1/2:ℝ)•w))-cost x (exp x ((1/2:ℝ)•w)))/l (ρ j) -
      s*((cost (p (ρ j)) (exp (p (ρ j)) ((1/2:ℝ)•a (ρ j)))-
        cost x (exp (p (ρ j)) ((1/2:ℝ)•a (ρ j))))/l (ρ j)) := by
    have h0 := hmin (p (ρ j))
    have h1 := shortened_upper_difference hw (by norm_num : (0:ℝ) < 1/2)
      (by norm_num : (1/2:ℝ) < 1) (p (ρ j))
    have h2 := activeSupport_le y h (p (ρ j)) (ha (ρ j)) (by norm_num : (0:ℝ) < 1/2)
      (by norm_num : (1/2:ℝ) < 1) x
    simp only [activeSupport] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 hs.le
    have hpos : 0 ≤ (cost (p (ρ j)) (exp x ((1/2:ℝ)•w))-cost x (exp x ((1/2:ℝ)•w)))-
        s*(cost (p (ρ j)) (exp (p (ρ j)) ((1/2:ℝ)•a (ρ j)))-cost x (exp (p (ρ j)) ((1/2:ℝ)•a (ρ j)))) := by
      norm_num at h1 h3
      nlinarith
    simpa only [sub_div,mul_div_assoc] using div_nonneg hpos (hlpos (ρ j)).le
  have hlim' := htW.sub (htA.const_mul s)
  have hle := ge_of_tendsto hlim' (Eventually.of_forall hineq)
  simp only [inner_smul_left,conj_trivial] at hle
  refine ⟨a₀,ha₀,?_⟩
  linarith

 theorem closed_convex_mem_of_directions {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {K : Set E}
    (hK : IsClosed K) (hc : Convex ℝ K) (hne : K.Nonempty) {u : E}
    (hu : ∀ ξ : E, ∃ a ∈ K, inner ℝ u ξ ≤ inner ℝ a ξ) : u ∈ K := by
  obtain ⟨v,hv,hm⟩ := exists_norm_eq_iInf_of_complete_convex hne hK.isComplete hc u
  have hproj := (norm_eq_iInf_iff_real_inner_le_zero hc hv).mp hm
  obtain ⟨a,ha,h⟩ := hu (u-v)
  have hp := hproj a ha
  rw [inner_sub_right,real_inner_comm a (u-v),real_inner_comm v (u-v)] at hp
  have hnorm : ‖u-v‖^2 ≤ 0 := by
    rw [← real_inner_self_eq_norm_sq,inner_sub_left]
    linarith
  have heq : u = v := sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (u-v)]))
  exact heq ▸ hv

 theorem minimizing_pole_capture (y : ι → M) (h : ι → ℝ)
    {x : M} {w : TangentSpace (model n) x} (hw : w ∈ minimizingDomain x)
    {s : ℝ} (hs : 0 < s)
    (hmin : ∀ z, cost x (exp x w) + s*finitePotential y h x ≤
      cost z (exp x w) + s*finitePotential y h z) :
    s⁻¹ • w ∈ activeHull y h x := by
  let : FiniteDimensional ℝ (TangentSpace (model n) x) :=
    VectorBundle.finiteDimensional ℝ (Model n) _ x
  let : CompleteSpace (TangentSpace (model n) x) := FiniteDimensional.complete ℝ _
  have hcl : IsClosed (activeHull (n := n) y h x) :=
    (tangentHull_closed (activeGraph_compact (n := n) y h)).preimage
      (FiberBundle.continuous_totalSpaceMk (Model n) (TangentSpace (model n)) x)
  apply closed_convex_mem_of_directions hcl (convex_convexHull ℝ _)
    ((activeVelocities_nonempty (n := n) y h x).mono (subset_convexHull ℝ _))
  intro ξ
  obtain ⟨a,ha,h⟩ := minimizing_pole_direction y h hw hs hmin ξ
  refine ⟨a,subset_convexHull ℝ _ ha,?_⟩
  simp only [inner_smul_left,conj_trivial]
  have hh := mul_le_mul_of_nonneg_left h (inv_pos.mpr hs).le
  simpa only [← mul_assoc,inv_mul_cancel₀ hs.ne',one_mul] using hh

 theorem activeHull_exp_surjective (y : ι → M) (h : ι → ℝ)
    {s : ℝ} (hs : 0 < s) (z : M) :
    ∃ x : M, ∃ b ∈ activeHull (n := n) y h x, exp x (s•b) = z := by
  let : Nonempty M := ⟨z⟩
  have hc : Continuous (fun x : M => cost x z+s*finitePotential y h x) :=
    ((cost_continuous (M := M)).comp (continuous_id.prodMk continuous_const)).add
      ((finitePotential_continuous y h).const_mul s)
  obtain ⟨x,_,hx⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty) hc.continuousOn
  obtain ⟨w,hw,hn⟩ := exists_minimizing_vector (n := n) x z
  have hwm : w ∈ minimizingDomain x := by
    change dist x (exp x w) = ‖w‖
    rw [hw,hn]
  have hmin : ∀ x', cost x (exp x w)+s*finitePotential y h x ≤
      cost x' (exp x w)+s*finitePotential y h x' := by
    intro x'
    rw [hw]
    exact hx (mem_univ x')
  refine ⟨x,s⁻¹•w,minimizing_pole_capture y h hwm hs hmin,?_⟩
  simpa only [smul_smul,mul_inv_cancel₀ hs.ne',one_smul] using hw

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
