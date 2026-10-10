import OAI.Geometry.RCD.Transport.FiniteComponentChord
import OAI.Geometry.RCD.Transport.ReducedChordMeshLimit

namespace OAI

/-! # Exact distance-weighted interpolation at every dyadic time -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

def ReducedRenyiChordBound (μ : Measure X) (K N : ℝ) (π : Measure C(Time,X)) (t : Time) : Prop :=
  (∫⁻ γ, sigma K (N+1) (1-(t:ℝ)) (dist (γ 0) (γ 1))*
    ((π.map (fun γ => γ 0)).rnDeriv μ (γ 0))^(-(1/N))+
    sigma K (N+1) (t:ℝ) (dist (γ 0) (γ 1))*
    ((π.map (fun γ => γ 1)).rnDeriv μ (γ 1))^(-(1/N)) ∂π)≤
      renyiIntegral μ (π.map (fun γ => γ t)) N

theorem NoncollapsedRCD.reduced_dyadic_chord
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X) (hK : K≤0)
    {N : ℝ} (hN : (n:ℝ)≤N) (a : RenyiTransportNode n X)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C≠∞) (hc : ∀ t : Time, π.map (fun γ => γ t)≤C • hausdorff n X)
    {m : ℕ} (hm : RenyiDyadicMaximal (hausdorff n X) (1-1/N) (fun t => π.map (fun γ => γ t)) m)
    {t : Time} (ht : t∈dyadicGrid m) (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) :
    ReducedRenyiChordBound (hausdorff n X) K N π t := by
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  have hN1 : 1<N := by
    have hnR : (2:ℝ)≤n := by exact_mod_cast hn
    linarith
  let g := fun (s : Time) (γ : C(Time,X)) => ((π.map (fun γ => γ s)).rnDeriv μ (γ s))^(-(1/N))
  have hgm (s : Time) : Measurable (g s) :=
    (((π.map (fun γ => γ s)).measurable_rnDeriv μ).comp (measurable_path_eval s)).pow_const _
  let ε := fun j : ℕ => (1/2:ℝ)^j
  have hε (j) : 0<ε j := pow_pos (by norm_num) _
  have hεt : Tendsto ε atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hD := a.distance_bound π inferInstance hg hp
  apply reduced_chord_mesh_limit π hK (by linarith : 1<N+1) t ht0 ht1
    (fun γ : C(Time,X) => dist (γ 0) (γ 1))
    ((measurable_path_eval 0).dist (measurable_path_eval 1)) (fun _ => dist_nonneg)
    (g 0) (g 1) (hgm 0) (hgm 1) hε hεt
  intro j
  have hb := weighted_chord_bin_entropy μ hN1 π
    (Measure.absolutelyContinuous_of_le_smul (hc 0))
    (Measure.absolutelyContinuous_of_le_smul (hc 1))
    (sigma K (N+1) (1-(t:ℝ))) (sigma K (N+1) (t:ℝ)) (hε j) hD
  apply hb.trans
  exact hX.finite_component_scalar_chord K n hn hK hN a π hg hp hC hc hm
    (lengthBin (ε j)) (Finset.range (⌊a.distance/ε j⌋₊+1)) (lengthBin_measurable (ε j))
    (fun _ _ _ _ hij => lengthBin_pairwise (hε j) hij)
    (hD.mono (fun _ hd => lengthBin_finite_cover (hε j) dist_nonneg hd))
    (fun i => ((i:ℝ)+1)*ε j) (fun i _ => mul_nonneg (by positivity) (hε j).le)
    (fun _ _ _ hd => hd.2.le) ht ht0 ht1

end RegularPointCoordinates

end

end OAI
