import OAI.Geometry.RCD.Transport.FiniteContinuousChord
import OAI.Geometry.RCD.Transport.ReducedDyadicChord
import OAI.Geometry.RCD.Transport.RenyiChord

namespace OAI

/-! # A compressed optimal plan with exact reduced interpolation

Finite length components inherit the whole maximal tree. Their scalar
interpolation bounds extend by upper semicontinuity, and shrinking the
length bins recovers the original endpoint-weighted distortion integral.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.compressed_reduced_interpolation
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X) (hK : K≤0)
    {N : ℝ} (hN : (n:ℝ)≤N) (a : RenyiTransportNode n X)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C≠∞) (hc : ∀ t : Time, π.map (fun γ => γ t)≤C • hausdorff n X)
    (hm : ∀ m, RenyiDyadicMaximal (hausdorff n X) (1-1/N) (fun t => π.map (fun γ => γ t)) m) :
    ∀ t, ReducedRenyiChordBound (hausdorff n X) K N π t := by
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  have hN1 : 1<N := by
    have hnR : (2:ℝ)≤n := by exact_mod_cast hn
    linarith
  have hNp : 1<N+1 := by linarith
  let g := fun (s : Time) (γ : C(Time,X)) => ((π.map (fun γ => γ s)).rnDeriv μ (γ s))^(-(1/N))
  have hgm (s : Time) : Measurable (g s) :=
    (((π.map (fun γ => γ s)).measurable_rnDeriv μ).comp (measurable_path_eval s)).pow_const _
  have he (s : Time) : (∫⁻ γ, g s γ ∂π)=renyiIntegral μ (π.map (fun γ => γ s)) N := by
    rw [←lintegral_map (((π.map (fun γ => γ s)).measurable_rnDeriv μ).pow_const _)
      (measurable_path_eval s),←renyiIntegral_eq_inverse_density μ _
      (Measure.absolutelyContinuous_of_le_smul (hc s)) hN1]
  intro t
  by_cases h0 : t=0
  · subst t
    unfold ReducedRenyiChordBound
    simp only [show ((0:Time):ℝ)=0 from rfl,sub_zero,sigma_nonpos_one hK hNp dist_nonneg,
      sigma_nonpos_zero hK hNp dist_nonneg,one_mul,zero_mul,add_zero]
    exact (he 0).le
  by_cases h1 : t=1
  · subst t
    unfold ReducedRenyiChordBound
    simp only [show ((1:Time):ℝ)=1 from rfl,sub_self,sigma_nonpos_one hK hNp dist_nonneg,
      sigma_nonpos_zero hK hNp dist_nonneg,one_mul,zero_mul,zero_add]
    exact (he 1).le
  have ht0 : 0<(t:ℝ) := lt_of_le_of_ne t.property.1 (by
    intro hh; apply h0; exact Subtype.ext hh.symm)
  have ht1 : (t:ℝ)<1 := lt_of_le_of_ne t.property.2 (by
    intro hh; apply h1; exact Subtype.ext hh)
  let ε := fun j : ℕ => (1/2:ℝ)^j
  have hε (j) : 0<ε j := pow_pos (by norm_num) _
  have hεt : Tendsto ε atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hD := a.distance_bound π inferInstance hg hp
  apply reduced_chord_mesh_limit π hK hNp t ht0 ht1
    (fun γ : C(Time,X) => dist (γ 0) (γ 1))
    ((measurable_path_eval 0).dist (measurable_path_eval 1)) (fun _ => dist_nonneg)
    (g 0) (g 1) (hgm 0) (hgm 1) hε hεt
  intro j
  have hb := weighted_chord_bin_entropy μ hN1 π
    (Measure.absolutelyContinuous_of_le_smul (hc 0))
    (Measure.absolutelyContinuous_of_le_smul (hc 1))
    (sigma K (N+1) (1-(t:ℝ))) (sigma K (N+1) (t:ℝ)) (hε j) hD
  apply hb.trans
  exact hX.finite_component_chord_all_times K n hn hK hN a π hg hp hC hc hm
    (lengthBin (ε j)) (Finset.range (⌊a.distance/ε j⌋₊+1)) (lengthBin_measurable (ε j))
    (fun _ _ _ _ hij => lengthBin_pairwise (hε j) hij)
    (hD.mono (fun _ hd => lengthBin_finite_cover (hε j) dist_nonneg hd))
    (fun i => ((i:ℝ)+1)*ε j) (fun i _ => mul_nonneg (by positivity) (hε j).le)
    (fun _ _ _ hd => hd.2.le) t

theorem NoncollapsedRCD.exists_compressed_reduced_interpolation
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X) (hK : K≤0)
    {N : ℝ} (hN : (n:ℝ)≤N) (a : RenyiTransportNode n X) :
    ∃ π : Measure C(Time,X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))) ∧
      (∀ t : Time, π.map (fun γ => γ t)≤compressionBudget K n a.distance a.capacity • hausdorff n X) ∧
      ∀ t, ReducedRenyiChordBound (hausdorff n X) K N π t := by
  obtain ⟨π,hπ,hg,hp,hc,hm,_⟩ := hX.exists_compressed_renyi_chord K n hn hK hN a
  let := hπ
  exact ⟨π,hπ,hg,hp,hc,hX.compressed_reduced_interpolation K n hn hK hN a π hg hp
    (compressionBudget_ne_top K n a.distance a.capacity_finite) hc hm⟩

end RegularPointCoordinates

end

end OAI
