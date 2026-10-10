import Mathlib
import OAI.Analysis.Conductivity.Sobolev.SobolevDistribution
import OAI.Analysis.Conductivity.Sources.NestedLimits
import OAI.Analysis.Conductivity.Walls.CriticalWall

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology

theorem exists_uniform_wall_source_gap {χ : Box3 → ℝ} {K : Set (ℝ×ℝ)}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hsχ : HasCompactSupport χ)
    (hK : IsClosed K) (hcore : ∀ q∈K,χ =ᶠ[𝓝 (q,0)] (fun _ => 1)) :
    ∃ δ : ℝ,0<δ ∧ ∀ (v : Box3 → ℝ) (a : (ℝ×ℝ) → ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) v → ContDiff ℝ (↑(⊤ : ℕ∞)) a →
      (∀ q,wallDerivative v (q,0)=0) →
      (∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0) →
      tsupport a⊆K → ∀ (j : Fin 2) (x : Coord3),
        x∈tsupport (symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v) j) →
        δ≤|(boxCoordinates x).2| := by
  let O : Set Box3 := {p | χ =ᶠ[𝓝 p] (fun _ => 1)}
  have ho : IsOpen O := isOpen_iff_mem_nhds.mpr (fun p hp => hp.eventually_nhds)
  let S : Set Box3 := (tsupport χ∩Prod.fst ⁻¹' K)∩Oᶜ
  have hS : IsCompact S :=
    (hsχ.inter_right (hK.preimage continuous_fst)).inter_right ho.isClosed_compl
  have hn (p : Box3) (hp : p∈S) : p.2≠0 := by
    intro hz
    have he : p=(p.1,0) := Prod.ext rfl hz
    have hon : χ =ᶠ[𝓝 p] (fun _ => 1) := by
      rw [he]
      exact hcore p.1 hp.1.2
    exact hp.2 hon
  obtain ⟨δ,hδ,hlo⟩ := hS.exists_forall_le' (continuous_snd.abs.continuousOn)
    (fun p hp => abs_pos.mpr (hn p hp))
  refine ⟨δ,hδ,?_⟩
  intro v a hv ha hz hne haK j x hx
  apply hlo
  have hxH := symmetricSource_tsupport _ _ j hx
  refine ⟨⟨(wallHomogeneousTensor_compact hsχ).2 hxH,
    haK (wallHomogeneousTensor_tsupport_surface hv ha hxH)⟩,?_⟩
  intro hone
  exact wallHomogeneousTensor_source_off_one hχ hv ha hz hne hone j hx

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma h1_layer_norm_bound {Z : H1} (hZ : Z∈H10) {K q : ℝ}
    (hK : 0≤K) (hq : 0≤q) (n : ℕ)
    (he : ‖weakGradientL Z‖^2≤K*q^n) :
    ‖Z‖≤h10PoincareConstant*Real.sqrt K*(Real.sqrt q)^n := by
  have hsK := Real.sq_sqrt hK
  have hsQ := Real.sq_sqrt hq
  have hp : (Real.sqrt K*(Real.sqrt q)^n)^2=K*q^n := by
    rw [mul_pow,←pow_mul,show n*2=2*n by omega,pow_mul,hsK,hsQ]
  have hn : ‖weakGradientL Z‖≤Real.sqrt K*(Real.sqrt q)^n := by
    nlinarith [norm_nonneg (weakGradientL Z),Real.sqrt_nonneg K,
      mul_nonneg (Real.sqrt_nonneg K) (pow_nonneg (Real.sqrt_nonneg q) n)]
  exact (H10_norm_le_weakGradientL (⟨Z,hZ⟩:H10)).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hn h10PoincareConstant_pos.le)

theorem geometric_source_series (Z : ℕ → H1) {K q : ℝ}
    (hK : 0≤K) (hq : 0≤q) (hq1 : q<1) (hZ : ∀ n, Z n∈H10)
    (hbound : ∀ n, ∀ᵐ x ∂ballMeasure, |weakValue (Z n) x|≤K*q^n)
    (henergy : ∀ n, ‖weakGradientL (Z n)‖^2≤K*q^n)
    (r : ℝ) (hsupp : ∀ n, ∀ᵐ x ∂ballMeasure, r<‖x‖ →
      weakValue (Z n) x=0 ∧ weakGradient (Z n) x=0) :
    ∃ w : H1, w∈H10 ∧
      Tendsto (fun N => ∑ n∈Finset.range N,Z n) atTop (𝓝 w) ∧
      (∀ᵐ x ∂ballMeasure, |weakValue w x|≤K/(1-q)) ∧
      (∀ᵐ x ∂ballMeasure, r<‖x‖ → weakValue w x=0 ∧ weakGradient w x=0) := by
  have hsq : Real.sqrt q<1 := by
    have hh := Real.sq_sqrt hq
    have hn := Real.sqrt_nonneg q
    nlinarith
  have hs : Summable (fun n => ‖Z n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => h1_layer_norm_bound (hZ n) hK hq n (henergy n))
      ((summable_geometric_of_lt_one (Real.sqrt_nonneg q) hsq).mul_left _)
  have hv : Summable (fun n => K*q^n) := (summable_geometric_of_lt_one hq hq1).mul_left K
  obtain ⟨w,hw,ht,hb,hsp⟩ := source_series_limit Z (fun n => K*q^n) hs hv
    (fun n => mul_nonneg hK (pow_nonneg hq n)) hZ hbound r hsupp
  refine ⟨w,hw,ht,?_,hsp⟩
  have hts : (∑' n : ℕ,K*q^n)=K/(1-q) := by
    rw [tsum_mul_left,tsum_geometric_of_lt_one hq hq1,div_eq_mul_inv]
  simpa only [hts] using hb

lemma source_energy_limit (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    {C : ℝ} (hC : 0≤C) (hb : ∀ᵐ x ∂ballMeasure, |a x|≤C)
    {w : ℕ → H1} {u : H1} (hw : Tendsto w atTop (𝓝 u)) (ψ : H1) :
    Tendsto (fun n => energy a (w n) ψ) atTop (𝓝 (energy a u ψ)) := by
  simpa only [Function.comp_def,ContinuousLinearMap.flip_apply,energyForm_apply] using
    ((energyForm a ha C hC hb).flip ψ).continuous.continuousAt.tendsto.comp hw

lemma source_energy_nonzero (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    {C : ℝ} (hC : 0≤C) (hb : ∀ᵐ x ∂ballMeasure, |a x|≤C)
    {w : ℕ → H1} {u : H1} (hw : Tendsto w atTop (𝓝 u)) (ψ : H1)
    (hne : ∀ᶠ n in atTop, energy a (w n) ψ=1) :
    u≠0 ∧ 0<ballMeasure {x | weakValue u x≠0} := by
  have he : energy a u ψ=1 := tendsto_nhds_unique
    (source_energy_limit a ha hC hb hw ψ) (tendsto_const_nhds.congr' (hne.mono (fun n hn => hn.symm)))
  have hu : u≠0 := by
    intro hz
    rw [hz,←energyForm_apply a ha C hC hb,map_zero,_root_.zero_apply] at he
    norm_num at he
  exact ⟨hu,nonzero_h1_positive_value_measure hu⟩

end ScalarConductivity

end
end

end OAI
