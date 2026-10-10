import OAI.Geometry.RCD.Heat.UniformHeatActionCenter
import OAI.Geometry.RCD.Sobolev.UniformVanishingGauge

namespace OAI

/-! # Sharp small-noise action lower bound for uniform compact laws

The limiting potential is constructed from the actual heat factors. Its
normalization constant vanishes; its lower bound has the exact quadratic
action coefficient, derived from the proved transport comparison.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem uniform_heat_action_lower (hK : K ≤ 0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (hν : ν.map Subtype.val = uniformOn (hausdorff n X) S)
    (z : X) {r R : ℝ} (hr : 0 < r) (hball : ball z r ⊆ S)
    (hR : 0 ≤ R) (hdS : ∀ a : S, dist z a ≤ R)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    ∃ (H : HeatActionLimit z) (ι : ℕ → ℕ), StrictMono ι ∧
      (∀ t ∈ Ioo (0:ℝ) 1, H.potential t z = 0) ∧
      (∀ t ∈ Ioo (0:ℝ) 1, ∀ x, -(dist z x)^2/(2*t) ≤ H.potential t x) ∧
      ∀ q : ℝ, 0 ≤ q → ∀ t : ℝ, (ht : t ∈ Ioo (0:ℝ) 1) →
        TendstoUniformly (fun k (x : closedBall z q) => ε (ι k)*Real.log
          (hX.compactHeatFactor hn p ν 1 (ε (ι k)*t/2)
            (div_pos (mul_pos (hε (ι k)) ht.1) (by norm_num)) x))
          (fun x => H.potential t x) atTop := by
  let μ := hausdorff n X
  have hS : IsCompact S := isCompact_iff_compactSpace.mpr inferInstance
  have hSf : μ S ≠ ∞ := (hX.finiteOnBounded S hS.isBounded).ne
  have hS0 : μ S ≠ 0 := ne_of_gt ((hX.fullSupport z r hr).trans_le (measure_mono hball))
  obtain ⟨ν',ρ,B,_hp,hmap,hm,hp,hb,hd⟩ := restricted_probability_law μ S
    hS.isClosed.measurableSet hS0 hSf
  have hνd : ν.map Subtype.val = μ.withDensity (fun x => ENNReal.ofReal (ρ x)) :=
    hν.trans (hmap.symm.trans hd)
  obtain ⟨H,ι,hι,hconv⟩ := hX.scaled_heat_action_limit hn p hK ν ρ hm hp
    (Eventually.of_forall hb) hνd (fun _ => 1) (by intros; norm_num) ε hε hε1 hε0 z hR hdS
  have hz (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : H.potential t z = 0 :=
    hX.uniform_heat_action_center hn p ν hν z hr hball ε hε hε0 H.potential ι hι hconv ht
  refine ⟨H,ι,hι,hz,fun t ht x => H.lower_of_center_zero hz ht x,?_⟩
  intro q hq t ht
  have hδ : 0 < t/2 := by linarith [ht.1]
  have hti : t ∈ Ioo (t/2) 1 := ⟨by linarith [ht.1],ht.2⟩
  have hc := hconv q hq (t/2) hδ t hti
  have he (k : ℕ) (x : closedBall z q) :
      hX.fixedGaugeScaledPotential hn p ν 1 (ε (ι k)) (hε (ι k)) (t/2) hδ z t x =
      ε (ι k)*Real.log (hX.compactHeatFactor hn p ν 1 (ε (ι k)*t/2)
        (div_pos (mul_pos (hε (ι k)) ht.1) (by norm_num)) x) -
      ε (ι k)*Real.log (hX.compactHeatFactor hn p ν 1 (ε (ι k)) (hε (ι k)) z) := by
    rw [hX.fixedGaugeScaledPotential_eq hn p ν 1 (ε (ι k)) (hε (ι k)) (t/2) hδ z hti.1.le x]
    rfl
  simp only [he] at hc
  apply uniform_of_sub_vanishing hc
  have hh := hX.compact_heat_reference_scaled_log hn p ν hν z hr hball
    (fun k => ε (ι k)) (fun k => hε (ι k)) (hε0.comp hι.tendsto_atTop) zero_lt_one
  simpa only [mul_one] using hh

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
