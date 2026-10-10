import Mathlib
import OAI.Geometry.WeakHessian.Transport.DensityMeasure
import OAI.Geometry.WeakHessian.Transport.DualTransportPairing

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology

namespace WeakHessianTransport

section DualPairing
open WeakHessian WeakHessianFunctional MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [MeasurableSpace X] [BorelSpace X] (m : Measure X) [IsFiniteMeasure m]

lemma boundedHopfLp_dual_pairing_le
    {f : X →ᵇ ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {ρ A : ℝ → Lp ℝ 2 m} {b α M : ℝ}
    (hb : 0 ≤ b) (hα : 0 < α) (hρ : ContinuousOn ρ (Icc 0 b))
    (hlower : ∀ t ∈ Ico 0 b, ∀ᵐ x ∂m, α ≤ ρ t x)
    (hyoung : ∀ t ∈ Ico 0 b, ∀ q : Lp ℝ 2 m, cheegerEnergy m (q : X → ℝ) < ∞ →
      -α*(cheegerEnergy m (q : X → ℝ)).toReal + ⟪q,A t⟫_ℝ ≤ M)
    (hderiv : ∀ t ∈ Ico 0 b, HasDerivWithinAt ρ (A t) (Ici t) t) :
    ⟪boundedHopfLp m f b,ρ b⟫_ℝ - ⟪BoundedContinuousFunction.toLp 2 m ℝ f,ρ 0⟫_ℝ ≤ b*M := by
  rcases hb.eq_or_lt with rfl | hb
  · simp [boundedHopfLp]
  have H (a : ℝ) (ha : 0 < a) (hab : a ≤ b) :
      ⟪boundedHopfLp m f b,ρ b⟫_ℝ - ⟪boundedHopfLp m f a,ρ a⟫_ℝ ≤ (b-a)*M := by
    have hsub : Icc a b ⊆ Icc 0 b := Icc_subset_Icc ha.le le_rfl
    have hq : ContinuousOn (boundedHopfLp m f) (Icc a b) := (continuousOn_boundedHopfLp m hf).mono
      (fun t ht => ha.le.trans ht.1)
    apply dualTransport_pairing_le ha hab hα hq (hρ.mono hsub)
    · intro t ht
      exact hyoung t ⟨ha.le.trans ht.1,ht.2⟩ _ (boundedHopfLp_energy_bound m f (ha.trans_le ht.1)).1
    · intro t ht
      exact hderiv t ⟨ha.le.trans ht.1,ht.2⟩
    · intro t ht s hs
      exact boundedHopfLp_pairing_increment m f (ha.trans_le ht.1) hs.1.le hα.le (ρ t)
        (hlower t ⟨ha.le.trans ht.1,ht.2⟩)
  have hq0 : Tendsto (boundedHopfLp m f) (𝓝[>] (0:ℝ)) (𝓝 (BoundedContinuousFunction.toLp 2 m ℝ f)) := by
    simpa only [boundedHopfLp, boundedHopfMap_zero] using
      ((continuousOn_boundedHopfLp m hf) 0 (by simp)).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hρ0 : Tendsto ρ (𝓝[>] (0:ℝ)) (𝓝 (ρ 0)) :=
    (hρ 0 ⟨le_rfl,hb.le⟩).mono_left (nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem ⟨le_rfl,hb⟩))
  have hleft : Tendsto (fun a : ℝ => ⟪boundedHopfLp m f b,ρ b⟫_ℝ-⟪boundedHopfLp m f a,ρ a⟫_ℝ)
      (𝓝[>] (0:ℝ)) (𝓝 (⟪boundedHopfLp m f b,ρ b⟫_ℝ-⟪BoundedContinuousFunction.toLp 2 m ℝ f,ρ 0⟫_ℝ)) :=
    tendsto_const_nhds.sub (hq0.inner hρ0)
  have hright : Tendsto (fun a : ℝ => (b-a)*M) (𝓝[>] (0:ℝ)) (𝓝 (b*M)) := by
    have hc : Continuous (fun a : ℝ => (b-a)*M) := by fun_prop
    simpa only [sub_zero] using (hc.tendsto (0:ℝ)).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [Ioc_mem_nhdsGT hb] with a ha
  exact H a ha.1 ha.2

end DualPairing

open WeakHessian WeakHessianFunctional MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] (m : Measure X) [IsFiniteMeasure m]

lemma proper_dual_density_coupling_bound
    {ρ A : ℝ → Lp ℝ 2 m} {α M : ℝ}
    (hα : 0 < α) (hρ : ContinuousOn ρ (Icc 0 1))
    (hpos : ∀ t ∈ Icc 0 1, ∀ᵐ x ∂m, 0 ≤ ρ t x)
    (hmass : ∀ t ∈ Icc 0 1, ∫ x, ρ t x ∂m = 1)
    (hlower : ∀ t ∈ Ico 0 1, ∀ᵐ x ∂m, α ≤ ρ t x)
    (hyoung : ∀ t ∈ Ico 0 1, ∀ q : Lp ℝ 2 m, cheegerEnergy m (q : X → ℝ) < ∞ →
      -α*(cheegerEnergy m (q : X → ℝ)).toReal + ⟪q,A t⟫_ℝ ≤ M)
    (hderiv : ∀ t ∈ Ico 0 1, HasDerivWithinAt ρ (A t) (Ici t) t) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = densityMeasure m (ρ 1) ∧
      q.map Prod.snd = densityMeasure m (ρ 0) ∧
      (∫⁻ p, (edist p.1 p.2)^2 ∂q) ≤ ENNReal.ofReal (2*M) := by
  let hp0 := densityMeasure_probability m (ρ 0) (hpos 0 (by norm_num)) (hmass 0 (by norm_num))
  let hp1 := densityMeasure_probability m (ρ 1) (hpos 1 (by norm_num)) (hmass 1 (by norm_num))
  apply exists_proper_coupling_cost_of_hopf_bound _ _ (2*M)
  intro f hf
  obtain ⟨L,hf⟩ := hf
  let f' : X →ᵇ ℝ := f
  have H := boundedHopfLp_dual_pairing_le m (f := f') hf (by norm_num : (0:ℝ) ≤ 1)
    hα hρ hlower hyoung hderiv
  have hq : (fun x => hopfLax f 1 x) = (boundedHopfMap f' 1 : X → ℝ) := by
    funext x
    exact (boundedHopfMap_apply_pos f' (by norm_num) x).symm
  rw [hq, integral_densityMeasure_boundedContinuous m _ (hpos 1 (by norm_num))]
  change _ - (∫ x, f' x ∂densityMeasure m (ρ 0)) ≤ _
  rw [integral_densityMeasure_boundedContinuous m _ (hpos 0 (by norm_num))]
  change ⟪boundedHopfLp m f' 1,ρ 1⟫_ℝ - ⟪BoundedContinuousFunction.toLp 2 m ℝ f',ρ 0⟫_ℝ ≤ _
  calc
    _ ≤ 1*M := H
    _ = _ := by ring

end WeakHessianTransport

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
