import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.CheegerClosedQuadraticEnergy
import OAI.Geometry.WeakHessian.Transport.HopfLpPairingIncrement
import OAI.Geometry.WeakHessian.HeatFlow.FormGeneratorYoung

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter
open scoped Topology ENNReal NNReal

namespace WeakHessianTransport
open WeakHessian WeakHessianFunctional MeasureTheory
open scoped InnerProductSpace

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (m : Measure X) [IsFiniteMeasure m]

lemma hopfLp_transport_pairing_le (h : QuadraticCheegerEnergy m)
    {f : C(X,ℝ)} {L : ℝ≥0} (hf : LipschitzWith L f)
    {ρ u A : ℝ → Lp ℝ 2 m} {b α c C : ℝ}
    (hb : 0 ≤ b) (hα : 0 < α) (hρ : ContinuousOn ρ (Icc 0 b))
    (hlower : ∀ t ∈ Ico 0 b, ∀ᵐ x ∂m, α ≤ ρ t x)
    (hgen : ∀ t ∈ Ico 0 b, (cheeger_closedQuadraticEnergy h).IsFormGenerator (u t) (A t))
    (hener : ∀ t ∈ Ico 0 b, (cheegerEnergy m (u t : X → ℝ)).toReal ≤ C)
    (hderiv : ∀ t ∈ Ico 0 b, HasDerivWithinAt ρ (c • A t) (Ici t) t) :
    ⟪hopfLp m f b,ρ b⟫_ℝ - ⟪ContinuousMap.toLp 2 m ℝ f,ρ 0⟫_ℝ ≤ b*c^2/α*C := by
  rcases hb.eq_or_lt with rfl | hb
  · simp [hopfLp]
  have H (a : ℝ) (ha : 0 < a) (hab : a ≤ b) :
      ⟪hopfLp m f b,ρ b⟫_ℝ - ⟪hopfLp m f a,ρ a⟫_ℝ ≤ (b-a)*c^2/α*C := by
    have hsub : Icc a b ⊆ Icc 0 b := Icc_subset_Icc ha.le le_rfl
    have hq : ContinuousOn (hopfLp m f) (Icc a b) := (continuousOn_hopfLp m hf).mono
      (fun t ht => ha.le.trans ht.1)
    apply (cheeger_closedQuadraticEnergy h).transport_pairing_le ha hab hα hq (hρ.mono hsub)
    · intro t ht
      exact (hopfLp_energy_bound m f (ha.trans_le ht.1)).1
    · intro t ht
      exact hgen t ⟨ha.le.trans ht.1,ht.2⟩
    · intro t ht
      exact hener t ⟨ha.le.trans ht.1,ht.2⟩
    · intro t ht
      exact hderiv t ⟨ha.le.trans ht.1,ht.2⟩
    · intro t ht s hs
      exact hopfLp_pairing_increment m f (ha.trans_le ht.1) hs.1.le hα.le (ρ t)
        (hlower t ⟨ha.le.trans ht.1,ht.2⟩)
  have hq0 : Tendsto (hopfLp m f) (𝓝[>] (0:ℝ)) (𝓝 (ContinuousMap.toLp 2 m ℝ f)) := by
    simpa only [hopfLp, hopfMap_zero] using
      ((continuousOn_hopfLp m hf) 0 (by simp)).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hρ0 : Tendsto ρ (𝓝[>] (0:ℝ)) (𝓝 (ρ 0)) :=
    (hρ 0 ⟨le_rfl,hb.le⟩).mono_left (nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem ⟨le_rfl,hb⟩))
  have hleft : Tendsto (fun a : ℝ => ⟪hopfLp m f b,ρ b⟫_ℝ-⟪hopfLp m f a,ρ a⟫_ℝ)
      (𝓝[>] (0:ℝ)) (𝓝 (⟪hopfLp m f b,ρ b⟫_ℝ-⟪ContinuousMap.toLp 2 m ℝ f,ρ 0⟫_ℝ)) :=
    tendsto_const_nhds.sub (hq0.inner hρ0)
  have hright : Tendsto (fun a : ℝ => (b-a)*c^2/α*C) (𝓝[>] (0:ℝ)) (𝓝 (b*c^2/α*C)) := by
    have hc : Continuous (fun a : ℝ => (b-a)*c^2/α*C) := by fun_prop
    simpa only [sub_zero] using (hc.tendsto (0:ℝ)).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [Ioc_mem_nhdsGT hb] with a ha
  exact H a ha.1 ha.2

end WeakHessianTransport

open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
