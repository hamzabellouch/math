import OAI.Analysis.CircleDomains.Probability.LocalNullImage
import OAI.Analysis.CircleDomains.Modulus.PathVariation
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! A finite payment measure that vanishes on free times forces their
trace image to be null, once interval oscillation is paid. This is the
last measure-theoretic step of the local tag argument. -/

open Set MeasureTheory
open scoped ENNReal

namespace CircleDomainRigidity

private theorem locallyConnected_pathTime : LocallyConnectedSpace PathTime := by
  apply locallyConnectedSpace_of_connected_bases
    (fun x r => Metric.ball x r) (fun _ r => 0 < r)
    (fun _ => Metric.nhds_basis_ball)
  intro x r _
  apply (Topology.IsInducing.subtypeVal.isPreconnected_image).mp
  rw [Subtype.image_ball, Real.ball_eq_Ioo]
  exact (ordConnected_Ioo.inter ordConnected_Icc).isPreconnected

theorem path_time_null_image_of_interval_payment
    (κ : Measure PathTime) [IsFiniteMeasure κ] [κ.OuterRegular]
    {F V : Set PathTime} (hV : IsOpen V) (hF : κ (F ∩ V) = 0)
    (v : PathTime → ℝ)
    (hpay : ∀ r ∈ F ∩ V, ∀ s ∈ F ∩ V, r ≤ s → Icc r s ⊆ V →
      ENNReal.ofReal |v s - v r| ≤ κ (Icc r s)) :
    volume (v '' (F ∩ V)) = 0 := by
  let : LocallyConnectedSpace PathTime := locallyConnected_pathTime
  apply null_image_inter_open_of_connected_open_oscillation hV hF v (A := 1) zero_le_one
  intro U hUV _ hconn r hr s hs
  have hforward : ∀ p ∈ F ∩ U, ∀ q ∈ F ∩ U, p ≤ q →
      |v q - v p| ≤ κ.real U := by
    intro p hp q hq hpq
    have hi : Icc p q ⊆ U := hconn.isPreconnected.ordConnected.out hp.2 hq.2
    have h := hpay p ⟨hp.1, hUV hp.2⟩ q ⟨hq.1, hUV hq.2⟩ hpq (hi.trans hUV)
    have hreal := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top κ (Icc p q))).mp h
    exact hreal.trans (measureReal_mono hi)
  rw [one_mul]
  rcases le_total r s with h | h
  · simpa only [abs_sub_comm] using hforward r hr s hs h
  · exact hforward s hs r hr h

end CircleDomainRigidity

end OAI
