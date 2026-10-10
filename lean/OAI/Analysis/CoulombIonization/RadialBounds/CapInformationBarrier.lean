import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.BarrierInitialDeterministicBarrier
import OAI.Analysis.CoulombIonization.Localization.ActualPointInverseBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.SpatialCapSubmeanBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CapInformation_barrier_scope

open MeasureTheory Set

namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier

lemma original_capBandStatistic_info_measurable {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀) (hs : 0 < s)
    (u C : ℝ) :
    Measurable[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j]
      (fun z => capBandStatistic u C (originalQueryField F Z lam r j c₁ r₀ s z)) := by
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  have hm := jointMasterPosterior_measurable (graphRawLaw F) ell j hc hr₀ hs
    canonicalRealPacket_smooth.continuous
  have hf : Measurable (fun p : OriginalDatum N K ell j × Space =>
      Z/‖p.2‖-lam-tfPotential (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket p.1) p.2) :=
    ((measurable_const.div measurable_snd.norm).sub measurable_const).sub
      (potential_joint_measurable hm)
  exact (((hf.const_mul _).sub measurable_const).max measurable_const).stronglyMeasurable.integral_prod_right'.measurable.const_mul _

end CoulombAtom

end Work_CapInformation_barrier_scope

open MeasureTheory Filter Set Metric

namespace CoulombAnalysis
open CoulombAtom CoulombBarrier

lemma norm_sixth_difference_le {r : ℝ} (_hr : 0 < r) {x y : Space}
    (hx : ‖x‖ ≤ 2*r) (hy : ‖y‖ ≤ 2*r) :
    |‖x‖^6-‖y‖^6| ≤ 192*r^5*‖x-y‖ := by
  have hp := abs_pow_sub_pow_le (a := ‖x‖) (b := ‖y‖) (n := 6)
  simp only [abs_of_nonneg (norm_nonneg x),abs_of_nonneg (norm_nonneg y)] at hp
  calc
    _ ≤ |‖x‖-‖y‖| *6*(max ‖x‖ ‖y‖)^5 := by simpa only [Nat.cast_ofNat] using hp
    _ ≤ ‖x-y‖*6*(2*r)^5 := by
      gcongr
      · exact abs_norm_sub_norm_le x y
      · exact max_le hx hy
    _ = _ := by ring

lemma normalized_density_net_variation {ρ : Space → ℝ} {x y : Space} {u D L w : ℝ}
    (hu : 0 < u) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hx : ‖x‖ ≤ 2*u) (hy : ‖y‖ ≤ 2*u) (hxy : ‖x-y‖ ≤ u^2)
    (hn : 0 ≤ ρ y) (hden : ρ y ≤ D*u^(-6-3*w))
    (hq : ‖ρ x-ρ y‖ ≤ L*u^(-7-4*w)*‖x-y‖) :
    |‖x‖^6*ρ x-‖y‖^6*ρ y| ≤ 64*L*u^(1-4*w)+192*D*u^(1-3*w) := by
  have hxp : ‖x‖^6 ≤ 64*u^6 := by
    calc _ ≤ (2*u)^6 := pow_le_pow_left₀ (norm_nonneg x) hx 6
         _ = _ := by ring
  have heq (n : ℕ) (v : ℝ) : u^n*u^v = u^((n:ℝ)+v) := by
    rw [←Real.rpow_natCast,Real.rpow_add hu]
  have hp₁ : u^6*u^(-7-4*w)*u^2 = u^(1-4*w) := by
    rw [mul_right_comm,←pow_add,heq]
    congr 1
    norm_num
    ring
  have hp₂ : u^5*u^2*u^(-6-3*w) = u^(1-3*w) := by
    rw [←pow_add,heq]
    congr 1
    norm_num
    ring
  have hfirst : ‖x‖^6*|ρ x-ρ y| ≤ 64*L*u^(1-4*w) := by
    calc
      _ ≤ (64*u^6)*(L*u^(-7-4*w)*‖x-y‖) :=
        mul_le_mul hxp (by simpa only [Real.norm_eq_abs] using hq) (abs_nonneg _) (by positivity)
      _ ≤ (64*u^6)*(L*u^(-7-4*w)*u^2) := by gcongr
      _ = 64*L*(u^6*u^(-7-4*w)*u^2) := by ring
      _ = _ := by rw [hp₁]
  have hsecond : |‖x‖^6-‖y‖^6| *|ρ y| ≤ 192*D*u^(1-3*w) := by
    rw [abs_of_nonneg hn]
    calc
      _ ≤ (192*u^5*‖x-y‖)*(D*u^(-6-3*w)) :=
        mul_le_mul (norm_sixth_difference_le hu hx hy) hden hn (by positivity)
      _ ≤ (192*u^5*u^2)*(D*u^(-6-3*w)) := by gcongr
      _ = 192*D*(u^5*u^2*u^(-6-3*w)) := by ring
      _ = _ := by rw [hp₂]
  calc
    _ = |‖x‖^6*(ρ x-ρ y)+(‖x‖^6-‖y‖^6)*ρ y| := by congr 1; ring
    _ ≤ |‖x‖^6*(ρ x-ρ y)|+|(‖x‖^6-‖y‖^6)*ρ y| := abs_add_le _ _
    _ = ‖x‖^6*|ρ x-ρ y|+|‖x‖^6-‖y‖^6| *|ρ y| := by
      rw [abs_mul,abs_of_nonneg (pow_nonneg (norm_nonneg x) 6),abs_mul]
    _ ≤ _ := add_le_add hfirst hsecond

end CoulombAnalysis

end

end OAI
