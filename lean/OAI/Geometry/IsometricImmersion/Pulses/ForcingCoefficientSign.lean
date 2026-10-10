import OAI.Geometry.IsometricImmersion.Pulses.ActualForcingCoefficient
import OAI.Geometry.IsometricImmersion.Energy.MultiplierIntegral
import Mathlib.Analysis.Convex.Topology

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem closedRectangle_eq_Icc (l r b t : ℝ) :
    closedRectangle l r b t = Icc (![l,b]) (![r,t]) := by
  ext p
  change (p 0 ∈ Icc l r ∧ p 1 ∈ Icc b t) ↔
    (![l,b] ≤ p ∧ p ≤ ![r,t])
  constructor
  · intro hp
    constructor <;> intro i <;> fin_cases i
    · exact hp.1.1
    · exact hp.2.1
    · exact hp.1.2
    · exact hp.2.2
  · intro hp
    exact ⟨⟨hp.1 0,hp.2 0⟩,⟨hp.1 1,hp.2 1⟩⟩

theorem closedRectangle_isPreconnected (l r b t : ℝ) :
    IsPreconnected (closedRectangle l r b t) := by
  rw [closedRectangle_eq_Icc]
  exact (convex_Icc (![l,b] : Coord) (![r,t])).isPreconnected

def forcingFloor (e D C : ℝ) : ℝ := e/(2*max D 1*max C 1)

theorem forcingFloor_pos {e : ℝ} (he : 0 < e) (D C : ℝ) : 0 < forcingFloor e D C := by
  unfold forcingFloor
  have hD : 0 < max D 1 := zero_lt_one.trans_le (le_max_right _ _)
  have hC : 0 < max C 1 := zero_lt_one.trans_le (le_max_right _ _)
  positivity

theorem forcingCoefficient_floor_of_reference_margins
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U)
    {e c D C : ℝ} (he : 0 < e) (hc : 0 < c)
    (hE : e ≤ heightEnergy g z p) (hdet : (g p).det ≤ D)
    (hxx : c ≤ |covHessian g z p 0 0|) (hxxup : |covHessian g z p 0 0| ≤ C) :
    forcingFloor e D C ≤ |forcingCoefficient g z p| := by
  exact (forcingCoefficient_bounds hg hp he (hg.2 p hp).det_pos hc hE le_rfl le_rfl
    (hdet.trans (le_max_left _ _)) hxx (hxxup.trans (le_max_left _ _))).2.1

theorem actual_forcingCoefficient_signed_floor
    {g : MetricField} {z : Coord → ℝ} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (hSU : S ⊆ U) (hS : IsPreconnected S)
    {p0 : Coord} (hp0 : p0 ∈ S) {e c D C : ℝ} (he : 0 < e) (hc : 0 < c)
    (hE : ∀ p ∈ S, e ≤ heightEnergy g z p)
    (hdet : ∀ p ∈ S, (g p).det ≤ D)
    (hxx : ∀ p ∈ S, c ≤ |covHessian g z p 0 0|)
    (hxxup : ∀ p ∈ S, |covHessian g z p 0 0| ≤ C) :
    ∃ sigma : ℝ, |sigma| = 1 ∧ ∀ p ∈ S,
      sigma*forcingCoefficient g z p = |forcingCoefficient g z p| ∧
      forcingFloor e D C ≤ sigma*forcingCoefficient g z p := by
  have hxxne : ∀ p ∈ S, covHessian g z p 0 0 ≠ 0 := by
    intro p hp hz0
    have hh := hxx p hp
    rw [hz0,abs_zero] at hh
    linarith
  have hsign := forcingCoefficient_one_sign hg hz hU hSU hS
    (fun p hp => he.trans_le (hE p hp)) hxxne
  have hfloor (p : Coord) (hp : p ∈ S) :=
    forcingCoefficient_floor_of_reference_margins hg (hSU hp) he hc
      (hE p hp) (hdet p hp) (hxx p hp) (hxxup p hp)
  have hanchor : forcingCoefficient g z p0 ≠ 0 :=
    abs_pos.mp ((forcingFloor_pos he D C).trans_le (hfloor p0 hp0))
  rcases lt_or_gt_of_ne hanchor with hneg | hpos
  · refine ⟨-1,by norm_num,?_⟩
    intro p hp
    have hpneg : forcingCoefficient g z p < 0 := by
      by_contra hn
      have hn0 : 0 ≤ forcingCoefficient g z p := le_of_not_gt hn
      have hnonpos := mul_nonpos_of_nonpos_of_nonneg hneg.le hn0
      linarith [hsign p0 hp0 p hp]
    constructor
    · rw [abs_of_neg hpneg]
      ring
    · simpa only [neg_one_mul,abs_of_neg hpneg] using hfloor p hp
  · refine ⟨1,by norm_num,?_⟩
    intro p hp
    have hppos : 0 < forcingCoefficient g z p := by
      by_contra hn
      have hn0 : forcingCoefficient g z p ≤ 0 := le_of_not_gt hn
      have hnonpos := mul_nonpos_of_nonneg_of_nonpos hpos.le hn0
      linarith [hsign p0 hp0 p hp]
    constructor
    · rw [one_mul,abs_of_pos hppos]
    · simpa only [one_mul,abs_of_pos hppos] using hfloor p hp

end SmoothLocal.Pulse

end

end OAI
