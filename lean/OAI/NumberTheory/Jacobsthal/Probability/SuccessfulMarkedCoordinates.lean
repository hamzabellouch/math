import OAI.NumberTheory.Jacobsthal.Estimates.CanonicalCoupledHistories

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.MarkedWindowCouplingGeometry

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeBinMembership
open ActualFlagInvariant NearbyParentGeometry RegeneratingInverseBands ArrivalKernelGeometry

theorem window_stability {b₀ b₁ rp rc sp tc x : ℝ} (hb₀ : 0 < b₀)
    (ht₀ : 209/100 ≤ tc) (ht₁ : tc ≤ 213/100)
    (hx₀ : 10*b₀/(313/100) ≤ x) (hx₁ : x ≤ b₁/(309/100))
    (hcurve : rc = x*tc) (hpq : rp ≤ (11/10)*rc) (hqp : rc ≤ (11/10)*rp)
    (hnear : |sp-tc| ≤ 1/100) :
    208/100 ≤ sp ∧ sp ≤ 214/100 ∧ 2*b₀ ≤ rp/sp ∧ rp/sp ≤ b₁/2 ∧ 6*b₀ < rp := by
  have hs₀ : 208/100 ≤ sp := by linarith [(abs_le.mp hnear).1]
  have hs₁ : sp ≤ 214/100 := by linarith [(abs_le.mp hnear).2]
  have hsp : 0 < sp := by linarith
  have hx0 : 0 < x := (div_pos (by positivity) (by norm_num : 0 < (313/100:ℝ))).trans_le hx₀
  have hl : 10*b₀ ≤ x*(313/100) := (div_le_iff₀ (by norm_num : 0 < (313/100:ℝ))).mp hx₀
  have hu : x*(309/100) ≤ b₁ := (le_div_iff₀ (by norm_num : 0 < (309/100:ℝ))).mp hx₁
  have hb₁ : 0 < b₁ := by nlinarith
  have hrc₀ : (209/100)*x ≤ rc := by nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr ht₀)]
  have hrc₁ : rc ≤ (213/100)*x := by nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr ht₁)]
  have hgap : 6*b₀ < rp := by nlinarith
  refine ⟨hs₀,hs₁,?_,?_,hgap⟩
  · apply (le_div_iff₀ hsp).mpr
    nlinarith [mul_nonneg hb₀.le (sub_nonneg.mpr hs₁)]
  · apply (div_le_iff₀ hsp).mpr
    nlinarith [mul_nonneg hb₁.le (sub_nonneg.mpr hs₀)]

theorem actual_marked_window {w ell S v mesh b₀ b₁ : ℝ} {start : Node}
    {n : ℕ} (h : History w ell S start) (z : CostState)
    (hb₀ : 0 < b₀)
    (hpositive : 0 < h.node.gap) (hconsistent : Consistent h.node)
    (hgood : GoodAt v mesh n (some h,Sum.inl z))
    (heven : stateSide z.1 = .even)
    (ht₀ : 209/100 ≤ stateRatio z.1) (ht₁ : stateRatio z.1 ≤ 213/100)
    (hx₀ : 10*b₀/(313/100) ≤ currentExponent v z)
    (hx₁ : currentExponent v z ≤ b₁/(309/100))
    (hmesh : mesh ≤ 1/100) (herror : 4*(n:ℝ)*mesh ≤ Real.log (11/10)) :
    h.node.side = .even ∧ 208/100 ≤ h.node.ratio ∧ h.node.ratio ≤ 214/100 ∧
      2*b₀ ≤ h.node.cutoff ∧ h.node.cutoff ≤ b₁/2 ∧ 6*b₀ < h.node.gap := by
  change liveGood v mesh n h z at hgood
  have hrel := log_gap_relative hpositive (Real.exp_pos _) hgood.2.2.2
  have he : Real.exp (4*(n:ℝ)*mesh) ≤ (11/10:ℝ) := by
    rw [← Real.exp_log (by norm_num : 0 < (11/10:ℝ))]
    exact Real.exp_le_exp.mpr herror
  have hpq : h.node.gap ≤ (11/10)*gapValue v z :=
    hrel.1.trans (mul_le_mul_of_nonneg_right he (Real.exp_pos _).le)
  have hqp : gapValue v z ≤ (11/10)*h.node.gap :=
    hrel.2.trans (mul_le_mul_of_nonneg_right he hpositive.le)
  have hcurve : gapValue v z = currentExponent v z*stateRatio z.1 := by
    unfold currentExponent
    exact (div_mul_cancel₀ _ (OccupationBoundaries.stateRatio_pos z.1).ne').symm
  have hg := window_stability hb₀ ht₀ ht₁ hx₀ hx₁ hcurve hpq hqp (hgood.2.2.1.trans hmesh)
  refine ⟨hgood.2.1.trans heven,hg.1,hg.2.1,?_,?_,hg.2.2.2.2⟩
  · rw [hconsistent]
    exact hg.2.2.1
  · rw [hconsistent]
    exact hg.2.2.2.1

end NumberTheoryLean.MarkedWindowCouplingGeometry

end

section

namespace NumberTheoryLean.SuccessfulMarkedCoordinates

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualProcessCoupling ActualFlagInvariant ActualCoupledHistories ActualSuccessfulHistories
open FiniteHistoryTransport MarkedWindowCouplingGeometry ArrivalKernelGeometry

def primeWindow (b₀ b₁ : ℝ) (z : Node) : Prop :=
  z.side = .even ∧ 208/100 ≤ z.ratio ∧ z.ratio ≤ 214/100 ∧
    2*b₀ ≤ z.cutoff ∧ z.cutoff ≤ b₁/2 ∧ 6*b₀ < z.gap

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem sourceHistory_transports_marked_window (hc : Consistent start)
    {mesh : ℝ} (hm : 0 < mesh) (hmesh : mesh ≤ 1/100) (N : ℕ)
    (herror : 4*(N:ℝ)*mesh ≤ Real.log (11/10)) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      (last N h).2 = false → ∀ j : Finset.Iic N, ∀ z : CostState,
      (h j).1.2 = Sum.inl z → ∀ b₀ b₁ : ℝ, 0 < b₀ →
      stateSide z.1 = .even → 209/100 ≤ stateRatio z.1 → stateRatio z.1 ≤ 213/100 →
      10*b₀/(313/100) ≤ currentExponent (Real.log start.gap) z →
      currentExponent (Real.log start.gap) z ≤ b₁/(309/100) →
      ∃ p : History w ell S start, (h j).1.1 = some p ∧ primeWindow b₀ b₁ p.node := by
  filter_upwards [sourceHistory_success_good hw hell hS0 hS hr hs hsS hm N] with h hh
  intro hflag j z hz b₀ b₁ hb₀ heven ht₀ ht₁ hx₀ hx₁
  have hg := hh hflag j
  have he : 4*(j.1:ℝ)*mesh ≤ Real.log (11/10) := by
    have hj : (j.1:ℝ) ≤ N := by exact_mod_cast Finset.mem_Iic.mp j.2
    exact (by nlinarith : 4*(j.1:ℝ)*mesh ≤ 4*(N:ℝ)*mesh).trans herror
  have hg' : GoodAt (Real.log start.gap) mesh j.1 ((h j).1.1,Sum.inl z) := by
    simpa only [← hz] using hg
  cases hp : (h j).1.1 with
  | none =>
    rw [hp] at hg'
    exact False.elim hg'
  | some p =>
    rw [hp] at hg'
    refine ⟨p,rfl,?_⟩
    exact actual_marked_window p z hb₀
      (terminal_gap_positive (by linarith : 0 ≤ ell) hr hs p.admissible)
      (PrimeBinMembership.history_consistent (by linarith : 0 ≤ ell) hr hs hc p)
      hg' heven ht₀ ht₁ hx₀ hx₁ hmesh he

end NumberTheoryLean.SuccessfulMarkedCoordinates

end

end Erdos970

end OAI
