import OAI.NumberTheory.Jacobsthal.Estimates.SuccessfulRewardComparison

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CompactTestGeometry

open _root_.Set _root_.MeasureTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualFlagInvariant RegeneratingInverseBands

variable {w ell S : ℝ} {start : Node}

noncomputable def primeTest (F : Side → ℝ×ℝ → ℝ) : ChainState w ell S start → ℝ
  | none => 0
  | some h => F h.node.side (h.node.gap,h.node.ratio)

noncomputable def continuousTest (v : ℝ) (F : Side → ℝ×ℝ → ℝ) : CemeteryKernel.Space CostState → ℝ
  | .inr _ => 0
  | .inl z => F (stateSide z.1) (gapValue v z,stateRatio z.1)

theorem phase_uniform_modulus (F : Side → ℝ×ℝ → ℝ) (hF : ∀ i,UniformContinuous (F i))
    {η : ℝ} (hη : 0 < η) : ∃ δ : ℝ,0 < δ ∧ ∀ i : Side,∀ x y : ℝ×ℝ,
      |x.1-y.1| ≤ δ → |x.2-y.2| ≤ δ → |F i x-F i y| ≤ η := by
  obtain ⟨de,hde,he⟩ := Metric.uniformContinuous_iff_le.mp (hF .even) η hη
  obtain ⟨do_,hdo,ho⟩ := Metric.uniformContinuous_iff_le.mp (hF .odd) η hη
  refine ⟨min de do_,lt_min hde hdo,?_⟩
  intro i x y hx hy
  have hdist : dist x y ≤ min de do_ := by rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]; exact max_le hx hy
  cases i with
  | even => simpa only [Real.dist_eq] using he (hdist.trans (min_le_left _ _))
  | odd => simpa only [Real.dist_eq] using ho (hdist.trans (min_le_right _ _))

theorem compact_gap_close {K r q d : ℝ} (_hK : 0 ≤ K) (hr : 0 < r) (hq : 0 < q)
    (hd : |Real.log r-Real.log q| ≤ d) (hd1 : d ≤ 1) (hcompact : r ≤ K ∨ q ≤ K) :
    r ≤ 3*K ∧ q ≤ 3*K ∧ |r-q| ≤ 3*K*(Real.exp d-1) := by
  have hrel := NearbyParentGeometry.log_gap_relative hr hq hd
  have he3 : Real.exp d ≤ 3 := (Real.exp_le_exp.mpr hd1).trans Real.exp_one_lt_three.le
  have hd0 : 0 ≤ d := (abs_nonneg _).trans hd
  have he0 : 0 ≤ Real.exp d-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hd0)
  have hrq : r ≤ 3*q := hrel.1.trans (mul_le_mul_of_nonneg_right he3 hq.le)
  have hqr : q ≤ 3*r := hrel.2.trans (mul_le_mul_of_nonneg_right he3 hr.le)
  have hboth : r ≤ 3*K ∧ q ≤ 3*K := by rcases hcompact with h | h <;> constructor <;> linarith
  refine ⟨hboth.1,hboth.2,abs_le.mpr ⟨?_,?_⟩⟩
  · have hh := mul_le_mul_of_nonneg_right hboth.1 he0
    nlinarith
  · have hh := mul_le_mul_of_nonneg_right hboth.2 he0
    nlinarith

theorem actual_compact_test_comparison (F : Side → ℝ×ℝ → ℝ)
    (hF : ∀ i,UniformContinuous (F i)) {K η : ℝ} (hK : 0 ≤ K) (hη : 0 < η)
    (hsupport : ∀ i : Side,∀ r s : ℝ,K < r → F i (r,s) = 0) :
    ∃ δ : ℝ,0 < δ ∧ ∀ w ell S : ℝ,∀ start : Node,
      0 ≤ ell → 0 < start.gap → Valid start.side start.ratio →
      ∀ v mesh : ℝ,∀ n : ℕ,mesh ≤ δ → 4*(n:ℝ)*mesh ≤ 1 →
        3*K*(Real.exp (4*(n:ℝ)*mesh)-1) ≤ δ →
        ∀ q : JointState w ell S start,GoodAt v mesh n q →
          |primeTest F q.1-continuousTest v F q.2| ≤ η*PrimeCompactVisits.visit (3*K) q.1 := by
  obtain ⟨δ,hδ,hmod⟩ := phase_uniform_modulus F hF hη
  refine ⟨δ,hδ,?_⟩
  intro w ell S start hell hr hs v mesh n hm hd hgap q hgood
  rcases q with ⟨p,y⟩
  cases p with
  | none =>
    cases y with
    | inr u => simp [primeTest,continuousTest,PrimeCompactVisits.visit]
    | inl z => exact False.elim hgood
  | some h =>
    cases y with
    | inr u => exact False.elim hgood
    | inl z =>
      have hh : liveGood v mesh n h z := hgood
      have hr' : 0 < h.node.gap := terminal_gap_positive hell hr hs h.admissible
      have hq' : 0 < gapValue v z := Real.exp_pos _
      by_cases hz : F h.node.side (h.node.gap,h.node.ratio) = 0 ∧
          F (stateSide z.1) (gapValue v z,stateRatio z.1) = 0
      · simp only [primeTest,continuousTest,hz.1,hz.2,sub_zero,abs_zero]
        exact mul_nonneg hη.le (PrimeCompactVisits.visit_nonneg _ _)
      · have hcomp : h.node.gap ≤ K ∨ gapValue v z ≤ K := by
          by_contra hn
          push Not at hn
          exact hz ⟨hsupport _ _ _ hn.1,hsupport _ _ _ hn.2⟩
        have hclose := compact_gap_close hK hr' hq' hh.2.2.2 hd hcomp
        have hvalue := hmod h.node.side (h.node.gap,h.node.ratio) (gapValue v z,stateRatio z.1)
          (hclose.2.2.trans hgap) (hh.2.2.1.trans hm)
        simp only [primeTest,continuousTest,PrimeCompactVisits.visit,ite_eq_left hclose.1,mul_one]
        simpa only [hh.2.1] using hvalue

end NumberTheoryLean.CompactTestGeometry

end

end Erdos970

end OAI
