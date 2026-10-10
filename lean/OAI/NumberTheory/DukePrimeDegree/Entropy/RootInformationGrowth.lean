import OAI.NumberTheory.DukePrimeDegree.Geometry.RootLeafLowerBound
import OAI.NumberTheory.DukePrimeDegree.Dynamics.HopfMeanBound

namespace OAI

/-!
# Linear growth of actual root information

Small-ball differentiation bounds the information along integer scales.
The actual scaling cocycle identifies these scales with Birkhoff sums.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
  (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
  (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

include hA

/-- The information at integer time is the corresponding finite orbit sum. -/
lemma ae_rootInformation_nat_sum (n : ℕ) :
    ∀ᵐ x ∂μ, rootInformation hij μ n x =
      birkhoffSum (fun y => rightAction y (rootCanonicalFlow d j 1))
        (rootInformation hij μ 1) n x := by
  induction n with
  | zero =>
    have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
        rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
      (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
    filter_upwards [ae_intrinsicRootLeaf_spec hij μ hfree] with x hx
    simp [rootInformation, hx.2]
  | succ n ih =>
    have hT := rootCanonicalFlow_preserving d j 1 μ hA
    have him : ∀ᵐ y ∂μ.map (fun y => rightAction y (rootCanonicalFlow d j 1)),
        rootInformation hij μ n y =
          birkhoffSum (fun y => rightAction y (rootCanonicalFlow d j 1))
            (rootInformation hij μ 1) n y := by
      rw [hT.map_eq]
      exact ih
    have hip := ae_of_ae_map hT.measurable.aemeasurable him
    filter_upwards [hip, ae_rootInformation_cocycle d hij μ hA n 1] with x hi hc
    simpa only [Nat.cast_succ, hi, birkhoffSum_succ_apply'] using hc

/-- Root information grows at most linearly, with slope one and a
point-dependent additive constant. -/
lemma ae_rootInformation_linear_bound :
    ∀ᵐ x ∂μ, ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      rootInformation hij μ n x ≤ n + B := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  filter_upwards [ae_intrinsicRootLeaf_discrete_lower_bound hij μ hfree,
    ae_intrinsicRootLeaf_spec hij μ hfree,
    ae_intrinsicRootLeaf_ball_pos hij μ hfree] with x hx hs hp
  let ν := intrinsicRootLeaf hij μ x
  let : IsLocallyFiniteMeasure ν := hs.1
  obtain ⟨C, N, hCN⟩ := hx
  refine ⟨Real.log (C + 1 : ℝ), N, ?_⟩
  intro n hn
  have hr := Real.exp_pos (-(n : ℝ))
  have hm : 0 < ν (ball 0 (Real.exp (-(n : ℝ)))) := hp _ hr
  have hfin : ν (ball 0 (Real.exp (-(n : ℝ)))) ≠ ∞ := measure_ball_lt_top.ne
  have hbig : ENNReal.ofReal (Real.exp (-(n : ℝ))) ≤
      ((C + 1 : ℕ) : ℝ≥0∞) * ν (ball 0 (Real.exp (-(n : ℝ)))) :=
    (hCN n hn).trans (mul_le_mul_left (by exact_mod_cast Nat.le_succ C) _)
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp) hfin) hbig
  rw [ENNReal.toReal_ofReal hr.le, ENNReal.toReal_mul, ENNReal.toReal_natCast] at hreal
  simp only [Nat.cast_add, Nat.cast_one] at hreal
  have hmreal : 0 < (ν (ball 0 (Real.exp (-(n : ℝ))))).toReal :=
    ENNReal.toReal_pos hm.ne' hfin
  have hlog := Real.log_le_log hr hreal
  rw [Real.log_exp, Real.log_mul (by positivity) hmreal.ne'] at hlog
  change -Real.log (ν (ball 0 (Real.exp (-(n : ℝ))))).toReal ≤ _
  linarith

end DukePrimeDegree

end

end OAI
