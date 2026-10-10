import OAI.Geometry.IsometricImmersion.Darboux.SixVariableDarboux
import OAI.Geometry.IsometricImmersion.Calculus.QuotientLowBounds

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def stateSegment (w0 w1 : DarbouxState) (sigma : ℝ) : DarbouxState :=
  (1 - sigma) • w0 + sigma • w1

def heightJetSegment (z0 z : Coord → ℝ) (sigma : ℝ) (p : Coord) : DarbouxState :=
  stateSegment (solutionJet z0 p) (solutionJet z p) sigma

theorem statePoint_segment {w0 w1 : DarbouxState}
    (hp : statePoint w0 = statePoint w1) (sigma : ℝ) :
    statePoint (stateSegment w0 w1 sigma) = statePoint w0 := by
  have h0 : w0 0 = w1 0 := congrFun hp 0
  have h1 : w0 1 = w1 1 := congrFun hp 1
  ext i
  fin_cases i <;> simp [statePoint, stateSegment, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, ← h0, ← h1] <;> ring

theorem statePoint_heightJetSegment (z0 z : Coord → ℝ) (sigma : ℝ) (p : Coord) :
    statePoint (heightJetSegment z0 z sigma p) = p := by
  rw [heightJetSegment, statePoint_segment (by simp only [statePoint_solutionJet]),
    statePoint_solutionJet]

theorem stateDenominator_segment (g : MetricField) {w0 w1 : DarbouxState}
    (hp : statePoint w0 = statePoint w1) (sigma : ℝ) :
    stateDenominator g (stateSegment w0 w1 sigma) =
      (1 - sigma) * stateDenominator g w0 + sigma * stateDenominator g w1 := by
  unfold stateDenominator
  rw [statePoint_segment hp, ← hp]
  simp only [jetYY, jetConnection, stateGradient, stateSegment, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

theorem stateMixed_segment (g : MetricField) {w0 w1 : DarbouxState}
    (hp : statePoint w0 = statePoint w1) (sigma : ℝ) :
    stateMixed g (stateSegment w0 w1 sigma) =
      (1 - sigma) * stateMixed g w0 + sigma * stateMixed g w1 := by
  unfold stateMixed
  rw [statePoint_segment hp, ← hp]
  simp only [jetMixed, jetConnection, stateGradient, stateSegment, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

theorem stateDenominator_heightJetSegment (g : MetricField) (z0 z : Coord → ℝ)
    (sigma : ℝ) (p : Coord) :
    stateDenominator g (heightJetSegment z0 z sigma p) =
      (1 - sigma) * covHessian g z0 p 1 1 + sigma * covHessian g z p 1 1 := by
  rw [heightJetSegment, stateDenominator_segment (g := g)
    (by simp only [statePoint_solutionJet]), stateDenominator_solutionJet,
    stateDenominator_solutionJet]

theorem stateDenominator_difference (g : MetricField) {w0 w1 : DarbouxState}
    (hp : statePoint w0 = statePoint w1) :
    stateDenominator g w1 - stateDenominator g w0 =
      (w1 5 - w0 5) - christoffel g 0 1 1 (statePoint w0) * (w1 2 - w0 2) -
        christoffel g 1 1 1 (statePoint w0) * (w1 3 - w0 3) := by
  simp only [stateDenominator, ← hp, jetYY, jetConnection, stateGradient,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem stateMixed_difference (g : MetricField) {w0 w1 : DarbouxState}
    (hp : statePoint w0 = statePoint w1) :
    stateMixed g w1 - stateMixed g w0 =
      (w1 4 - w0 4) - christoffel g 0 0 1 (statePoint w0) * (w1 2 - w0 2) -
        christoffel g 1 0 1 (statePoint w0) * (w1 3 - w0 3) := by
  simp only [stateMixed, ← hp, jetMixed, jetConnection, stateGradient,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem three_term_jet_error {x y z c0 c1 B epsilon : ℝ}
    (hB : 0 ≤ B) (heps : 0 ≤ epsilon)
    (hx : |x| ≤ epsilon) (hy : |y| ≤ epsilon) (hz : |z| ≤ epsilon)
    (h0 : |c0| ≤ B) (h1 : |c1| ≤ B) :
    |x - c0 * y - c1 * z| ≤ (1 + 2 * B) * epsilon := by
  have hy' : |c0 * y| ≤ B * epsilon := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hy (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right h0 heps)
  have hz' : |c1 * z| ≤ B * epsilon := by
    rw [abs_mul]
    exact mul_le_mul h1 hz (abs_nonneg _) hB
  calc
    _ ≤ (|x| + |c0 * y|) + |c1 * z| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ (epsilon + B * epsilon) + B * epsilon := add_le_add (add_le_add hx hy') hz'
    _ = _ := by ring

theorem affine_segment_error {a b epsilon sigma : ℝ}
    (hs : sigma ∈ Icc (0 : ℝ) 1) (heps : 0 ≤ epsilon) (hab : |b - a| ≤ epsilon) :
    |((1 - sigma) * a + sigma * b) - a| ≤ epsilon := by
  have heq : ((1 - sigma) * a + sigma * b) - a = sigma * (b - a) := by ring
  rw [heq, abs_mul, abs_of_nonneg hs.1]
  exact (mul_le_mul_of_nonneg_left hab hs.1).trans
    (mul_le_of_le_one_left heps hs.2)

theorem stateDenominator_segment_error (g : MetricField) {w0 w1 : DarbouxState}
    (hp : statePoint w0 = statePoint w1) {sigma B epsilon : ℝ}
    (hs : sigma ∈ Icc (0 : ℝ) 1) (hB : 0 ≤ B) (heps : 0 ≤ epsilon)
    (hΓ : ∀ r : Fin 2, |christoffel g r 1 1 (statePoint w0)| ≤ B)
    (h2 : |w1 2 - w0 2| ≤ epsilon) (h3 : |w1 3 - w0 3| ≤ epsilon)
    (h5 : |w1 5 - w0 5| ≤ epsilon) :
    |stateDenominator g (stateSegment w0 w1 sigma) - stateDenominator g w0| ≤
      (1 + 2 * B) * epsilon := by
  rw [stateDenominator_segment g hp]
  apply affine_segment_error hs (mul_nonneg (by linarith) heps)
  rw [stateDenominator_difference g hp]
  exact three_term_jet_error hB heps h5 h2 h3 (hΓ 0) (hΓ 1)

theorem stateMixed_segment_error (g : MetricField) {w0 w1 : DarbouxState}
    (hp : statePoint w0 = statePoint w1) {sigma B epsilon : ℝ}
    (hs : sigma ∈ Icc (0 : ℝ) 1) (hB : 0 ≤ B) (heps : 0 ≤ epsilon)
    (hΓ : ∀ r : Fin 2, |christoffel g r 0 1 (statePoint w0)| ≤ B)
    (h2 : |w1 2 - w0 2| ≤ epsilon) (h3 : |w1 3 - w0 3| ≤ epsilon)
    (h4 : |w1 4 - w0 4| ≤ epsilon) :
    |stateMixed g (stateSegment w0 w1 sigma) - stateMixed g w0| ≤
      (1 + 2 * B) * epsilon := by
  rw [stateMixed_segment g hp]
  apply affine_segment_error hs (mul_nonneg (by linarith) heps)
  rw [stateMixed_difference g hp]
  exact three_term_jet_error hB heps h4 h2 h3 (hΓ 0) (hΓ 1)

theorem denominator_lower_of_error {a b nu : ℝ}
    (hnu : nu ≤ |a|) (herr : |b - a| ≤ nu / 2) : nu / 2 ≤ |b| := by
  have htriangle : |a| ≤ |b| + |b - a| := by
    calc
      |a| = |b - (b - a)| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  linarith

theorem heightJetSegment_denominator_lower (g : MetricField) (z0 z : Coord → ℝ)
    (p : Coord) {sigma B epsilon nu : ℝ}
    (hs : sigma ∈ Icc (0 : ℝ) 1) (hB : 0 ≤ B) (heps : 0 ≤ epsilon)
    (hΓ : ∀ r : Fin 2, |christoffel g r 1 1 p| ≤ B)
    (hgrad : ∀ r : Fin 2, |coordPartial r z p - coordPartial r z0 p| ≤ epsilon)
    (hsecond : |coordPartial 1 (coordPartial 1 z) p -
      coordPartial 1 (coordPartial 1 z0) p| ≤ epsilon)
    (hbase : nu ≤ |covHessian g z0 p 1 1|) (hsmall : (1 + 2 * B) * epsilon ≤ nu / 2) :
    nu / 2 ≤ |stateDenominator g (heightJetSegment z0 z sigma p)| := by
  apply denominator_lower_of_error (a := covHessian g z0 p 1 1) hbase
  have herr := stateDenominator_segment_error g
    (w0 := solutionJet z0 p) (w1 := solutionJet z p)
    (by simp only [statePoint_solutionJet]) hs hB heps
    (by simpa only [statePoint_solutionJet] using hΓ) (hgrad 0) (hgrad 1) hsecond
  simpa only [heightJetSegment, stateDenominator_solutionJet] using herr.trans hsmall

theorem heightJetSegment_mem_domain (g : MetricField) (z0 z : Coord → ℝ)
    {U : Set Coord} {p : Coord} (hp : p ∈ U) {sigma nu : ℝ} (hnu : 0 < nu)
    (hden : nu / 2 ≤ |stateDenominator g (heightJetSegment z0 z sigma p)|) :
    heightJetSegment z0 z sigma p ∈ darbouxStateDomain g U := by
  refine ⟨by simpa only [statePoint_heightJetSegment] using hp, ?_⟩
  intro hz
  rw [hz, abs_zero] at hden
  linarith

theorem quotient_difference_bound {b h b0 h0 M epsilon c : ℝ}
    (hc : 0 < c) (hM : 0 ≤ M) (heps : 0 ≤ epsilon)
    (hh : c ≤ |h|) (hh0 : c ≤ |h0|) (hb0 : |b0| ≤ M)
    (hb : |b - b0| ≤ epsilon) (hd : |h - h0| ≤ epsilon) :
    |b / h - b0 / h0| ≤ epsilon / c + M * epsilon / c ^ 2 := by
  have hne : h ≠ 0 := by intro hz; rw [hz, abs_zero] at hh; linarith
  have h0ne : h0 ≠ 0 := by intro hz; rw [hz, abs_zero] at hh0; linarith
  have heq : b / h - b0 / h0 = (b - b0) / h + b0 * (h0 - h) / (h * h0) := by
    field_simp [hne, h0ne]
    ring
  rw [heq]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact LowQuotient.abs_div_bound heps hb hc hh
  · refine LowQuotient.abs_div_bound (mul_nonneg hM heps) ?_ (sq_pos_of_pos hc) ?_
    · rw [abs_mul, abs_sub_comm h0 h]
      exact mul_le_mul hb0 hd (abs_nonneg _) hM
    · rw [abs_mul, pow_two]
      exact mul_le_mul hh hh0 hc.le (abs_nonneg _)

theorem stateSegment_quotient_error (g : MetricField) {w0 w1 : DarbouxState}
    (hp : statePoint w0 = statePoint w1) {sigma B epsilon nu M : ℝ}
    (hs : sigma ∈ Icc (0 : ℝ) 1) (hB : 0 ≤ B) (heps : 0 ≤ epsilon)
    (hnu : 0 < nu) (hM : 0 ≤ M)
    (hΓyy : ∀ r : Fin 2, |christoffel g r 1 1 (statePoint w0)| ≤ B)
    (hΓxy : ∀ r : Fin 2, |christoffel g r 0 1 (statePoint w0)| ≤ B)
    (h2 : |w1 2 - w0 2| ≤ epsilon) (h3 : |w1 3 - w0 3| ≤ epsilon)
    (h4 : |w1 4 - w0 4| ≤ epsilon) (h5 : |w1 5 - w0 5| ≤ epsilon)
    (hbase : nu ≤ |stateDenominator g w0|) (hsmall : (1 + 2 * B) * epsilon ≤ nu / 2)
    (hmix : |stateMixed g w0| ≤ M) :
    |stateMixed g (stateSegment w0 w1 sigma) / stateDenominator g (stateSegment w0 w1 sigma) -
      stateMixed g w0 / stateDenominator g w0| ≤
      ((1 + 2 * B) * epsilon) / (nu / 2) +
        M * ((1 + 2 * B) * epsilon) / (nu / 2) ^ 2 := by
  have hden := stateDenominator_segment_error g hp hs hB heps hΓyy h2 h3 h5
  have hmixerr := stateMixed_segment_error g hp hs hB heps hΓxy h2 h3 h4
  have hlower := denominator_lower_of_error hbase (hden.trans hsmall)
  exact quotient_difference_bound (half_pos hnu) hM
    (mul_nonneg (by linarith) heps) hlower ((by linarith : nu / 2 ≤ nu).trans hbase)
    hmix hmixerr hden

end SmoothLocal.HighEquation

end

end OAI
