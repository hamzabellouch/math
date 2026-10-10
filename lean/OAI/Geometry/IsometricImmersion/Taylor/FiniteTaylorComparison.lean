import OAI.Geometry.IsometricImmersion.Taylor.TaylorResidual
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix BigOperators

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

def linearCauchy (a : ℝ) (u0 u1 : ℝ → ℝ) (p : Coord) : ℝ :=
  u0 (p 0) + u1 (p 0) * (p 1 - a)

theorem linearCauchy_contDiffOn {u0 u1 : ℝ → ℝ} {I : Set ℝ}
    (h0 : ContDiffOn ℝ ∞ u0 I) (h1 : ContDiffOn ℝ ∞ u1 I) (a : ℝ) :
    ContDiffOn ℝ ∞ (linearCauchy a u0 u1) (spatialStrip I) :=
  (h0.comp (contDiffOn_apply ℝ ℝ 0 (spatialStrip I)) (fun _ hp => hp)).add
    ((h1.comp (contDiffOn_apply ℝ ℝ 0 (spatialStrip I)) (fun _ hp => hp)).mul
      ((contDiffOn_apply ℝ ℝ 1 (spatialStrip I)).sub contDiffOn_const))

theorem linearCauchy_value (a x : ℝ) (u0 u1 : ℝ → ℝ) :
    linearCauchy a u0 u1 ![x, a] = u0 x := by simp [linearCauchy]

theorem linearCauchy_velocity {u0 u1 : ℝ → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (h0 : ContDiffOn ℝ ∞ u0 I) (h1 : ContDiffOn ℝ ∞ u1 I)
    (a : ℝ) {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 1 (linearCauchy a u0 u1) p = u1 (p 0) := by
  have hlin := linearCauchy_contDiffOn h0 h1 a
  have hd : HasFDerivAt (linearCauchy a u0 u1)
      (fderiv ℝ (linearCauchy a u0 u1) p) (![p 0, p 1] : Coord) := by
    simpa only [point_eta] using
      ((hlin.contDiffAt ((spatialStrip_isOpen hI).mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hc := hd.comp_hasDerivAt (p 1) (verticalPoint_hasDerivAt (p 0) (p 1))
  have he : (fun t => linearCauchy a u0 u1 ![p 0, t]) =
      (fun t => u0 (p 0) + u1 (p 0) * (t - a)) := rfl
  change HasDerivAt (fun t => linearCauchy a u0 u1 ![p 0, t])
    (coordPartial 1 (linearCauchy a u0 u1) p) (p 1) at hc
  rw [he] at hc
  have hf := ((hasDerivAt_id (p 1)).sub_const a).const_mul (u1 (p 0))
  have hf' := hf.const_add (u0 (p 0))
  simpa only [mul_one] using hc.unique hf'

def taylorApproximation (g : MetricField) (a : ℝ) (u0 u1 : ℝ → ℝ) : ℕ → Coord → ℝ
  | 0 => linearCauchy a u0 u1
  | n + 1 => fun p => taylorApproximation g a u0 u1 n p +
      taylorCorrection (nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n) a n p

theorem taylorApproximation_value (g : MetricField) (a x : ℝ) (u0 u1 : ℝ → ℝ) (N : ℕ) :
    taylorApproximation g a u0 u1 N ![x, a] = u0 x := by
  induction N with
  | zero => exact linearCauchy_value a x u0 u1
  | succ n hn =>
    simp only [taylorApproximation, hn, taylorCorrection, separatedProduct,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    simp [normalizedTimePower]

def comparisonTimePolynomial (g : MetricField) (a : ℝ) (u0 u1 : ℝ → ℝ)
    (x : ℝ) : ℕ → Polynomial ℝ
  | 0 => Polynomial.C (u0 x) + Polynomial.C (u1 x) * (Polynomial.X - Polynomial.C a)
  | n + 1 => comparisonTimePolynomial g a u0 u1 x n +
      Polynomial.C (nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n x /
        ((n + 2).factorial : ℝ)) * (Polynomial.X - Polynomial.C a)^(n + 2)

theorem comparisonTimePolynomial_eval (g : MetricField) (a : ℝ) (u0 u1 : ℝ → ℝ)
    (x t : ℝ) (N : ℕ) :
    (comparisonTimePolynomial g a u0 u1 x N).eval t =
      taylorApproximation g a u0 u1 N ![x, t] := by
  induction N with
  | zero => simp [comparisonTimePolynomial, taylorApproximation, linearCauchy]
  | succ n hn =>
    simp only [comparisonTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      hn, taylorApproximation, taylorCorrection, separatedProduct,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, normalizedTimePower]
    ring

theorem comparisonTimePolynomial_natDegree (g : MetricField) (a : ℝ) (u0 u1 : ℝ → ℝ)
    (x : ℝ) (N : ℕ) :
    (comparisonTimePolynomial g a u0 u1 x N).natDegree ≤ N + 1 := by
  induction N with
  | zero =>
    unfold comparisonTimePolynomial
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · simp
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_sub_C_le a)
  | succ n hn =>
    change (comparisonTimePolynomial g a u0 u1 x n + _).natDegree ≤ n + 1 + 1
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact hn.trans (by omega)
    · apply (Polynomial.natDegree_C_mul_le _ _).trans
      have hp : ((Polynomial.X - Polynomial.C a : Polynomial ℝ)^(n + 2)).natDegree ≤ n + 2 := by
        simpa only [mul_one] using
          (Polynomial.natDegree_pow_le_of_le (n + 2) (Polynomial.natDegree_X_sub_C_le a))
      exact hp.trans (by omega)

theorem taylorApproximation_properties {g : MetricField} {U : Set Coord}
    {u0 u1 : ℝ → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (h0 : ContDiffOn ℝ ∞ u0 I) (h1 : ContDiffOn ℝ ∞ u1 I)
    (a : ℝ) (hcut : ∀ x ∈ I, (![x, a] : Coord) ∈ U)
    (hxx : ∀ x ∈ I, covHessian g (linearCauchy a u0 u1) ![x, a] 0 0 ≠ 0) :
    ∀ N,
      ContDiffOn ℝ ∞ (taylorApproximation g a u0 u1 N) (spatialStrip I) ∧
      (∀ x ∈ I, qSolutionJet (taylorApproximation g a u0 u1 N) ![x, a] =
        qSolutionJet (linearCauchy a u0 u1) ![x, a]) ∧
      (∀ x ∈ I, ∀ k < N,
        iteratedDeriv k (fun t => qResidual g (taylorApproximation g a u0 u1 N) ![x, t]) a = 0) := by
  intro N
  induction N with
  | zero =>
    refine ⟨linearCauchy_contDiffOn h0 h1 a, fun _ _ => rfl, ?_⟩
    intro _ _ k hk
    omega
  | succ n hn =>
    have hxxn : ∀ x ∈ I,
        covHessian g (taylorApproximation g a u0 u1 n) ![x, a] 0 0 ≠ 0 := by
      intro x hx
      rw [← stateQDenominator_qSolutionJet, hn.2.1 x hx, stateQDenominator_qSolutionJet]
      exact hxx x hx
    have hC := nextTaylorCoefficient_contDiffOn hg hU hI hn.1 a n hcut hxxn
    refine ⟨hn.1.add (taylorCorrection_contDiffOn hC a n), ?_, ?_⟩
    · intro x hx
      have hj := qSolutionJet_taylorCorrection_time_jets hI hn.1 hC a n hx 0 (Nat.zero_le n)
      change qSolutionJet (fun p => taylorApproximation g a u0 u1 n p +
        taylorCorrection (nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n) a n p)
        ![x, a] = _
      have hj0 : qSolutionJet (fun p => taylorApproximation g a u0 u1 n p +
          taylorCorrection (nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n) a n p)
          ![x, a] = qSolutionJet (taylorApproximation g a u0 u1 n) ![x, a] := by
        simpa only [iteratedDeriv_zero] using hj
      exact hj0.trans (hn.2.1 x hx)
    · exact nextTaylorCoefficient_cancels hg hU hI hn.1 a n hcut hxxn hn.2.2

theorem finiteTaylorComparison {g : MetricField} {U : Set Coord}
    {u0 u1 : ℝ → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (h0 : ContDiffOn ℝ ∞ u0 I) (h1 : ContDiffOn ℝ ∞ u1 I)
    (a : ℝ) (hcut : ∀ x ∈ I, (![x, a] : Coord) ∈ U)
    (hxx : ∀ x ∈ I, covHessian g (linearCauchy a u0 u1) ![x, a] 0 0 ≠ 0) (N : ℕ) :
    let z0 := taylorApproximation g a u0 u1 N
    ContDiffOn ℝ ∞ z0 (spatialStrip I) ∧
    (∀ x ∈ I, z0 ![x, a] = u0 x ∧ coordPartial 1 z0 ![x, a] = u1 x) ∧
    (∀ x, ∃ p : Polynomial ℝ, p.natDegree ≤ N + 1 ∧
      ∀ t, p.eval t = z0 ![x, t]) ∧
    (∃ V : Set Coord, IsOpen V ∧ V ⊆ U ∩ spatialStrip I ∧
      (∀ x ∈ I, (![x, a] : Coord) ∈ V) ∧
      (∀ p ∈ V, covHessian g z0 p 0 0 ≠ 0) ∧
      ContDiffOn ℝ ∞ (qResidual g z0) V) ∧
    (∀ x ∈ I, ∀ k < N, iteratedDeriv k (fun t => qResidual g z0 ![x, t]) a = 0) := by
  dsimp only
  obtain ⟨hP, hjet, hzero⟩ := taylorApproximation_properties hg hU hI h0 h1 a hcut hxx N
  have hxxN : ∀ x ∈ I,
      covHessian g (taylorApproximation g a u0 u1 N) ![x, a] 0 0 ≠ 0 := by
    intro x hx
    rw [← stateQDenominator_qSolutionJet, hjet x hx, stateQDenominator_qSolutionJet]
    exact hxx x hx
  refine ⟨hP, ?_, ?_, ?_, hzero⟩
  · intro x hx
    refine ⟨taylorApproximation_value g a x u0 u1 N, ?_⟩
    have hv := congrArg (fun w : DarbouxState => w 3) (hjet x hx)
    change coordPartial 1 (taylorApproximation g a u0 u1 N) ![x, a] =
      coordPartial 1 (linearCauchy a u0 u1) ![x, a] at hv
    exact hv.trans (linearCauchy_velocity hI h0 h1 a hx)
  · intro x
    exact ⟨comparisonTimePolynomial g a u0 u1 x N,
      comparisonTimePolynomial_natDegree g a u0 u1 x N,
      fun t => comparisonTimePolynomial_eval g a u0 u1 x t N⟩
  · refine ⟨comparisonDomain g U (taylorApproximation g a u0 u1 N) I,
      comparisonDomain_isOpen hg hU hI hP, ?_, ?_, ?_, qResidual_contDiffOn hg hU hI hP⟩
    · intro p hp
      exact ⟨(comparisonDomain_denominator hp).1, hp.1⟩
    · intro x hx
      exact mem_comparisonDomain hx (hcut x hx) (hxxN x hx)
    · intro p hp
      exact (comparisonDomain_denominator hp).2

end SmoothLocal.Taylor

end

end OAI
