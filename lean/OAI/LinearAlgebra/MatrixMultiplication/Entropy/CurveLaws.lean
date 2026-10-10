import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexWitness
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.CurveLaws

open MatrixMultiplication.Foundation ComplexWitness

theorem fiberSize_real_pos (u : CurveCoordinate) : (0 : ℝ) < curveFiberSize u := by
  exact_mod_cast curveFiberSize_pos u

def uniformLift (p : FiniteLaw CurveCoordinate) : FiniteLaw CurveLeaf where
  mass s := p.mass (CW75LabelHierarchy.x s) / curveFiberSize (CW75LabelHierarchy.x s)
  nonneg s := div_nonneg (p.nonneg _) (fiberSize_real_pos _).le
  total := by
    rw [sum_curveLeaves_by_X (fun u => p.mass u / (curveFiberSize u : ℝ))]
    simpa only [mul_div_cancel₀ _ (fiberSize_real_pos _).ne'] using p.total

theorem uniformLift_marginal (p : FiniteLaw CurveCoordinate) (u : CurveCoordinate) :
    ((uniformLift p).map CW75LabelHierarchy.x).mass u = p.mass u := by
  classical
  rw [FiniteLaw.map_mass]
  change (∑ s : CurveLeaf,
    if CW75LabelHierarchy.x s = u then
      p.mass (CW75LabelHierarchy.x s) / curveFiberSize (CW75LabelHierarchy.x s)
    else 0) = p.mass u
  rw [sum_curveLeaves_by_X
    (fun v => if v = u then p.mass v / (curveFiberSize v : ℝ) else 0)]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact mul_div_cancel₀ (p.mass u) (fiberSize_real_pos u).ne'

theorem entropyTerm_div_fiber (p : ℝ) {d : ℝ} (hd : 0 < d) :
    d * entropyTerm (p / d) = entropyTerm p + p * Real.log d := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [entropyTerm, Real.log_div hp hd.ne', entropyTerm]
    field_simp [hd.ne']
    ring

theorem uniformLift_entropy (p : FiniteLaw CurveCoordinate) :
    finiteEntropy (uniformLift p).mass = finiteEntropy p.mass +
      ∑ u : CurveCoordinate, p.mass u * Real.log (curveFiberSize u) := by
  change (∑ s : CurveLeaf,
    entropyTerm (p.mass (CW75LabelHierarchy.x s) /
      curveFiberSize (CW75LabelHierarchy.x s))) = _
  rw [sum_curveLeaves_by_X
    (fun u => entropyTerm (p.mass u / (curveFiberSize u : ℝ)))]
  simp_rw [entropyTerm_div_fiber _ (fiberSize_real_pos _)]
  simp only [finiteEntropy, Finset.sum_add_distrib]

def partition (t : ℝ) : ℝ :=
  ∑ u : CurveCoordinate, (curveFiberSize u : ℝ) ^ t

theorem partition_pos (t : ℝ) : 0 < partition t := by
  apply Finset.sum_pos
  · intro u _
    exact Real.rpow_pos_of_pos (fiberSize_real_pos u) t
  · exact Finset.univ_nonempty

theorem partition_closed (t : ℝ) :
    partition t = 8 + 12 * (2 : ℝ) ^ t + 6 * (4 : ℝ) ^ t + (19 : ℝ) ^ t := by
  rw [partition, sum_curveFiberSizes (fun d => (d : ℝ) ^ t)]
  simp

def marginal (t : ℝ) : FiniteLaw CurveCoordinate where
  mass u := (curveFiberSize u : ℝ) ^ t / partition t
  nonneg u := div_nonneg (Real.rpow_pos_of_pos (fiberSize_real_pos u) t).le
    (partition_pos t).le
  total := by
    rw [← Finset.sum_div]
    exact div_self (partition_pos t).ne'

theorem marginal_pos (t : ℝ) (u : CurveCoordinate) : 0 < (marginal t).mass u :=
  div_pos (Real.rpow_pos_of_pos (fiberSize_real_pos u) t) (partition_pos t)

theorem marginal_lt_one (t : ℝ) (u : CurveCoordinate) : (marginal t).mass u < 1 := by
  classical
  obtain ⟨v, hv⟩ := exists_ne u
  calc
    (marginal t).mass u < ∑ w : CurveCoordinate, (marginal t).mass w :=
      Finset.single_lt_sum hv (Finset.mem_univ u) (Finset.mem_univ v)
        (marginal_pos t v) (fun w _ _ => (marginal t).nonneg w)
    _ = 1 := (marginal t).total

def leafLaw (t : ℝ) : FiniteLaw CurveLeaf := uniformLift (marginal t)

theorem leafLaw_pos (t : ℝ) (s : CurveLeaf) : 0 < (leafLaw t).mass s :=
  div_pos (marginal_pos t _) (fiberSize_real_pos _)

theorem marginal_of_leafLaw (t : ℝ) :
    ((leafLaw t).map CW75LabelHierarchy.x).mass = (marginal t).mass := by
  funext u
  exact uniformLift_marginal (marginal t) u

theorem leafLaw_uniform_in_fibers (t : ℝ) (s r : CurveLeaf)
    (h : CW75LabelHierarchy.x s = CW75LabelHierarchy.x r) :
    (leafLaw t).mass s = (leafLaw t).mass r := by
  change (marginal t).mass _ / _ = (marginal t).mass _ / _
  rw [h]

def hidden (t : ℝ) : ℝ :=
  ∑ u : CurveCoordinate, (marginal t).mass u * Real.log (curveFiberSize u)

def incident (t : ℝ) : ℝ := Real.log (partition t) - t * hidden t

theorem log_marginal (t : ℝ) (u : CurveCoordinate) :
    Real.log ((marginal t).mass u) =
      t * Real.log (curveFiberSize u) - Real.log (partition t) := by
  change Real.log ((curveFiberSize u : ℝ) ^ t / partition t) = _
  rw [Real.log_div (Real.rpow_pos_of_pos (fiberSize_real_pos u) t).ne'
    (partition_pos t).ne', Real.log_rpow (fiberSize_real_pos u)]

theorem incident_entropy (t : ℝ) : finiteEntropy (marginal t).mass = incident t := by
  unfold finiteEntropy
  simp_rw [entropyTerm, log_marginal]
  calc
    (∑ u : CurveCoordinate,
      -(marginal t).mass u *
        (t * Real.log (curveFiberSize u) - Real.log (partition t))) =
      (∑ u : CurveCoordinate, (marginal t).mass u) * Real.log (partition t) -
        t * ∑ u : CurveCoordinate,
          (marginal t).mass u * Real.log (curveFiberSize u) := by
      simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = incident t := by rw [(marginal t).total]; simp [incident, hidden]

theorem incident_pos (t : ℝ) : 0 < incident t := by
  rw [← incident_entropy]
  apply Finset.sum_pos
  · intro u _
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos (marginal_pos t u))
      (Real.log_neg (marginal_pos t u) (marginal_lt_one t u))
  · exact Finset.univ_nonempty

theorem hidden_nonneg (t : ℝ) : 0 ≤ hidden t := by
  apply Finset.sum_nonneg
  intro u _
  have hd : (1 : ℝ) ≤ curveFiberSize u := by
    exact_mod_cast (curveFiberSize_pos u : 1 ≤ curveFiberSize u)
  exact mul_nonneg ((marginal t).nonneg u) (Real.log_nonneg hd)

theorem leaf_entropy (t : ℝ) :
    finiteEntropy (leafLaw t).mass = incident t + hidden t := by
  rw [leafLaw, uniformLift_entropy, incident_entropy]
  rfl

theorem conditional_entropy (t : ℝ) :
    finiteEntropy (leafLaw t).mass -
      finiteEntropy ((leafLaw t).map CW75LabelHierarchy.x).mass = hidden t := by
  rw [marginal_of_leafLaw, leaf_entropy, incident_entropy]
  ring

theorem hidden_closed (t : ℝ) :
    hidden t =
      (12 * (2 : ℝ) ^ t * Real.log 2 + 6 * (4 : ℝ) ^ t * Real.log 4 +
        (19 : ℝ) ^ t * Real.log 19) / partition t := by
  unfold hidden
  change (∑ u : CurveCoordinate,
    ((curveFiberSize u : ℝ) ^ t / partition t) * Real.log (curveFiberSize u)) = _
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, sum_curveFiberSizes (fun d => (d : ℝ) ^ t * Real.log d)]
  simp
  ring

theorem incident_rate (t : ℝ) :
    ConditionalLabels.lawPairingRate (leafLaw t) curveLabels 5 curveReaderPair .xy +
      ConditionalLabels.lawPairingRate (leafLaw t) curveLabels 5 curveReaderPair .xz =
        incident t := by
  rw [curveIncidentRate_eq_entropy_X, marginal_of_leafLaw, incident_entropy]

theorem hidden_rate (t : ℝ) :
    ConditionalLabels.lawPairingRate (leafLaw t) curveLabels 5 curveReaderPair .yz =
      hidden t := by
  rw [curveHiddenRate_eq_entropy_sub_X]
  exact conditional_entropy t

end MatrixMultiplication.CurveLaws

end

end OAI
