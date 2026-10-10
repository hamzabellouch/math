import OAI.Probability.SwitchChain.PairFiberBridge

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

namespace Problem315.PairResampling

variable {n : Nat} {d : Fin n → Nat}

theorem sum_expectation (a : Finset (Fin n)) (f : StateSpace n d) :
    (∑ G, expectation n d a f G) = ∑ G, f G := by
  let one : StateSpace n d := WithLp.toLp 2 (fun _ => 1)
  have hone : expectation n d a one = one :=
    (expectation_eq_self_iff a one).mpr (constant_mem a 1)
  have h := expectation_isSymmetric a f one
  change inner ℝ (expectation n d a f) one = inner ℝ f (expectation n d a one) at h
  rw [hone, state_inner, state_inner] at h
  simpa [one] using h

theorem sum_fiber_average (a : Finset (Fin n)) (g : GraphState n d → ℝ) :
    (∑ G, (∑ H ∈ fiberStates a G, g H) / (fiberStates a G).card) = ∑ G, g G := by
  let f : StateSpace n d := WithLp.toLp 2 g
  have h := sum_expectation a f
  simpa only [expectation_eq_average, f] using h

theorem inner_fluctuation_eq_sum_fiber_variance (a : Finset (Fin n))
    (f : StateSpace n d) :
    inner ℝ f (fluctuation n d a f) =
      ∑ G, (∑ H ∈ fiberStates a G,
        (f H - expectation n d a f G) ^ 2) / (fiberStates a G).card := by
  have heq : ∀ G H, H ∈ fiberStates a G →
      expectation n d a f H = expectation n d a f G := by
    intro G H hH
    exact (expectation_mem a f) H G ((mem_fiberStates a G H).mp hH).symm
  calc
    inner ℝ f (fluctuation n d a f) =
        inner ℝ (fluctuation n d a f) (fluctuation n d a f) := by
      rw [inner_fluctuation, real_inner_self_eq_norm_sq]
    _ = ∑ G, (f G - expectation n d a f G) ^ 2 := by
      rw [state_inner, fluctuation_eq_sub]
      apply Finset.sum_congr rfl
      intro G hG
      change (f G - expectation n d a f G) * (f G - expectation n d a f G) = _
      ring
    _ = ∑ G, (∑ H ∈ fiberStates a G,
        (f H - expectation n d a f H) ^ 2) / (fiberStates a G).card :=
      (sum_fiber_average a (fun H => (f H - expectation n d a f H) ^ 2)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro G hG
      congr 1
      apply Finset.sum_congr rfl
      intro H hH
      rw [heq G H hH]

theorem inner_fluctuation_le_of_fiber_variance_bound
    (a : Finset (Fin n)) (f : StateSpace n d) (e : GraphState n d → ℝ) (C : ℝ)
    (hlocal : ∀ G : GraphState n d,
      (∑ H ∈ fiberStates a G, (f H - expectation n d a f G) ^ 2) /
          (fiberStates a G).card ≤
        C * ((∑ H ∈ fiberStates a G, e H) / (fiberStates a G).card)) :
    inner ℝ f (fluctuation n d a f) ≤ C * ∑ G, e G := by
  rw [inner_fluctuation_eq_sum_fiber_variance]
  calc
    _ ≤ ∑ G, C * ((∑ H ∈ fiberStates a G, e H) / (fiberStates a G).card) :=
      Finset.sum_le_sum (fun G _ => hlocal G)
    _ = _ := by rw [← Finset.mul_sum, sum_fiber_average]

end Problem315.PairResampling

namespace Problem315.PairFiber

variable {n : Nat} {d : Fin n → Nat}

theorem assignment_average_eq_fiber_average
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) (g : GraphState n d → ℝ) :
    (∑ T : Assignment G.val i j, g ((stateFiberEquiv G i j hij).symm T).val) /
        (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ) =
      (∑ H ∈ PairResampling.fiberStates {i, j} G, g H) /
        (PairResampling.fiberStates {i, j} G).card := by
  let f : PairResampling.StateSpace n d := WithLp.toLp 2 g
  have h := expectation_eq_assignment_average G i j hij f
  rw [PairResampling.expectation_eq_average] at h
  exact h.symm

theorem inner_fluctuation_le_of_assignment_variance_bound
    (i j : Fin n) (hij : i ≠ j) (f : PairResampling.StateSpace n d)
    (e : GraphState n d → ℝ) (C : ℝ)
    (hlocal : ∀ G : GraphState n d,
      (∑ T : Assignment G.val i j,
        (f ((stateFiberEquiv G i j hij).symm T).val -
          PairResampling.expectation n d {i, j} f G) ^ 2) /
          (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ) ≤
        C * ((∑ T : Assignment G.val i j, e ((stateFiberEquiv G i j hij).symm T).val) /
          (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ))) :
    inner ℝ f (PairResampling.fluctuation n d {i, j} f) ≤ C * ∑ G, e G := by
  apply PairResampling.inner_fluctuation_le_of_fiber_variance_bound {i, j} f e C
  intro G
  rw [← assignment_average_eq_fiber_average G i j hij
      (fun H => (f H - PairResampling.expectation n d {i, j} f G) ^ 2),
    ← assignment_average_eq_fiber_average G i j hij e]
  exact hlocal G

theorem inner_fluctuation_le_of_assignment_sum_bound
    (i j : Fin n) (hij : i ≠ j) (f : PairResampling.StateSpace n d)
    (e : GraphState n d → ℝ) (C : ℝ)
    (hlocal : ∀ G : GraphState n d,
      (∑ T : Assignment G.val i j,
        (f ((stateFiberEquiv G i j hij).symm T).val -
          PairResampling.expectation n d {i, j} f G) ^ 2) ≤
        C * (∑ T : Assignment G.val i j, e ((stateFiberEquiv G i j hij).symm T).val)) :
    inner ℝ f (PairResampling.fluctuation n d {i, j} f) ≤ C * ∑ G, e G := by
  apply inner_fluctuation_le_of_assignment_variance_bound i j hij f e C
  intro G
  simpa only [mul_div_assoc] using
    div_le_div_of_nonneg_right (hlocal G)
      (show (0 : ℝ) ≤ Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card by
        positivity)

end Problem315.PairFiber

end

end OAI
