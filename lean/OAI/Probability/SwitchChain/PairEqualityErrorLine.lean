import OAI.Probability.SwitchChain.PairFiberBridge

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairEqualityErrorLine

attribute [local instance] Classical.propDecidable
open PairFiber PairResampling

variable {n : Nat} {d : Fin n → Nat}

def crossTotal (G : SimpleGraph (Fin n)) (i j k l : Fin n) : Nat :=
  edgeBit G i k + edgeBit G i l + edgeBit G j k + edgeBit G j l

def rowExtreme (G : SimpleGraph (Fin n)) (i j k l : Fin n) : ℝ :=
  if crossTotal G i j k l = 2 ∧ edgeBit G i k + edgeBit G i l ≠ 1 then 1 else 0

def equalityIndicator (G : SimpleGraph (Fin n)) (i k l : Fin n) : ℝ :=
  if (G.Adj i k ↔ G.Adj i l) then 1 else 0

theorem rowExtreme_eq_gated_equality (G : SimpleGraph (Fin n))
    (i j k l : Fin n) (hk : Outside i j k) (hl : Outside i j l) :
    rowExtreme G i j k l =
      if k ∈ singletonSet G i j ∧ l ∈ singletonSet G i j then
        equalityIndicator G i k l else 0 := by
  by_cases hik : G.Adj i k <;> by_cases hil : G.Adj i l <;>
    by_cases hjk : G.Adj j k <;> by_cases hjl : G.Adj j l <;>
    simp [rowExtreme, crossTotal, edgeBit, equalityIndicator,
      mem_singletonSet, hk, hl, Xor, hik, hil, hjk, hjl]

theorem singleton_gate_eq_of_sameFiber (i j k l : Fin n) (hij : i ≠ j)
    {G H : GraphState n d} (h : SameFiber {i, j} G.val H.val) :
    (k ∈ singletonSet G.val i j ∧ l ∈ singletonSet G.val i j) ↔
      (k ∈ singletonSet H.val i j ∧ l ∈ singletonSet H.val i j) := by
  rw [singletonSet_eq_of_key_eq ((sameFiber_iff_key_eq i j hij G.val H.val).mp h)]

theorem expectation_mul_fiberConstant (a : Finset (Fin n))
    (c : GraphState n d → ℝ)
    (hc : ∀ G H, SameFiber a G.val H.val → c G = c H)
    (f : StateSpace n d) (G : GraphState n d) :
    expectation n d a (WithLp.toLp 2 (fun H => c H * f H)) G =
      c G * expectation n d a f G := by
  rw [expectation_eq_average, expectation_eq_average]
  have hs : (∑ H ∈ fiberStates a G, c H * f H) =
      c G * ∑ H ∈ fiberStates a G, f H := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro H hH
    rw [← hc G H ((mem_fiberStates a G H).mp hH)]
  change (∑ H ∈ fiberStates a G, c H * f H) / _ = _
  rw [hs]
  ring

theorem fluctuation_mul_fiberConstant (a : Finset (Fin n))
    (c : GraphState n d → ℝ)
    (hc : ∀ G H, SameFiber a G.val H.val → c G = c H)
    (f : StateSpace n d) (G : GraphState n d) :
    fluctuation n d a (WithLp.toLp 2 (fun H => c H * f H)) G =
      c G * fluctuation n d a f G := by
  rw [fluctuation_eq_sub, fluctuation_eq_sub]
  change c G * f G - expectation n d a _ G =
    c G * (f G - expectation n d a f G)
  rw [expectation_mul_fiberConstant a c hc f G]
  ring

theorem fluctuation_rowExtreme (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l) (G : GraphState n d) :
    fluctuation n d {i, j}
        (WithLp.toLp 2 (fun H : GraphState n d => rowExtreme H.val i j k l)) G =
      if k ∈ singletonSet G.val i j ∧ l ∈ singletonSet G.val i j then
        fluctuation n d {i, j}
          (WithLp.toLp 2 (fun H : GraphState n d => equalityIndicator H.val i k l)) G
      else 0 := by
  let c : GraphState n d → ℝ := fun H =>
    if k ∈ singletonSet H.val i j ∧ l ∈ singletonSet H.val i j then 1 else 0
  have hc : ∀ G H : GraphState n d, SameFiber {i, j} G.val H.val → c G = c H := by
    intro G H h
    simp only [c, singleton_gate_eq_of_sameFiber i j k l hij h]
  have heq : (WithLp.toLp 2 (fun H : GraphState n d => rowExtreme H.val i j k l) :
      StateSpace n d) = WithLp.toLp 2 (fun H : GraphState n d =>
        c H * equalityIndicator H.val i k l) := by
    ext H
    change rowExtreme H.val i j k l = c H * equalityIndicator H.val i k l
    rw [rowExtreme_eq_gated_equality H.val i j k l hk hl]
    simp only [c]
    split_ifs <;> simp
  rw [heq]
  have h := fluctuation_mul_fiberConstant {i, j} c hc
    (WithLp.toLp 2 (fun H : GraphState n d => equalityIndicator H.val i k l)) G
  simpa only [c, ite_mul, one_mul, zero_mul] using h

theorem rowExtreme_of_total_two (G : SimpleGraph (Fin n)) (i j k l : Fin n)
    (h : crossTotal G i j k l = 2) :
    rowExtreme G i j k l =
      if edgeBit G i k + edgeBit G i l ≠ 1 then 1 else 0 := by
  simp only [rowExtreme, h, true_and]

theorem fluctuation_affine (a : Finset (Fin n)) (f : StateSpace n d)
    (s r : ℝ) :
    fluctuation n d a (WithLp.toLp 2 (fun G : GraphState n d => s * f G + r)) =
      s • fluctuation n d a f := by
  have heq : (WithLp.toLp 2 (fun G : GraphState n d => s * f G + r) :
      StateSpace n d) = s • f + WithLp.toLp 2 (fun _ : GraphState n d => r) := by
    ext G
    rfl
  rw [heq, map_add, map_smul,
    (fluctuation_eq_zero_iff a _).mpr (constant_mem a r), add_zero]

theorem fluctuation_cell_affine_rowExtreme (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l)
    (c : GraphState n d → ℝ)
    (hc : ∀ G H, SameFiber {i, j} G.val H.val → c G = c H)
    (s r : ℝ) (G : GraphState n d) :
    fluctuation n d {i, j} (WithLp.toLp 2 (fun H : GraphState n d =>
        c H * (s * rowExtreme H.val i j k l + r))) G =
      (c G * s) *
        (if k ∈ singletonSet G.val i j ∧ l ∈ singletonSet G.val i j then
          fluctuation n d {i, j}
            (WithLp.toLp 2 (fun H : GraphState n d => equalityIndicator H.val i k l)) G
        else 0) := by
  rw [fluctuation_mul_fiberConstant {i, j} c hc
    (WithLp.toLp 2 (fun H : GraphState n d => s * rowExtreme H.val i j k l + r)) G]
  have h := fluctuation_affine {i, j}
    (WithLp.toLp 2 (fun H : GraphState n d => rowExtreme H.val i j k l)) s r
  change c G * (fluctuation n d {i, j}
    (WithLp.toLp 2 (fun H : GraphState n d => s * rowExtreme H.val i j k l + r))) G = _
  rw [h]
  change c G * (s * (fluctuation n d {i, j}
    (WithLp.toLp 2 (fun H : GraphState n d => rowExtreme H.val i j k l))) G) = _
  rw [fluctuation_rowExtreme i j k l hij hk hl G]
  ring

theorem leftSet_mem_iff_adj_of_singleton (G : SimpleGraph (Fin n))
    (i j k : Fin n) (hk : k ∈ singletonSet G i j) :
    k ∈ leftSet G i j ↔ G.Adj i k := by
  rcases (mem_singletonSet G i j k).mp hk with ⟨ho, hxor⟩
  rw [mem_leftSet]
  rcases hxor with ⟨hi, hj⟩ | ⟨hi, hj⟩ <;> simp [ho, hi, hj]

theorem equalityIndicator_eq_leftSet (G : SimpleGraph (Fin n))
    (i j k l : Fin n) (hk : k ∈ singletonSet G i j)
    (hl : l ∈ singletonSet G i j) :
    equalityIndicator G i k l =
      if (k ∈ leftSet G i j ↔ l ∈ leftSet G i j) then 1 else 0 := by
  simp only [leftSet_mem_iff_adj_of_singleton G i j k hk,
    leftSet_mem_iff_adj_of_singleton G i j l hl, equalityIndicator]

end Problem315.PairEqualityErrorLine

end

end OAI
