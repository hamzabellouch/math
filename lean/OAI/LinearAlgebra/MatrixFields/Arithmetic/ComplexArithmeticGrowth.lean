import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.ComplexExpressionFamily
import OAI.LinearAlgebra.MatrixFields.Tensors.TerminalRelabel

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation.Arithmetic.RecursiveBlock

namespace LinearExpression

variable {Input : Type*}

def sumFin : (n : ℕ) → (Fin n → Expression Input) → Expression Input
  | 0, _ => .constant 0
  | n + 1, f => .add (f 0) (sumFin n (fun i => f i.succ))

theorem eval_sumFin (n : ℕ) (f : Fin n → Expression Input) (inputs : Input → ℂ) :
    (sumFin n f).eval inputs = ∑ i, (f i).eval inputs := by
  induction n with
  | zero => simp [sumFin, Expression.eval]
  | succ n ih =>
    simp only [sumFin, Expression.eval, ih, Fin.sum_univ_succ]

theorem cost_sumFin (n : ℕ) (f : Fin n → Expression Input) :
    (sumFin n f).cost = (∑ i, (f i).cost) + n := by
  induction n with
  | zero => simp [sumFin, Expression.cost]
  | succ n ih =>
    simp only [sumFin, Expression.cost, ih, Fin.sum_univ_succ]
    omega

def linear {Term : Type*} [Fintype Term] (a : Term → ℂ) (wire : Term → Input) :
    Expression Input :=
  sumFin (Fintype.card Term) (fun i =>
    .mul (.constant (a ((Fintype.equivFin Term).symm i)))
      (.input (wire ((Fintype.equivFin Term).symm i))))

theorem eval_linear {Term : Type*} [Fintype Term]
    (a : Term → ℂ) (wire : Term → Input) (inputs : Input → ℂ) :
    (linear a wire).eval inputs = ∑ i, a i * inputs (wire i) := by
  rw [linear, eval_sumFin]
  exact (Fintype.equivFin Term).symm.sum_comp (fun i => a i * inputs (wire i))

theorem cost_linear {Term : Type*} [Fintype Term]
    (a : Term → ℂ) (wire : Term → Input) :
    (linear a wire).cost = 2 * Fintype.card Term := by
  simp [linear, cost_sumFin, Expression.cost, two_mul]

end LinearExpression

structure Family (Input Output : Type*) where
  registers : ℕ
  program : Program Input registers
  output : Output → Fin registers

namespace Family

variable {Input Mid Output : Type*}

def eval (p : Family Input Output) (inputs : Input → ℂ) (o : Output) : ℂ :=
  p.program.eval inputs (p.output o)

def cost (p : Family Input Output) : ℕ := p.program.cost

def expressions [Fintype Output] (e : Output → Expression Input) : Family Input Output :=
  let p := Expression.compileFamily e
  ⟨p.registers, p.program, p.output⟩

theorem eval_expressions [Fintype Output] (e : Output → Expression Input)
    (inputs : Input → ℂ) (o : Output) :
    (expressions e).eval inputs o = (e o).eval inputs :=
  (Expression.compileFamily e).correct inputs o

theorem cost_expressions [Fintype Output] (e : Output → Expression Input) :
    (expressions e).cost = ∑ o, (e o).cost :=
  (Expression.compileFamily e).cost_eq

def compose (p : Family Input Mid) (q : Family Mid Output) : Family Input Output :=
  let s := p.program.substitute q.program p.output
  ⟨s.registers, s.program, fun o => s.output (q.output o)⟩

theorem eval_compose (p : Family Input Mid) (q : Family Mid Output)
    (inputs : Input → ℂ) (o : Output) :
    (compose p q).eval inputs o = q.eval (p.eval inputs) o :=
  (p.program.substitute q.program p.output).correct inputs (q.output o)

theorem cost_compose (p : Family Input Mid) (q : Family Mid Output) :
    (compose p q).cost = p.cost + q.cost :=
  (p.program.substitute q.program p.output).cost_eq

def mapInputs {NewInput : Type*} (f : Input → NewInput) (p : Family Input Output) :
    Family NewInput Output :=
  ⟨p.registers, p.program.mapInput f, p.output⟩

theorem eval_mapInputs {NewInput : Type*} (f : Input → NewInput)
    (p : Family Input Output) (inputs : NewInput → ℂ) (o : Output) :
    (p.mapInputs f).eval inputs o = p.eval (fun i => inputs (f i)) o := by
  exact Program.eval_mapInput f p.program inputs (p.output o)

theorem cost_mapInputs {NewInput : Type*} (f : Input → NewInput)
    (p : Family Input Output) : (p.mapInputs f).cost = p.cost := by
  exact Program.cost_mapInput f p.program

def parallel : (r : ℕ) → (Fin r → Family Input Output) → Family Input (Fin r × Output)
  | 0, _ => ⟨0, Program.nil, fun o => Fin.elim0 o.1⟩
  | r + 1, p =>
    let head := p 0
    let tail := parallel r (fun i => p i.succ)
    { registers := head.registers + tail.registers
      program := head.program.append tail.program
      output := fun o => Fin.cases
        (Program.oldIndex _ _ (head.output o.2))
        (fun i => Program.newIndex _ _ (tail.output (i, o.2))) o.1 }

theorem eval_parallel (r : ℕ) (p : Fin r → Family Input Output)
    (inputs : Input → ℂ) (o : Fin r × Output) :
    (parallel r p).eval inputs o = (p o.1).eval inputs o.2 := by
  induction r with
  | zero => exact Fin.elim0 o.1
  | succ r ih =>
    rcases o with ⟨i, o⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Program.eval_append_old _ _ inputs _
    · exact (Program.eval_append_new _ _ inputs _).trans
        (ih (fun j => p j.succ) (j, o))

theorem cost_parallel (r : ℕ) (p : Fin r → Family Input Output) :
    (parallel r p).cost = ∑ i, (p i).cost := by
  induction r with
  | zero => simp [parallel, cost, Program.cost]
  | succ r ih =>
    change ((p 0).program.append (parallel r (fun i => p i.succ)).program).cost = _
    rw [Program.cost_append]
    change (p 0).cost + (parallel r (fun i => p i.succ)).cost = _
    rw [ih, Fin.sum_univ_succ]

def copies (r : ℕ) (p : Family Input Output) :
    Family (Fin r × Input) (Fin r × Output) :=
  parallel r (fun i => p.mapInputs (fun x => (i, x)))

theorem eval_copies (r : ℕ) (p : Family Input Output)
    (inputs : Fin r × Input → ℂ) (o : Fin r × Output) :
    (copies r p).eval inputs o = p.eval (fun x => inputs (o.1, x)) o.2 := by
  rw [copies, eval_parallel, eval_mapInputs]

theorem cost_copies (r : ℕ) (p : Family Input Output) :
    (copies r p).cost = r * p.cost := by
  simp [copies, cost_parallel, cost_mapInputs]

def ofMatrix {m : ℕ} (p : MatrixAlgorithm m) :
    Family (MatrixInput m) (Fin m × Fin m) :=
  ⟨p.registers, p.program, fun o => p.output o.1 o.2⟩

@[simp] theorem cost_ofMatrix {m : ℕ} (p : MatrixAlgorithm m) :
    (ofMatrix p).cost = p.cost := rfl

theorem eval_ofMatrix {m : ℕ} (p : MatrixAlgorithm m) (hp : p.Correct)
    (inputs : MatrixInput m → ℂ) (o : Fin m × Fin m) :
    (ofMatrix p).eval inputs o =
      ∑ j, inputs (.inl (o.1, j)) * inputs (.inr (j, o.2)) := by
  have h := (MatrixAlgorithm.correct_iff_entries p).mp hp
    (fun i j => inputs (.inl (i, j))) (fun j k => inputs (.inr (j, k))) o.1 o.2
  have hi : matrixInputs (fun i j => inputs (.inl (i, j)))
      (fun j k => inputs (.inr (j, k))) = inputs := by
    funext x
    cases x <;> rfl
  rw [hi] at h
  exact h

end Family

section BlockIdentities

variable {n r m : ℕ}

def join (i : Fin n) (j : Fin m) : Fin (n * m) := finProdFinEquiv (i, j)

theorem rank_bilinear_identity
    (a b c : Fin r → Fin n × Fin n → ℂ)
    (h : Tensor.matrixMultiplication n n n =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (left right : Fin n × Fin n → ℂ) (i k : Fin n) :
    (∑ q, c q (k, i) * (∑ x, a q x * left x) * (∑ y, b q y * right y)) =
      ∑ j, left (i, j) * right (j, k) := by
  rw [← Tensor.contract_matrixCoefficients left right i k]
  change _ = Tensor.contract (Tensor.matrixMultiplication n n n) left right (k, i)
  rw [h]
  simp only [Tensor.contract, Tensor.rankOne, Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ q, ∑ y, ∑ x, c q (k, i) * (a q x * left x) * (b q y * right y)) =
        ∑ q, ∑ x, ∑ y, c q (k, i) * (a q x * left x) * (b q y * right y) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact Finset.sum_comm
    _ =
        ∑ x, ∑ q, ∑ y, c q (k, i) * (a q x * left x) * (b q y * right y) :=
      Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ q, a q x * b q y * c q (k, i) * left x * right y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro q hq
      ring

def leftBlock (a : Fin r → Fin n × Fin n → ℂ)
    (A : Matrix (Fin (n * m)) (Fin (n * m)) ℂ) (q : Fin r) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun s t => ∑ x, a q x * A (join x.1 s) (join x.2 t)

def rightBlock (b : Fin r → Fin n × Fin n → ℂ)
    (B : Matrix (Fin (n * m)) (Fin (n * m)) ℂ) (q : Fin r) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun t u => ∑ y, b q y * B (join y.1 t) (join y.2 u)

theorem block_identity
    (a b c : Fin r → Fin n × Fin n → ℂ)
    (h : Tensor.matrixMultiplication n n n =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (A B : Matrix (Fin (n * m)) (Fin (n * m)) ℂ)
    (i k : Fin n) (s u : Fin m) :
    (∑ q, c q (k, i) * ((leftBlock a A q) * (rightBlock b B q)) s u) =
      (A * B) (join i s) (join k u) := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hlocal (t : Fin m) := rank_bilinear_identity a b c h
    (fun x => A (join x.1 s) (join x.2 t))
    (fun y => B (join y.1 t) (join y.2 u)) i k
  simp only [leftBlock, rightBlock]
  simp_rw [← mul_assoc, hlocal]
  rw [Finset.sum_comm]
  exact (Fintype.sum_prod_type _).symm.trans
    (finProdFinEquiv.sum_comp (fun j => A (join i s) j * B j (join k u)))

end BlockIdentities

variable {n r m : ℕ}

def inputExpressions (a b : Fin r → Fin n × Fin n → ℂ) :
    Fin r × MatrixInput m → Expression (MatrixInput (n * m))
  | (q, .inl (s, t)) => LinearExpression.linear (a q)
      (fun x => .inl (join x.1 s, join x.2 t))
  | (q, .inr (t, u)) => LinearExpression.linear (b q)
      (fun y => .inr (join y.1 t, join y.2 u))

def inputFamily (a b : Fin r → Fin n × Fin n → ℂ) :
    Family (MatrixInput (n * m)) (Fin r × MatrixInput m) :=
  Family.expressions (inputExpressions a b)

theorem inputFamily_eval (a b : Fin r → Fin n × Fin n → ℂ)
    (A B : Matrix (Fin (n * m)) (Fin (n * m)) ℂ) (q : Fin r) (x : MatrixInput m) :
    (inputFamily a b).eval (matrixInputs A B) (q, x) =
      matrixInputs (leftBlock a A q) (rightBlock b B q) x := by
  cases x with
  | inl x =>
    simp only [inputFamily, Family.eval_expressions, inputExpressions,
      LinearExpression.eval_linear, matrixInputs, leftBlock]
  | inr x =>
    simp only [inputFamily, Family.eval_expressions, inputExpressions,
      LinearExpression.eval_linear, matrixInputs, rightBlock]

theorem inputFamily_cost (a b : Fin r → Fin n × Fin n → ℂ) :
    (inputFamily (m := m) a b).cost = 4 * r * n ^ 2 * m ^ 2 := by
  rw [inputFamily, Family.cost_expressions]
  have hc (o : Fin r × MatrixInput m) : (inputExpressions a b o).cost = 2 * n ^ 2 := by
    rcases o with ⟨q, o⟩
    cases o <;> simp [inputExpressions, LinearExpression.cost_linear, pow_two]
  simp_rw [hc]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_sum, smul_eq_mul]
  ring

def recursiveProducts (a b : Fin r → Fin n × Fin n → ℂ) (p : MatrixAlgorithm m) :
    Family (MatrixInput (n * m)) (Fin r × (Fin m × Fin m)) :=
  (inputFamily a b).compose (Family.copies r (Family.ofMatrix p))

theorem recursiveProducts_eval (a b : Fin r → Fin n × Fin n → ℂ)
    (p : MatrixAlgorithm m) (hp : p.Correct)
    (A B : Matrix (Fin (n * m)) (Fin (n * m)) ℂ) (q : Fin r) (s u : Fin m) :
    (recursiveProducts a b p).eval (matrixInputs A B) (q, (s, u)) =
      ((leftBlock a A q) * (rightBlock b B q)) s u := by
  rw [recursiveProducts, Family.eval_compose, Family.eval_copies,
    Family.eval_ofMatrix _ hp]
  simp only [inputFamily_eval, matrixInputs, Matrix.mul_apply]

theorem recursiveProducts_cost (a b : Fin r → Fin n × Fin n → ℂ)
    (p : MatrixAlgorithm m) :
    (recursiveProducts a b p).cost = 4 * r * n ^ 2 * m ^ 2 + r * p.cost := by
  rw [recursiveProducts, Family.cost_compose, inputFamily_cost,
    Family.cost_copies, Family.cost_ofMatrix]

def outputExpressions (c : Fin r → Fin n × Fin n → ℂ) :
    Fin (n * m) × Fin (n * m) → Expression (Fin r × (Fin m × Fin m)) :=
  fun o => LinearExpression.linear
    (fun q => c q ((finProdFinEquiv.symm o.2).1, (finProdFinEquiv.symm o.1).1))
    (fun q => (q, ((finProdFinEquiv.symm o.1).2, (finProdFinEquiv.symm o.2).2)))

def outputFamily (c : Fin r → Fin n × Fin n → ℂ) :
    Family (Fin r × (Fin m × Fin m)) (Fin (n * m) × Fin (n * m)) :=
  Family.expressions (outputExpressions c)

theorem outputFamily_eval (c : Fin r → Fin n × Fin n → ℂ)
    (inputs : Fin r × (Fin m × Fin m) → ℂ) (i k : Fin n) (s u : Fin m) :
    (outputFamily c).eval inputs (join i s, join k u) =
      ∑ q, c q (k, i) * inputs (q, (s, u)) := by
  simp only [outputFamily, Family.eval_expressions, outputExpressions,
    LinearExpression.eval_linear, join, Equiv.symm_apply_apply]

theorem outputFamily_cost (c : Fin r → Fin n × Fin n → ℂ) :
    (outputFamily (m := m) c).cost = 2 * r * n ^ 2 * m ^ 2 := by
  simp only [outputFamily, Family.cost_expressions, outputExpressions,
    LinearExpression.cost_linear, Fintype.card_fin, Finset.sum_const,
    Finset.card_univ, Fintype.card_prod, smul_eq_mul]
  ring

def algorithm (a b c : Fin r → Fin n × Fin n → ℂ) (p : MatrixAlgorithm m) :
    MatrixAlgorithm (n * m) :=
  let f := (recursiveProducts a b p).compose (outputFamily c)
  ⟨f.registers, f.program, fun i k => f.output (i, k)⟩

theorem algorithm_correct
    (a b c : Fin r → Fin n × Fin n → ℂ)
    (h : Tensor.matrixMultiplication n n n =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (p : MatrixAlgorithm m) (hp : p.Correct) : (algorithm a b c p).Correct := by
  intro A B
  funext i k
  obtain ⟨⟨i, s⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨k, u⟩, rfl⟩ := finProdFinEquiv.surjective k
  change ((recursiveProducts a b p).compose (outputFamily c)).eval
    (matrixInputs A B) (join i s, join k u) = _
  rw [Family.eval_compose, outputFamily_eval]
  simp_rw [recursiveProducts_eval a b p hp A B]
  exact block_identity a b c h A B i k s u

theorem algorithm_cost (a b c : Fin r → Fin n × Fin n → ℂ)
    (p : MatrixAlgorithm m) :
    (algorithm a b c p).cost = r * p.cost + (6 * r * n ^ 2) * m ^ 2 := by
  change ((recursiveProducts a b p).compose (outputFamily c)).cost = _
  rw [Family.cost_compose, recursiveProducts_cost, outputFamily_cost]
  ring

theorem rank_block_step (h : Tensor.RankAtMost (Tensor.matrixMultiplication n n n) r)
    (p : MatrixAlgorithm m) (hp : p.Correct) :
    ∃ q : MatrixAlgorithm (n * m), q.Correct ∧
      q.cost = r * p.cost + (6 * r * n ^ 2) * m ^ 2 := by
  rcases h with ⟨a, b, c, h⟩
  exact ⟨algorithm a b c p, algorithm_correct a b c h p hp, algorithm_cost a b c p⟩

end MatrixMultiplication.Foundation.Arithmetic.RecursiveBlock

end

noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

theorem exists_power_cover {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) :
    ∃ k : ℕ, n ≤ b ^ k ∧ b ^ k ≤ b * n := by
  refine ⟨Nat.log b n + 1, (Nat.lt_pow_succ_log_self (by omega) n).le, ?_⟩
  rw [pow_succ']
  exact Nat.mul_le_mul_left b (Nat.pow_log_le_self b (by omega))

theorem geometric_cost_recurrence_bound (x : ℕ → ℝ) (a b d q : ℝ)
    (hx : 0 ≤ x 0) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (haq : a < q) (hdq : d ≤ q)
    (hstep : ∀ k, x (k + 1) ≤ a * x k + b * d ^ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ k, x k ≤ C * q ^ k := by
  let C := x 0 + b / (q - a) + 1
  have hgap : 0 < q - a := sub_pos.mpr haq
  have hfrac : 0 ≤ b / (q - a) := div_nonneg hb hgap.le
  have hC : 0 < C := by dsimp [C]; linarith
  have hcancel : (q - a) * (b / (q - a)) = b := by
    field_simp [ne_of_gt hgap]
  have hCfrac : b / (q - a) ≤ C := by dsimp [C]; linarith
  have hcoeff : a * C + b ≤ C * q := by
    have hmul := mul_le_mul_of_nonneg_left hCfrac hgap.le
    rw [hcancel] at hmul
    calc
      a * C + b ≤ a * C + (q - a) * C := add_le_add (le_refl _) hmul
      _ = C * q := by ring
  refine ⟨C, hC, ?_⟩
  intro k
  induction k with
  | zero => simp only [pow_zero, mul_one]; dsimp [C]; linarith
  | succ k ih =>
    calc
      x (k + 1) ≤ a * x k + b * d ^ k := hstep k
      _ ≤ a * (C * q ^ k) + b * q ^ k :=
        add_le_add (mul_le_mul_of_nonneg_left ih ha)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd hdq k) hb)
      _ = (a * C + b) * q ^ k := by ring
      _ ≤ (C * q) * q ^ k :=
        mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (hd.trans hdq) k)
      _ = C * q ^ (k + 1) := by rw [pow_succ]; ring

theorem power_cost_padding_bound
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost)
    {b : ℕ} (hb : 2 ≤ b) {s C : ℝ} (hs : 0 ≤ s) (hC : 0 < C)
    (hpower : ∀ k : ℕ, ∃ P : MatrixAlgorithm (b ^ k),
      P.Correct ∧ (P.cost : ℝ) ≤ C * ((b : ℝ) ^ s) ^ k) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm n,
      P.Correct ∧ (P.cost : ℝ) ≤ D * (n : ℝ) ^ s := by
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  refine ⟨C * (b : ℝ) ^ s, mul_pos hC (Real.rpow_pos_of_pos hbpos s), ?_⟩
  intro n hn
  obtain ⟨k, hnk, hkn⟩ := exists_power_cover hb hn
  obtain ⟨P, hP, hcost⟩ := hpower k
  obtain ⟨Q, hQ, hQP⟩ := hpad hnk P hP
  refine ⟨Q, hQ, ?_⟩
  calc
    (Q.cost : ℝ) ≤ (P.cost : ℝ) := by exact_mod_cast hQP
    _ ≤ C * ((b : ℝ) ^ s) ^ k := hcost
    _ = C * ((b ^ k : ℕ) : ℝ) ^ s := by
      rw [Real.rpow_pow_comm hbpos.le, Nat.cast_pow]
    _ ≤ C * ((b : ℝ) * (n : ℝ)) ^ s :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hkn) hs) hC.le
    _ = (C * (b : ℝ) ^ s) * (n : ℝ) ^ s := by
      rw [Real.mul_rpow hbpos.le (Nat.cast_nonneg n)]
      ring

theorem admissibleExponent_of_uniform_power_costs
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost)
    {b : ℕ} (hb : 2 ≤ b) {τ C : ℝ} (hτ : 0 ≤ τ) (hC : 0 < C)
    (hpower : ∀ k : ℕ, ∃ P : MatrixAlgorithm (b ^ k),
      P.Correct ∧ (P.cost : ℝ) ≤ C * ((b : ℝ) ^ τ) ^ k) :
    AdmissibleExponent τ := by
  obtain ⟨D, hD, hall⟩ := power_cost_padding_bound hpad hb hτ hC hpower
  intro ε hε
  refine ⟨D, hD, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hall n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)) hD.le

theorem admissibleExponent_of_power_costs
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost)
    {b : ℕ} (hb : 2 ≤ b) {τ : ℝ} (hτ : 0 ≤ τ)
    (hpower : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ, ∃ P : MatrixAlgorithm (b ^ k),
        P.Correct ∧ (P.cost : ℝ) ≤ C * ((b : ℝ) ^ (τ + ε)) ^ k) :
    AdmissibleExponent τ := by
  intro ε hε
  obtain ⟨C, hC, hcost⟩ := hpower ε hε
  exact power_cost_padding_bound hpad hb (by linarith) hC hcost

theorem admissibleExponent_of_recursive_costs
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost)
    {b R K : ℕ} (hb : 2 ≤ b) {τ : ℝ} (hτ : 2 ≤ τ)
    (hR : (R : ℝ) ≤ (b : ℝ) ^ τ)
    (P : ∀ k : ℕ, MatrixAlgorithm (b ^ k))
    (hP : ∀ k, (P k).Correct)
    (hstep : ∀ k, (P (k + 1)).cost ≤ R * (P k).cost + K * (b ^ k) ^ 2) :
    AdmissibleExponent τ := by
  apply admissibleExponent_of_power_costs hpad hb (by linarith)
  intro ε hε
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hbone : 1 < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hrate : (R : ℝ) < (b : ℝ) ^ (τ + ε) :=
    hR.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hbone (by linarith))
  have hquad : (b : ℝ) ^ (2 : ℕ) ≤ (b : ℝ) ^ (τ + ε) := by
    rw [← Real.rpow_natCast]
    change (b : ℝ) ^ (2 : ℝ) ≤ (b : ℝ) ^ (τ + ε)
    exact Real.rpow_le_rpow_of_exponent_le hbone.le (by linarith)
  obtain ⟨C, hC, hbound⟩ := geometric_cost_recurrence_bound
    (fun k => ((P k).cost : ℝ)) (R : ℝ) (K : ℝ) ((b : ℝ) ^ (2 : ℕ))
    ((b : ℝ) ^ (τ + ε)) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (sq_nonneg _) hrate hquad (fun k => by
      have h := hstep k
      have hcast : ((P (k + 1)).cost : ℝ) ≤
          (R : ℝ) * ((P k).cost : ℝ) + (K : ℝ) * ((b : ℝ) ^ k) ^ 2 := by
        exact_mod_cast h
      simpa only [← pow_mul, Nat.mul_comm k 2] using hcast)
  exact ⟨C, hC, fun k => ⟨P k, hP k, hbound k⟩⟩

def blockRecurrenceCost (b R K : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => R * blockRecurrenceCost b R K k + K * (b ^ k) ^ 2

@[simp] theorem blockRecurrenceCost_zero (b R K : ℕ) :
    blockRecurrenceCost b R K 0 = 1 := rfl

@[simp] theorem blockRecurrenceCost_succ (b R K k : ℕ) :
    blockRecurrenceCost b R K (k + 1) =
      R * blockRecurrenceCost b R K k + K * (b ^ k) ^ 2 := rfl

theorem power_programs_of_block_step {b R K : ℕ}
    (hstep : ∀ m : ℕ, ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm (b * m), Q.Correct ∧
        Q.cost ≤ R * P.cost + K * m ^ 2) :
    ∀ k : ℕ, ∃ P : MatrixAlgorithm (b ^ k), P.Correct ∧
      P.cost ≤ blockRecurrenceCost b R K k := by
  intro k
  induction k with
  | zero =>
    exact ⟨scalarAlgorithm, scalarAlgorithm_correct, by simp⟩
  | succ k ih =>
    obtain ⟨P, hP, hcost⟩ := ih
    obtain ⟨Q, hQ, hQcost⟩ := hstep (b ^ k) P hP
    have hbound : Q.cost ≤ blockRecurrenceCost b R K (k + 1) := by
      exact hQcost.trans (Nat.add_le_add_right (Nat.mul_le_mul_left R hcost) _)
    have hresult : ∃ Q : MatrixAlgorithm (b * b ^ k), Q.Correct ∧
        Q.cost ≤ blockRecurrenceCost b R K (k + 1) := ⟨Q, hQ, hbound⟩
    exact (pow_succ' b k).symm ▸ hresult

theorem admissibleExponent_of_block_step_of_padding
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost)
    {b R K : ℕ} (hb : 2 ≤ b) {τ : ℝ} (hτ : 2 ≤ τ)
    (hR : (R : ℝ) ≤ (b : ℝ) ^ τ)
    (hstep : ∀ m : ℕ, ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm (b * m), Q.Correct ∧
        Q.cost ≤ R * P.cost + K * m ^ 2) :
    AdmissibleExponent τ := by
  apply admissibleExponent_of_power_costs hpad hb (by linarith)
  intro ε hε
  have hbone : 1 < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hrate : (R : ℝ) < (b : ℝ) ^ (τ + ε) :=
    hR.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hbone (by linarith))
  have hquad : (b : ℝ) ^ (2 : ℕ) ≤ (b : ℝ) ^ (τ + ε) := by
    rw [← Real.rpow_natCast]
    change (b : ℝ) ^ (2 : ℝ) ≤ (b : ℝ) ^ (τ + ε)
    exact Real.rpow_le_rpow_of_exponent_le hbone.le (by linarith)
  obtain ⟨C, hC, hbound⟩ := geometric_cost_recurrence_bound
    (fun k => (blockRecurrenceCost b R K k : ℝ))
    (R : ℝ) (K : ℝ) ((b : ℝ) ^ (2 : ℕ)) ((b : ℝ) ^ (τ + ε))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (sq_nonneg _) hrate hquad (fun k => by
      simp only [blockRecurrenceCost_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2])
  refine ⟨C, hC, ?_⟩
  intro k
  obtain ⟨P, hP, hcost⟩ := power_programs_of_block_step hstep k
  exact ⟨P, hP, (by exact_mod_cast hcost : (P.cost : ℝ) ≤
    (blockRecurrenceCost b R K k : ℝ)).trans (hbound k)⟩

theorem admissibleExponent_of_block_step
    {b R K : ℕ} (hb : 2 ≤ b) {τ : ℝ} (hτ : 2 ≤ τ)
    (hR : (R : ℝ) ≤ (b : ℝ) ^ τ)
    (hstep : ∀ m : ℕ, ∀ P : MatrixAlgorithm m, P.Correct →
      ∃ Q : MatrixAlgorithm (b * m), Q.Correct ∧
        Q.cost ≤ R * P.cost + K * m ^ 2) :
    AdmissibleExponent τ :=
  admissibleExponent_of_block_step_of_padding
    (fun h P hP => MatrixAlgorithm.exists_restrict h P hP) hb hτ hR hstep

theorem admissibleExponent_of_rankAtMost {n R : ℕ} (hn : 2 ≤ n)
    (hRank : Tensor.RankAtMost (Tensor.matrixMultiplication n n n) R)
    {τ : ℝ} (hτ : 2 ≤ τ) (hR : (R : ℝ) ≤ (n : ℝ) ^ τ) :
    AdmissibleExponent τ := by
  apply admissibleExponent_of_block_step (K := 6 * R * n ^ 2) hn hτ hR
  intro m P hP
  obtain ⟨Q, hQ, hcost⟩ := RecursiveBlock.rank_block_step hRank P hP
  exact ⟨Q, hQ, hcost.le⟩

end MatrixMultiplication.Foundation.Arithmetic

end

end MatrixAllFields

end OAI
