import Mathlib

namespace OAI

/-! Nonnegative falling-factorial expansions for the local trace weights. -/
namespace Problem335

open scoped BigOperators

universe u

/-- Evaluation of a falling-factorial monomial at a natural occupation vector. -/
def factorialMonomial {σ : Type u} [Fintype σ]
    (d M : σ → ℕ) : ℕ := ∏ i, (M i).descFactorial (d i)

/-- A finite expansion with natural (hence nonnegative) coefficients,
    bounded total order, supported on a specified coordinate set. -/
structure FactorialExpansion {σ : Type u} [Fintype σ]
    (f : (σ → ℕ) → ℕ) (S : Finset σ) (D : ℕ) where
  Index : Type
  indexFintype : Fintype Index
  coeff : Index → ℕ
  degree : Index → σ → ℕ
  order_le : ∀ j, ∑ i, degree j i ≤ D
  supported : ∀ j i, i ∉ S → degree j i = 0
  eval_eq : ∀ M, f M = ∑ j, coeff j * factorialMonomial (degree j) M

attribute [instance] FactorialExpansion.indexFintype

namespace FactorialExpansion

variable {σ : Type u} [Fintype σ] [DecidableEq σ]

/-- Addition preserves positivity of the factorial-basis coefficients. -/
def add {f g : (σ → ℕ) → ℕ} {S : Finset σ} {D : ℕ}
    (F : FactorialExpansion f S D) (G : FactorialExpansion g S D) :
    FactorialExpansion (fun M => f M + g M) S D where
  Index := F.Index ⊕ G.Index
  indexFintype := inferInstance
  coeff := Sum.elim F.coeff G.coeff
  degree := Sum.elim F.degree G.degree
  order_le := by rintro (j | j); exact F.order_le j; exact G.order_le j
  supported := by rintro (j | j) i hi; exact F.supported j i hi; exact G.supported j i hi
  eval_eq := by
    intro M
    rw [F.eval_eq, G.eval_eq]
    simp

/-- A disjoint-coordinate product has the product of the local coefficients. -/
def mul {f g : (σ → ℕ) → ℕ} {S T : Finset σ} {D E : ℕ}
    (F : FactorialExpansion f S D) (G : FactorialExpansion g T E)
    (hST : Disjoint S T) :
    FactorialExpansion (fun M => f M * g M) (S ∪ T) (D + E) where
  Index := F.Index × G.Index
  indexFintype := inferInstance
  coeff := fun j => F.coeff j.1 * G.coeff j.2
  degree := fun j i => F.degree j.1 i + G.degree j.2 i
  order_le := by
    intro j
    simpa [Finset.sum_add_distrib] using Nat.add_le_add (F.order_le j.1) (G.order_le j.2)
  supported := by
    intro j i hi
    simp only [Finset.mem_union, not_or] at hi
    simp [F.supported j.1 i hi.1, G.supported j.2 i hi.2]
  eval_eq := by
    intro M
    have hterm (a : F.Index) (b : G.Index) :
        factorialMonomial (fun i => F.degree a i + G.degree b i) M =
          factorialMonomial (F.degree a) M * factorialMonomial (G.degree b) M := by
      unfold factorialMonomial
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hS : i ∈ S
      · have hT : i ∉ T := fun ht => (Finset.disjoint_left.mp hST) hS ht
        simp [G.supported b i hT]
      · simp [F.supported a i hS]
    rw [F.eval_eq, G.eval_eq, Finset.sum_mul_sum]
    simp only [Fintype.sum_prod_type, hterm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring

theorem factorialMonomial_single (i : σ) (d : ℕ) (M : σ → ℕ) :
    factorialMonomial (fun j => if j = i then d else 0) M = (M i).descFactorial d := by
  simp [factorialMonomial, apply_ite]

/-- Lift an explicit univariate expansion to one selected coordinate. -/
def coordinate (i : σ) (J : Type) [Fintype J] (c e : J → ℕ)
    {f : ℕ → ℕ} {D : ℕ} (he : ∀ j, e j ≤ D)
    (hf : ∀ z, f z = ∑ j, c j * z.descFactorial (e j)) :
    FactorialExpansion (fun M => f (M i)) {i} D where
  Index := J
  indexFintype := inferInstance
  coeff := c
  degree := fun a j => if j = i then e a else 0
  order_le := by intro a; simpa using he a
  supported := by
    intro a j hj
    simp only [Finset.mem_singleton] at hj
    simp [hj]
  eval_eq := by intro M; simpa only [factorialMonomial_single] using hf (M i)

/-- The occupation itself has order one. -/
def occupation (i : σ) : FactorialExpansion (fun M => M i) {i} 1 :=
  coordinate (f := fun z => z) (D := 1) i Unit (fun _ => 1) (fun _ => 1) (by simp) (by simp)

/-- Creation operators contribute the successor occupation. -/
def successor (i : σ) : FactorialExpansion (fun M => M i + 1) {i} 1 :=
  coordinate (f := fun z => z + 1) (D := 1) i (Fin 2) (fun _ => 1) ![1, 0]
    (by intro j; fin_cases j <;> simp)
    (by intro z; simp [Fin.sum_univ_two])

theorem square_descFactorial (z : ℕ) : z ^ 2 = z.descFactorial 2 + z := by
  cases z with
  | zero => simp
  | succ z => simp [Nat.descFactorial_succ]; ring

/-- A repeated annihilation coordinate retains its extra first-order term. -/
def square (i : σ) : FactorialExpansion (fun M => (M i) ^ 2) {i} 2 :=
  coordinate (f := fun z => z ^ 2) (D := 2) i (Fin 2) (fun _ => 1) ![2, 1]
    (by intro j; fin_cases j <;> simp)
    (by intro z; simpa [Fin.sum_univ_two] using square_descFactorial z)

/-- The repeated creation-coordinate weight has coefficients `1,3,1`. -/
def successorSquare (i : σ) :
    FactorialExpansion (fun M => (M i + 1) ^ 2) {i} 2 :=
  coordinate (f := fun z => (z + 1) ^ 2) (D := 2) i (Fin 3) ![1, 3, 1] ![2, 1, 0]
    (by intro j; fin_cases j <;> simp)
    (by
      intro z
      simp only [Fin.sum_univ_three]
      simp
      have h := square_descFactorial z
      simp [Nat.descFactorial_succ] at h
      nlinarith)

/-- Copy the coefficient data while enlarging bounds or changing the displayed
function by pointwise equality. Unlike a type cast, this keeps all data projections transparent. -/
def reframe {f g : (σ → ℕ) → ℕ} {S T : Finset σ} {D E : ℕ}
    (F : FactorialExpansion f S D) (hfg : ∀ M, f M = g M)
    (hST : S ⊆ T) (hDE : D ≤ E) : FactorialExpansion g T E where
  Index := F.Index
  indexFintype := F.indexFintype
  coeff := F.coeff
  degree := F.degree
  order_le := fun j => (F.order_le j).trans hDE
  supported := fun j i hi => F.supported j i (fun h => hi (hST h))
  eval_eq := fun M => (hfg M).symm.trans (F.eval_eq M)

/-- The normal pairing in a derivative layer, including equal coordinates. -/
def normalDerivative (i j : σ) :
    FactorialExpansion (fun M => M i * M j) {i, j} 2 := by
  by_cases h : i = j
  · exact (square i).reframe (by intro M; simp [h, pow_two]) (by simp) (by rfl)
  · exact ((occupation i).mul (occupation j) (by simpa using h)).reframe
      (by intro M; rfl) (by simp) (by rfl)

/-- The normal pairing in a multiplication layer, including equal coordinates. -/
def normalMultiplication (i j : σ) :
    FactorialExpansion (fun M => (M i + 1) * (M j + 1)) {i, j} 2 := by
  by_cases h : i = j
  · exact (successorSquare i).reframe (by intro M; simp [h, pow_two]) (by simp) (by rfl)
  · exact ((successor i).mul (successor j) (by simpa using h)).reframe
      (by intro M; rfl) (by simp) (by rfl)

/-- The distinct-coordinate pairing in a derivative layer. -/
def distinctDerivative (i j : σ) (h : i ≠ j) :
    FactorialExpansion (fun M => M i * (M j + 1)) {i, j} 2 :=
  ((occupation i).mul (successor j) (by simpa using h)).reframe
    (by intro M; rfl) (by simp) (by rfl)

/-- The distinct-coordinate pairing in a multiplication layer. -/
def distinctMultiplication (i j : σ) (h : i ≠ j) :
    FactorialExpansion (fun M => (M i + 1) * M j) {i, j} 2 :=
  ((successor i).mul (occupation j) (by simpa using h)).reframe
    (by intro M; rfl) (by simp) (by rfl)

omit [DecidableEq σ] in
/-- The same expansion as a real-valued sum, ready for expectation comparisons. -/
theorem eval_real {f : (σ → ℕ) → ℕ} {S : Finset σ} {D : ℕ}
    (F : FactorialExpansion f S D) (M : σ → ℕ) :
    (f M : ℝ) = ∑ j, (F.coeff j : ℝ) * (factorialMonomial (F.degree j) M : ℝ) := by
  exact_mod_cast F.eval_eq M

/-- A constant has a single order-zero term. -/
def constant (c : ℕ) : FactorialExpansion (fun _ : σ → ℕ => c) ∅ 0 where
  Index := Unit
  indexFintype := inferInstance
  coeff := fun _ => c
  degree := fun _ _ => 0
  order_le := by simp
  supported := by simp
  eval_eq := by simp [factorialMonomial]

/-- Products of local weights on pairwise disjoint coordinate sets retain a
nonnegative factorial expansion, and their local order bounds add. -/
theorem nonempty_prod {ι : Type*} (s : Finset ι)
    (f : ι → (σ → ℕ) → ℕ) (S : ι → Finset σ) (D : ι → ℕ)
    (F : ∀ i, FactorialExpansion (f i) (S i) (D i))
    (hS : (s : Set ι).Pairwise fun i j => Disjoint (S i) (S j)) :
    Nonempty (FactorialExpansion (fun M => ∏ i ∈ s, f i M)
      (s.biUnion S) (∑ i ∈ s, D i)) := by
  classical
  revert hS
  induction s using Finset.induction_on with
  | empty =>
    intro hS
    simpa using (show Nonempty (FactorialExpansion (fun _ : σ → ℕ => 1) ∅ 0) from
      ⟨constant 1⟩)
  | @insert a s ha ih =>
    intro hS
    have hs : (s : Set ι).Pairwise fun i j => Disjoint (S i) (S j) := by
      intro i hi j hj hij
      exact hS (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) hij
    obtain ⟨G⟩ := ih hs
    have hd : Disjoint (S a) (s.biUnion S) := by
      rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact hS (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj)
        (by intro h; subst j; exact ha hj)
    simpa [Finset.prod_insert, Finset.biUnion_insert, Finset.sum_insert, ha] using
      (show Nonempty (FactorialExpansion
        (fun M => f a M * ∏ i ∈ s, f i M) (S a ∪ s.biUnion S)
        (D a + ∑ i ∈ s, D i)) from ⟨(F a).mul G hd⟩)

omit [DecidableEq σ] in
/-- Any real linear functional can be evaluated termwise in the expansion. -/
theorem linear_eval {f : (σ → ℕ) → ℕ} {S : Finset σ} {D : ℕ}
    (F : FactorialExpansion f S D)
    (L : ((σ → ℕ) → ℝ) →ₗ[ℝ] ℝ) :
    L (fun M => (f M : ℝ)) =
      ∑ j, (F.coeff j : ℝ) * L (fun M => (factorialMonomial (F.degree j) M : ℝ)) := by
  have h : (fun M => (f M : ℝ)) =
      ∑ j, (F.coeff j : ℝ) • (fun M => (factorialMonomial (F.degree j) M : ℝ)) := by
    funext M
    simpa using F.eval_real M
  rw [h]
  simp

omit [DecidableEq σ] in
/-- Termwise moment comparison extends to every nonnegative factorial expansion. -/
theorem linear_comparison {f : (σ → ℕ) → ℕ} {S : Finset σ} {D : ℕ}
    (F : FactorialExpansion f S D)
    (L R : ((σ → ℕ) → ℝ) →ₗ[ℝ] ℝ) (C : ℝ)
    (h : ∀ d : σ → ℕ, (∑ i, d i) ≤ D → (∀ i, i ∉ S → d i = 0) →
      L (fun M => (factorialMonomial d M : ℝ)) ≤
        C * R (fun M => (factorialMonomial d M : ℝ))) :
    L (fun M => (f M : ℝ)) ≤ C * R (fun M => (f M : ℝ)) := by
  rw [F.linear_eval L, F.linear_eval R, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hd := h (F.degree j) (F.order_le j) (F.supported j)
  have hc : (0 : ℝ) ≤ F.coeff j := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hd hc]

end FactorialExpansion
end Problem335

end OAI
