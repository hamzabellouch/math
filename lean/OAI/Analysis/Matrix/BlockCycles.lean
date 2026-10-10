import Mathlib
import OAI.Analysis.Matrix.Holder

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.BlockCycles
variable {Ω R : Type*} [Fintype Ω] [DecidableEq Ω] [Semiring R]

def tupleSplit (n : ℕ) : (Fin (n+1) → Ω) ≃ Ω × (Fin n → Ω) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv x := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv x := by cases x; rfl

omit [DecidableEq Ω] in
lemma sum_tuple_split {S : Type*} [AddCommMonoid S] (n : ℕ) (f : (Fin (n+1) → Ω) → S) :
    ∑ x, f x=∑ a, ∑ x : Fin n → Ω, f (Fin.cons a x) := by
  rw [← Equiv.sum_comp (tupleSplit (Ω := Ω) n).symm]
  exact Fintype.sum_prod_type _

def walk {n : ℕ} (A : Fin n → Matrix Ω Ω R) (x : Fin (n+1) → Ω) : R :=
  (List.ofFn (fun i => A i (x i.castSucc) (x i.succ))).prod

omit [Fintype Ω] [DecidableEq Ω] in
lemma walk_succ {n : ℕ} (A : Fin (n+1) → Matrix Ω Ω R) (x : Fin (n+2) → Ω) :
    walk A x=A 0 (x 0) (x 1)*walk (fun i => A i.succ) (fun i => x i.succ) := by
  rw [walk,List.ofFn_succ,List.prod_cons]
  rfl

omit [Fintype Ω] [DecidableEq Ω] in
lemma snoc_cons {n : ℕ} (x : Fin n → Ω) (i j : Ω) :
    Fin.snoc (α := fun _ => Ω) (Fin.cons i x) j=Fin.cons i (Fin.snoc (α := fun _ => Ω) x j) := by
  funext k
  refine Fin.lastCases ?_ (fun l => ?_) k
  · simp
  · cases l using Fin.cases with
    | zero => simp
    | succ l =>
        simp only [Fin.snoc_castSucc,Fin.cons_succ]
        rw [← Fin.succ_castSucc,Fin.cons_succ,Fin.snoc_castSucc]

/- Complete matrix product expansion by paths, with the endpoint checked rather
than divided out. Valid for any noncommutative semiring of blocks. -/
lemma product_entry {n : ℕ} (A : Fin n → Matrix Ω Ω R) (i j : Ω) :
    ((List.ofFn A).prod) i j=
      ∑ x : Fin n → Ω, if (Fin.snoc (α := fun _ => Ω) x j) 0=i then walk A (Fin.snoc (α := fun _ => Ω) x j) else 0 := by
  induction n generalizing i j with
  | zero =>
    simp [walk,Matrix.one_apply,Fin.snoc_zero,eq_comm]
  | succ n ih =>
    rw [List.ofFn_succ,List.prod_cons,Matrix.mul_apply,sum_tuple_split]
    have hr : (∑ u : Ω, ∑ x : Fin n → Ω,
        if (Fin.snoc (α := fun _ => Ω) (Fin.cons u x) j) 0=i then walk A (Fin.snoc (α := fun _ => Ω) (Fin.cons u x) j) else 0)=
          ∑ x : Fin n → Ω, walk A (Fin.snoc (α := fun _ => Ω) (Fin.cons i x) j) := by
      rw [Finset.sum_eq_single i]
      · simp only [snoc_cons,Fin.cons_zero,ite_true]
      · intro u _ hu
        simp [hu]
      · simp
    rw [hr]
    simp only [ih,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [snoc_cons,walk_succ]
    simp only [Fin.cons_zero,Fin.cons_one,Fin.cons_succ]
    rw [Finset.sum_eq_single ((Fin.snoc (α := fun _ => Ω) x j) 0)]
    · simp
    · intro u _ hu
      simp [Ne.symm hu]
    · simp

omit [Fintype Ω] [DecidableEq Ω] in
lemma snoc_cycle {n : ℕ} (x : Fin (n+1) → Ω) (i : Fin (n+1)) :
    Fin.snoc (α := fun _ => Ω) x (x 0) i.succ=x (i+1) := by
  cases i using Fin.lastCases with
  | last => simp
  | cast i =>
    have he : i.castSucc+1=i.succ := by
      apply Fin.ext
      exact Fin.val_add_one_of_lt (Fin.castSucc_lt_last i)
    rw [he]
    rw [Fin.succ_castSucc]
    exact Fin.snoc_castSucc (α := fun _ => Ω) (x 0) x i.succ

/- Exact cyclic trace expansion, also when entries themselves are matrices. -/
theorem trace_product {n : ℕ} (A : Fin (n+1) → Matrix Ω Ω R) :
    Matrix.trace ((List.ofFn A).prod)=
      ∑ x : Fin (n+1) → Ω, (List.ofFn (fun i => A i (x i) (x (i+1)))).prod := by
  unfold Matrix.trace Matrix.diag
  simp_rw [product_entry]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (x 0)]
  · rw [show (Fin.snoc (α := fun _ => Ω) x (x 0)) 0=x 0 from Fin.snoc_castSucc (α := fun _ => Ω) (x 0) x (0 : Fin (n+1)),ite_eq_left rfl]
    unfold walk
    congr 2
    funext i
    rw [Fin.snoc_castSucc,snoc_cycle]
  · intro i _ hi
    have he : (Fin.snoc (α := fun _ => Ω) x i) 0=x 0 := by exact Fin.snoc_castSucc (α := fun _ => Ω) i x (0 : Fin (n+1))
    rw [he,ite_eq_right (Ne.symm hi)]
  · simp

end CoordinateSweeps.BlockCycles

namespace CoordinateSweeps.BlockCycles
variable {Ω n R : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype n] [DecidableEq n] [Semiring R]

def block (A : Matrix (Ω × n) (Ω × n) R) : Matrix Ω Ω (Matrix n n R) :=
  Matrix.of fun y x => Matrix.of fun i j => A (y,i) (x,j)

/- Literal placement blocks, with no normalized trace convention. -/
def blocks : Matrix (Ω × n) (Ω × n) R →+* Matrix Ω Ω (Matrix n n R) where
  toFun := block
  map_one' := by
    ext y x i j
    change (if (y,i)=(x,j) then (1 : R) else 0)=
      (if y=x then (1 : Matrix n n R) else 0) i j
    by_cases h : y=x <;> by_cases h' : i=j <;> simp [h,h',Matrix.one_apply]
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' A B := by
    ext y x i j
    have hh : (block A*block B) y x=∑ z, block A y z*block B z x := Matrix.mul_apply ..
    change (A*B) (y,i) (x,j)=(block A*block B) y x i j
    rw [hh]
    simp only [Matrix.mul_apply,Matrix.sum_apply]
    exact Fintype.sum_prod_type _

@[simp] lemma blocks_apply (A : Matrix (Ω × n) (Ω × n) R) (x y : Ω) (i j : n) :
    blocks A y x i j=A (y,i) (x,j) := rfl

lemma trace_blocks (A : Matrix (Ω × n) (Ω × n) R) :
    Matrix.trace A=Matrix.trace (Matrix.trace (blocks A)) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.sum_apply,blocks_apply]
  rw [Fintype.sum_prod_type,Finset.sum_comm]

/- Exact placement-cycle expansion of a product of operators on placement fibers. -/
theorem trace_block_product {m : ℕ} [NeZero m] (hm : 0 < m)
    (A : Fin m → Matrix (Ω × n) (Ω × n) R) :
    Matrix.trace (List.ofFn A).prod=
      ∑ x : Fin m → Ω, Matrix.trace (List.ofFn (fun i => blocks (A i) (x i) (x (i+1)))).prod := by
  cases m with
  | zero => omega
  | succ m =>
    rw [trace_blocks,map_list_prod]
    simp only [List.map_ofFn]
    rw [trace_product,Matrix.trace_sum]
    rfl

end CoordinateSweeps.BlockCycles

namespace CoordinateSweeps.BlockCycles
open TraceHolder
variable {Ω n : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype n] [DecidableEq n] [Nonempty n]

/- Trace Holder applied separately on every literal placement cycle. -/
theorem trace_block_holder {m : ℕ} [NeZero m] (hm : 0 < m)
    (A : Fin m → Matrix (Ω × n) (Ω × n) ℂ) :
    ‖Matrix.trace (List.ofFn A).prod‖ ≤
      ∑ x : Fin m → Ω, ∏ i, schatten m (blocks (A i) (x i) (x (i+1))) := by
  rw [trace_block_product hm]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => matrix_trace_holder hm _)

/- The exact alternating word for the unnormalized even moment. -/
def evenWord (q : ℕ) (A : Matrix (Ω × n) (Ω × n) ℂ) : List (Matrix (Ω × n) (Ω × n) ℂ) :=
  (List.replicate q [A.conjTranspose,A]).flatten

omit [Fintype Ω] [DecidableEq Ω] [Fintype n] [DecidableEq n] [Nonempty n] in
lemma evenWord_length (q : ℕ) (A : Matrix (Ω × n) (Ω × n) ℂ) :
    (evenWord q A).length=2*q := by
  simp [evenWord,Nat.mul_comm]

omit [Nonempty n] in
lemma evenWord_prod (q : ℕ) (A : Matrix (Ω × n) (Ω × n) ℂ) :
    (evenWord q A).prod=(A.conjTranspose*A)^q := by
  induction q with
  | zero => simp [evenWord]
  | succ q ih =>
    change ([A.conjTranspose,A]++evenWord q A).prod=_
    simp only [List.prod_append,List.prod_cons,List.prod_nil,mul_one,ih,pow_succ']

omit [Fintype Ω] [DecidableEq Ω] [Fintype n] [DecidableEq n] [Nonempty n] in
lemma evenWord_mem (q : ℕ) (A : Matrix (Ω × n) (Ω × n) ℂ) {B : Matrix (Ω × n) (Ω × n) ℂ}
    (h : B ∈ evenWord q A) : B=A.conjTranspose ∨ B=A := by
  obtain ⟨l,hl,hm⟩ := List.mem_flatten.mp h
  have he : l=[A.conjTranspose,A] := (List.mem_replicate.mp hl).2
  simpa [he] using hm

/- Literal cyclic index expansion of the induced even moment, before probabilities
and augmented path potentials are substituted. -/
theorem even_moment_blocks (q : ℕ) (hq : 0 < q) (A : Matrix (Ω × n) (Ω × n) ℂ) :
    let L := evenWord q A
    letI : NeZero L.length := ⟨by rw [evenWord_length]; omega⟩
    (Matrix.trace ((A.conjTranspose*A)^q)).re ≤
      ∑ x : Fin L.length → Ω, ∏ i, schatten (2*q) (blocks (L.get i) (x i) (x (i+1))) := by
  let L := evenWord q A
  have hL : 0 < L.length := by dsimp [L]; rw [evenWord_length]; omega
  let : NeZero L.length := ⟨by omega⟩
  have hh := trace_block_holder hL (fun i => L.get i)
  rw [List.ofFn_get] at hh
  have hl : L.length=2*q := evenWord_length q A
  have he : (∑ x : Fin L.length → Ω, ∏ i, schatten L.length (blocks (L.get i) (x i) (x (i+1))))=
      ∑ x : Fin L.length → Ω, ∏ i, schatten (2*q) (blocks (L.get i) (x i) (x (i+1))) := by
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (fun m => schatten m (blocks (L.get i) (x i) (x (i+1)))) hl
  rw [he] at hh
  have hp : L.prod=(A.conjTranspose*A)^q := evenWord_prod q A
  rw [hp] at hh
  exact (Complex.re_le_norm _).trans hh

end CoordinateSweeps.BlockCycles

namespace CoordinateSweeps.BlockCycles
open TraceHolder
variable {Ω n : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype n] [DecidableEq n] [Nonempty n]

def edgeWeight (A B : Matrix (Ω × n) (Ω × n) ℂ) (p : Ω → Ω → ℝ) (y x : Ω) : ℝ :=
  if B=A then p y x else p x y

def edgeFiber (A B : Matrix (Ω × n) (Ω × n) ℂ)
    (K : Ω → Ω → Matrix n n ℂ) (y x : Ω) : Matrix n n ℂ :=
  if B=A then K y x else (K x y).conjTranspose

omit [Nonempty n] in
lemma block_adjoint (A : Matrix (Ω × n) (Ω × n) ℂ) (y x : Ω) :
    blocks A.conjTranspose y x=(blocks A x y).conjTranspose := by ext i j; rfl

omit [Nonempty n] in
lemma edge_block (A B : Matrix (Ω × n) (Ω × n) ℂ) (p : Ω → Ω → ℝ)
    (K : Ω → Ω → Matrix n n ℂ) (hA : ∀ y x, blocks A y x=(p y x : ℂ) • K y x)
    (hB : B=A.conjTranspose ∨ B=A) (y x : Ω) :
    blocks B y x=(edgeWeight A B p y x : ℂ) • edgeFiber A B K y x := by
  by_cases h : B=A
  · simp only [edgeWeight,edgeFiber,h]
    exact hA y x
  · obtain hb | hb := hB
    · subst B
      rw [edgeWeight,edgeFiber,ite_eq_right h,ite_eq_right h,block_adjoint,hA,
        Matrix.conjTranspose_smul]
      simp
    · exact (h hb).elim

omit [DecidableEq Ω] [DecidableEq n] [Nonempty n] in
lemma edgeWeight_nonneg (A B : Matrix (Ω × n) (Ω × n) ℂ) (p : Ω → Ω → ℝ)
    (hp : ∀ y x, 0 ≤ p y x) (y x : Ω) : 0 ≤ edgeWeight A B p y x := by
  unfold edgeWeight
  split_ifs <;> apply hp

/- Each placement cycle carries exactly the transition probabilities of its
forward or adjoint edges and the unnormalized conditional fiber moments. -/
theorem even_cycle_bound (q : ℕ) (hq : 0 < q) (A : Matrix (Ω × n) (Ω × n) ℂ)
    (p : Ω → Ω → ℝ) (hp : ∀ y x, 0 ≤ p y x) (K : Ω → Ω → Matrix n n ℂ)
    (hA : ∀ y x, blocks A y x=(p y x : ℂ) • K y x) :
    let L := evenWord q A
    letI : NeZero L.length := ⟨by rw [evenWord_length]; omega⟩
    (Matrix.trace ((A.conjTranspose*A)^q)).re ≤
      ∑ x : Fin L.length → Ω,
        (∏ i, edgeWeight A (L.get i) p (x i) (x (i+1))) *
        ∏ i, (Matrix.trace (((edgeFiber A (L.get i) K (x i) (x (i+1))).conjTranspose*
          edgeFiber A (L.get i) K (x i) (x (i+1)))^q)).re ^ ((2*q : ℝ)⁻¹) := by
  let L := evenWord q A
  let : NeZero L.length := ⟨by dsimp [L]; rw [evenWord_length]; omega⟩
  refine (even_moment_blocks q hq A).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro i _
    exact schatten_nonneg _ _
  · intro i _
    have hB := evenWord_mem q A (List.get_mem L i)
    rw [edge_block A (L.get i) p K hA hB]
    have he := schatten_even_smul_le q hq
      (edgeWeight A (L.get i) p (x i) (x (i+1)) : ℂ)
      (edgeFiber A (L.get i) K (x i) (x (i+1)))
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (edgeWeight_nonneg A (L.get i) p hp _ _)] at he
    simpa only [schatten_even_eq] using he

end CoordinateSweeps.BlockCycles
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
