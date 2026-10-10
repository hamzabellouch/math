import OAI.Computability.SpaceSimulation.Evaluation.Field
import OAI.Computability.SpaceSimulation.Register.Digits

namespace OAI

namespace Fifths
namespace Modulus
variable (P : Modulus)
open Polynomial Finset

-- Use weights over the whole field (simpler than general Lagrange
-- weights). Enumerate by residue code.
theorem sum_code (f : P.K → P.K) :
    ∑ i ∈ range P.n, f (i : P.K) = ∑ x : P.K, f x := by
  classical
  refine sum_bij (fun a _ => (a : P.K)) ?_ ?_ ?_ ?_
  · simp
  · intro a i b j h
    exact (ZMod.val_natCast_of_lt (mem_range.mp i)).symm.trans
      ((congrArg ZMod.val h).trans (ZMod.val_natCast_of_lt (mem_range.mp j)))
  · intro b _
    exact ⟨b.val,mem_range.mpr b.val_lt,ZMod.natCast_zmod_val b⟩
  · simp

theorem sum_at_top : ∑ x : P.K, x ^ (P.n-1) = -1 := by
  classical
  have h (x : P.K) : x ^ (P.n-1) = 1 - if x = 0 then 1 else 0 := by
    by_cases g : x = 0
    · subst x; have a := P.bound; simp [show P.n-1 ≠ 0 by omega]
    · simp [ZMod.pow_card_sub_one_eq_one g,g]
  simp [h,sum_sub_distrib,K,ZMod.card]

theorem dot_mono {d i : ℕ} (p : d+1 < P.n) (l : i ≤ d) :
    ∑ x : P.K, P.weight d x * x ^ i = if d=i then 1 else 0 := by
  simp_rw [weight, neg_mul, ← pow_add, sum_neg_distrib]
  by_cases e : d = i
  · rw [ite_eq_left e, show P.n-1-d+i = P.n-1 by omega,P.sum_at_top]
    simp
  rw [ite_eq_right e, FiniteField.sum_pow_lt_card_sub_one]
  · simp
  · change P.n-1-d+i < Fintype.card (ZMod P.n) - 1
    rw [ZMod.card]
    omega

theorem extract {d} (g : Polynomial P.K) (o : g.natDegree ≤ d)
    (h : d+1 < P.n) :
    (∑ i ∈ range P.n, P.weight d (i : P.K) * g.eval (i : P.K)) =
      g.coeff d := by
  rw [P.sum_code (fun x => P.weight d x * g.eval x)]
  have hg : g.natDegree < d+1 := Nat.lt_succ_of_le o
  calc
    _ = ∑ i ∈ range (d+1), g.coeff i * (∑ x : P.K, P.weight d x*x^i) := by
      simp_rw [eval_eq_sum_range' hg,mul_sum]
      rw [sum_comm]
      simp [mul_left_comm]
    _ = ∑ i ∈ range (d+1), g.coeff i * (if d=i then 1 else 0) := by
      refine sum_congr rfl (fun i l => ?_)
      rw [dot_mono P h (Nat.le_of_lt_succ (mem_range.mp l))]
    _ = _ := by simp

/-- `Line d f v`: f fits a low-degree polynomial with coefficient v at d. -/
def Line (d : ℕ) (f : P.K → P.K) (v : P.K) : Prop :=
  ∃ g : Polynomial P.K, g.natDegree ≤ d ∧ g.coeff d = v ∧ ∀ x, g.eval x = f x

namespace Line
variable {P} {d m : ℕ} {f g : P.K → P.K} {u v : P.K}
theorem congr (r : P.Line d f u) (o : ∀ i, f i = g i) (a : u = v) :
    P.Line d g v := funext o ▸ a ▸ r
theorem zero (P : Modulus) (d : ℕ) : P.Line d (fun _ => 0) 0 := by
  exact ⟨0,by simp⟩
theorem constant (u : P.K) : P.Line 0 (fun _ => u) u := by
  exact ⟨C u,by simp⟩
theorem lin (a b : P.K) : P.Line 1 (fun x => a+x*b) b := by
  refine ⟨C b * X + C a, natDegree_linear_le, ?_⟩
  constructor
  · simp
  · intro x; simp only [eval_add,eval_mul,eval_C,eval_X]; ring
theorem mul (p : P.Line d f u) (q : P.Line m g v) :
    P.Line (d+m) (fun x => f x * g x) (u*v) := by
  obtain ⟨a,h,r,l⟩ := p
  obtain ⟨b,i,s,t⟩ := q
  exact ⟨a*b,natDegree_mul_le_of_le h i,
    by rw [coeff_mul_add_eq_of_natDegree_le h i,r,s], by simp [l,t]⟩
theorem kMul (h : P.Line d f u) (v : P.K) : P.Line d (fun x => f x*v) (u*v) :=
  h.mul (constant v)
theorem add (p : P.Line d f u) (q : P.Line d g v) :
    P.Line d (fun x => f x + g x) (u+v) := by
  obtain ⟨a,h,r,l⟩ := p
  obtain ⟨b,i,s,t⟩ := q
  exact ⟨a+b,natDegree_add_le_of_degree_le h i,by simp [r,s],by simp [l,t]⟩
theorem sub (p : P.Line d f u) (q : P.Line d g v) :
    P.Line d (fun x => f x - g x) (u-v) := by
  obtain ⟨b,i,s,t⟩ := q
  have e : P.Line d (fun x => -g x) (-v) :=
    ⟨-b,by simp_all⟩
  simpa only [sub_eq_add_neg] using p.add e

theorem sums {f : ℕ → P.K → P.K} {v : ℕ → P.K} (n : ℕ)
    (p : ∀ i, P.Line d (f i) (v i)) :
    P.Line d (fun x => ∑ i ∈ range n, f i x) (∑ i ∈ range n, v i) := by
  induction n with
  | zero => simpa using Line.zero P d
  | succ n ih => simpa [sum_range_succ] using ih.add (p n)
theorem prods {f : ℕ → P.K → P.K} {v : ℕ → P.K} (n : ℕ)
    (p : ∀ i, P.Line d (f i) (v i)) :
    P.Line (n*d) (fun x => ∏ i ∈ range n, f i x) (∏ i ∈ range n, v i) := by
  induction n with
  | zero => simpa using (Line.constant (1 : P.K))
  | succ n ih => simpa [prod_range_succ,add_mul] using ih.mul (p n)

theorem evaluate (p : P.Line d f u) (h : d+1 < P.n) :
    (∑ i ∈ range P.n, P.weight d (i : P.K) * f (i : P.K)) = u := by
  obtain ⟨r,l,a,b⟩ := p
  simp_rw [← b, extract P r l h,a]
end Line

open Radix

/-- Vec is allowed to have "ghost" coordinates above the finite width.
Every packed access uses just first d+1 coordinates. Gives less
cast-burdened proofs about loops. The actual registers store only the
charged coordinates. -/
abbrev Vec := ℕ → P.K

def augBit (d u i : ℕ) : ℕ :=
  if i < d then get 2 u i else if i=d then 1 else 0

def aug (d u : ℕ) : P.Vec := fun i => augBit d u i

def chooseCoord (d u : ℕ) (v : P.Vec) (i : ℕ) : P.K :=
  if get 2 u i = 1 then v i else v d - v i

def basis (d u : ℕ) (v : P.Vec) : P.K :=
  ∏ i ∈ range d, P.chooseCoord d u v i

/-- Single fully augmented Boolean-word lookup. Compute
word-valued rules coordinate by coordinate this way. -/
def extWord (d : ℕ) (f : ℕ → P.K) (v : P.Vec) : P.K :=
  ∑ u ∈ range (2^d), P.basis d u v * f u
def extTwo (d : ℕ) (f : ℕ → ℕ → P.K) (v w : P.Vec) : P.K :=
  P.extWord d (fun u => P.extWord d (f u) w) v

def shift (v w : P.Vec) (x : P.K) : P.Vec := fun i => v i + x*w i

theorem basis_kronecker (d u w : ℕ) (a : u < 2^d) (b : w < 2^d) :
    P.basis d u (P.aug d w) = if u=w then 1 else 0 := by
  have h (i : ℕ) (l : i < d) :
      P.chooseCoord d u (P.aug d w) i =
        if get 2 u i = get 2 w i then 1 else 0 := by
    have q (a : ℕ) : get 2 a i = 1 ∨ get 2 a i = 0 := by
      have := get_lt (m := 2) (by omega) a i
      omega
    cases q u with
    | inl t => simp [chooseCoord,t,aug,augBit,l]; rcases q w with t|t <;> simp [t]
    | inr t => rcases q w with r|r <;> simp [chooseCoord,t,r,aug,augBit,l]
  by_cases p : u=w
  · unfold basis
    rw [ite_eq_left p]
    apply prod_eq_one
    exact fun i l => by rw [h i (mem_range.mp l),p]; simp
  · have s : ∃ i < d, get 2 u i ≠ get 2 w i := by
      by_contra! e
      exact p (Radix.ext (by omega) a b e)
    obtain ⟨i,l,m⟩ := s
    unfold basis
    rw [ite_eq_right p]
    exact prod_eq_zero (mem_range.mpr l) (by simp [h i l,m])

theorem extWord_aug (d : ℕ) (f : ℕ → P.K) (u : ℕ) (h : u<2^d) :
    P.extWord d f (P.aug d u) = f u := by
  unfold extWord
  rw [sum_eq_single_of_mem u (mem_range.mpr h)]
  · simp [P.basis_kronecker d u u h h]
  · intro v l e; simp [P.basis_kronecker d v u (mem_range.mp l) h,e]

theorem extTwo_aug (d : ℕ) (f : ℕ → ℕ → P.K) (u v : ℕ) (h : u < 2^d) (g : v < 2^d) :
    P.extTwo d f (P.aug d u) (P.aug d v) = f u v := by simp [extTwo,extWord_aug,h,g]

theorem basis_shift (d u : ℕ) (v w : P.Vec) :
    P.Line d (fun x => P.basis d u (P.shift v w x)) (P.basis d u w) := by
  suffices h : ∀ i, P.Line 1 (fun x => P.chooseCoord d u (P.shift v w x) i)
      (P.chooseCoord d u w i) from by simpa [basis] using Line.prods d h
  intro i
  unfold chooseCoord
  split_ifs
  · exact Line.lin _ _
  · exact (Line.lin _ _).sub (Line.lin _ _)

theorem extWord_shift (d : ℕ) (f : ℕ → P.K) (v w : P.Vec) :
    P.Line d (fun x => P.extWord d f (P.shift v w x)) (P.extWord d f w) :=
  Line.sums _ (fun i => Line.kMul (P.basis_shift _ _ v w) (f i))

theorem extTwo_shiftF (d : ℕ) (f : ℕ → ℕ → P.K) (u v w : P.Vec) :
    P.Line d (fun x => P.extTwo d f (P.shift u v x) w) (P.extTwo d f v w) :=
  P.extWord_shift d _ u v
theorem extTwo_shiftS (d : ℕ) (f : ℕ → ℕ → P.K) (u v w : P.Vec) :
    P.Line d (fun x => P.extTwo d f u (P.shift v w x)) (P.extTwo d f u w) := by
  have h (i : ℕ) :
      P.Line d (fun x => P.basis d i u * P.extWord d (f i) (P.shift v w x))
        (P.basis d i u * P.extWord d (f i) w) := by
    simpa only [mul_comm (P.basis d i u)]
      using Line.kMul (P.extWord_shift d (f i) v w) (P.basis d i u)
  exact Line.sums _ h
end Modulus
end Fifths

end OAI
