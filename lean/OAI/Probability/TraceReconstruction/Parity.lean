import Mathlib

namespace OAI

/-!
# Parity

Parity-tree roles, forced leaves, coefficient shapes, and exact unsigned/signed motif expansions.
-/

open scoped ENNReal
noncomputable section

namespace TraceReconstruction

/-- Three roles of an active odd child in the manuscript parity expansion:
constant, unsigned motif, and signed motif. -/
def roleWeight (χ σ : ℝ) (r : Fin 3) : ℝ :=
  if r=0 then 1 else if r=1 then -χ else σ

def signedRoleCount {n : ℕ} (r : Fin n → Fin 3) : ℕ :=
  (Finset.univ.filter fun i => r i=2).card

def activeRoleCount {n : ℕ} (r : Fin n → Fin 3) : ℕ :=
  (Finset.univ.filter fun i => r i≠0).card

theorem role_product_expansion {n : ℕ} (χ σ : Fin n → ℝ) (τ : ℝ) :
    (∏ i : Fin n, (1 - χ i + σ i * τ)) =
      ∑ r : Fin n → Fin 3, (∏ i, roleWeight (χ i) (σ i) (r i)) * τ^signedRoleCount r := by
  have hp (r : Fin n → Fin 3) : ∏ i, (if r i=2 then τ else (1:ℝ)) = τ^signedRoleCount r := by
    rw [← Finset.prod_filter]
    simp only [Finset.prod_const, signedRoleCount]
  simp_rw [← hp, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin n) (r : Fin 3) => roleWeight (χ i) (σ i) r * (if r=2 then τ else 1))]
  apply Finset.prod_congr rfl
  intro i _
  simp [Fin.sum_univ_three, roleWeight]
  ring

theorem odd_role_difference {n : ℕ} (χ σ : Fin n → ℝ) :
    (∏ i : Fin n, (1 - χ i + σ i)) - (∏ i : Fin n, (1 - χ i - σ i)) =
      2*∑ r : Fin n → Fin 3,
        if Odd (signedRoleCount r) then ∏ i, roleWeight (χ i) (σ i) (r i) else 0 := by
  have hplus := role_product_expansion χ σ 1
  have hminus := role_product_expansion χ σ (-1)
  simp only [mul_one, one_pow] at hplus
  simp only [mul_neg_one, ← sub_eq_add_neg] at hminus
  rw [hplus,hminus, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : Odd (signedRoleCount r)
  · rw [ite_eq_left hr, hr.neg_one_pow]
    ring
  · have he : Even (signedRoleCount r) := Nat.not_odd_iff_even.mp hr
    rw [ite_eq_right hr, he.neg_one_pow]
    ring

theorem signedRoleCount_le_active {n : ℕ} (r : Fin n → Fin 3) :
    signedRoleCount r ≤ activeRoleCount r := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  rw [hi]
  decide

/-- A surviving odd node either has a unique active signed motif (the
local high-order cancellation case), or at least two active children. -/
theorem odd_roles_singleton_or_branch {n : ℕ} (r : Fin n → Fin 3)
    (hodd : Odd (signedRoleCount r)) :
    (∃ i, r i=2 ∧ ∀ j, j≠i → r j=0) ∨ 2 ≤ activeRoleCount r := by
  have hpos : 0 < signedRoleCount r := hodd.pos
  have hle := signedRoleCount_le_active r
  by_cases h : 2 ≤ activeRoleCount r
  · exact Or.inr h
  have ha : activeRoleCount r=1 := by omega
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp ha
  have hmem : ∀ j, r j≠0 ↔ j=i := by
    intro j
    have he := Finset.ext_iff.mp hi j
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] using he
  have hs : ∃ j, r j=2 := by
    have hs0 : (Finset.univ.filter fun j => r j=2).Nonempty := Finset.card_pos.mp hpos
    obtain ⟨j,hj⟩ := hs0
    exact ⟨j, (Finset.mem_filter.mp hj).2⟩
  obtain ⟨j,hj⟩ := hs
  have hij := (hmem j).mp (by rw [hj]; decide)
  subst j
  exact Or.inl ⟨i,hj,fun j hji => Classical.byContradiction (fun hn => hji ((hmem j).mp hn))⟩

/-- Finite occupied trees with at least two continuing odd children at
each positive depth. This records exactly the no-singleton branch of
the parity argument; the arity and all extra children remain arbitrary. -/
inductive BranchingTree : ℕ → Type
  | leaf : BranchingTree 0
  | node {b : ℕ} (n : ℕ) (children : Fin n → BranchingTree b) (branch : 2 ≤ n) : BranchingTree (b+1)

def BranchingTree.leafCount : {b : ℕ} → BranchingTree b → ℕ
  | _, .leaf => 1
  | _, .node _ children _ => ∑ i, (children i).leafCount

def BranchingTree.levelCount : {b : ℕ} → BranchingTree b → ℕ → ℕ
  | _, .leaf, h => if h=0 then 1 else 0
  | _, .node _ children _, h => if h=0 then 1 else ∑ i, (children i).levelCount (h-1)

theorem BranchingTree.leafCount_lower {b : ℕ} (t : BranchingTree b) :
    2^b ≤ t.leafCount := by
  induction t with
  | leaf => simp [leafCount]
  | @node b n children hn ih =>
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => ih i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
    have hmul := Nat.mul_le_mul_right (2^b) hn
    simp only [leafCount]
    rw [pow_succ]
    omega



/-- A term in the parity expansion retains the occupied ordered shape,
all roles, and all extra children, rather than assuming it is binary. -/
inductive OccupiedParityTree : ℕ → Type
  | leaf : OccupiedParityTree 0
  | node {b : ℕ} (n : ℕ) (children : Fin n → OccupiedParityTree b)
      (roles : Fin n → Fin 3) : OccupiedParityTree (b+1)

def OccupiedParityTree.isOdd : {b : ℕ} → OccupiedParityTree b → Prop
  | _, .leaf => True
  | _, .node _ _ roles => Odd (signedRoleCount roles)

def OccupiedParityTree.leafCount : {b : ℕ} → OccupiedParityTree b → ℕ
  | _, .leaf => 1
  | _, .node _ children _ => ∑ i, (children i).leafCount

/-- Only odd-role child terms may acquire an active parent multiplier. -/
def OccupiedParityTree.valid : {b : ℕ} → OccupiedParityTree b → Prop
  | _, .leaf => True
  | _, .node _ children roles =>
      (∀ i, roles i ≠ 0 → (children i).isOdd) ∧ ∀ i, (children i).valid

def OccupiedParityTree.noSingleton : {b : ℕ} → OccupiedParityTree b → Prop
  | _, .leaf => True
  | _, .node _ children roles =>
      (Odd (signedRoleCount roles) → activeRoleCount roles ≠ 1) ∧
        ∀ i, (children i).noSingleton

/-- The exact forced binary number of selected leaves, with all extra
occupied vertices present. The hypotheses here are checked properties
of a parity term, not a statistical or construction theorem. -/
theorem OccupiedParityTree.forced_leaves {b : ℕ} (t : OccupiedParityTree b)
    (hv : t.valid) (hn : t.noSingleton) (ho : t.isOdd) : 2^b ≤ t.leafCount := by
  induction t with
  | leaf => simp [leafCount]
  | @node b n children roles ih =>
    have hod : Odd (signedRoleCount roles) := ho
    have hpos := hod.pos
    have hle := signedRoleCount_le_active roles
    have hne := hn.1 hod
    have ha : 2 ≤ activeRoleCount roles := by omega
    have hsum : (∑ i : Fin n, if roles i≠0 then 2^b else 0) ≤
        ∑ i : Fin n, (children i).leafCount := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · exact ih i (hv.2 i) (hn.2 i) (hv.1 i hi)
      · exact Nat.zero_le _
    have hs : (∑ i : Fin n, if roles i≠0 then 2^b else 0) = activeRoleCount roles * 2^b := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, smul_eq_mul, activeRoleCount]
    rw [hs] at hsum
    change 2^(b+1) ≤ _
    rw [pow_succ]
    exact (show 2^b*2 ≤ activeRoleCount roles*2^b by
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_right (2^b) ha).trans hsum

end TraceReconstruction

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
attribute [local instance] Classical.propDecidable

/-- The literal unsigned/signed motif values at one child index. -/
def IsMotifValue (χ σ : ℝ) : Prop :=
  (χ=0 ∧ σ=0) ∨ (χ=1 ∧ (σ=1 ∨ σ= -1))

def IsTypeSign (τ : ℝ) : Prop := τ=1 ∨ τ= -1

theorem motif_child_sign {χ σ τ : ℝ} (hm : IsMotifValue χ σ) (ht : IsTypeSign τ) :
    IsTypeSign (1-χ+σ*τ) := by
  rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,hσ⟩
  · exact Or.inl (by ring)
  · rcases hσ with rfl | rfl <;> rcases ht with rfl | rfl <;>
      norm_num [IsTypeSign]

theorem sign_pow_parity {τ : ℝ} (ht : IsTypeSign τ) (n : ℕ) :
    τ^n = if Odd n then τ else 1 := by
  rcases ht with rfl | rfl
  · simp
  · split_ifs with hn
    · exact hn.neg_one_pow
    · exact (Nat.not_odd_iff_even.mp hn).neg_one_pow

/-- Product expansion with an arbitrary three-role scalar per child; the
only sign variable is the current vertex type. -/
theorem arbitrary_role_expansion {n : ℕ} (w : Fin n → Fin 3 → ℝ) (τ : ℝ) :
    (∏ i, ∑ a : Fin 3, w i a * (if a=2 then τ else 1)) =
      ∑ a : Fin n → Fin 3, (∏ i, w i (a i))*τ^signedRoleCount a := by
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ,Finset.prod_mul_distrib]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [← Finset.prod_filter]
  simp [signedRoleCount]

/-- At the last internal level every selected leaf has to be active.
Role zero has weight zero; unsigned and signed roles are respectively
χ/2 and -σ/2 in (χ-στ)/2. -/
def bottomRoleWeight (χ σ : ℝ) (a : Fin 3) : ℝ :=
  if a=0 then 0 else if a=1 then χ/2 else -σ/2

def internalRoleWeight (odd : Prop) [Decidable odd] (χ σ : ℝ) (a : Fin 3) : ℝ :=
  if odd then roleWeight χ σ a else if a=0 then 1 else 0

theorem bottomRole_sum (χ σ τ : ℝ) :
    (∑ a : Fin 3, bottomRoleWeight χ σ a*(if a=2 then τ else 1)) = (χ-σ*τ)/2 := by
  rw [Fin.sum_univ_three]
  have h01 : (0:Fin 3) ≠ 1 := by decide
  have h02 : (0:Fin 3) ≠ 2 := by decide
  have h12 : (1:Fin 3) ≠ 2 := by decide
  simp only [bottomRoleWeight,h02,h12,Ne.symm h01,Ne.symm h02,Ne.symm h12,
    ↓reduceIte,zero_add,mul_one]
  ring

theorem internalRole_sum (odd : Prop) [Decidable odd] (χ σ τ : ℝ) :
    (∑ a : Fin 3, internalRoleWeight odd χ σ a*(if a=2 then τ else 1)) =
      if odd then 1-χ+σ*τ else 1 := by
  rw [Fin.sum_univ_three]
  have h01 : (0:Fin 3) ≠ 1 := by decide
  have h02 : (0:Fin 3) ≠ 2 := by decide
  have h12 : (1:Fin 3) ≠ 2 := by decide
  by_cases h : odd <;> simp only [internalRoleWeight,roleWeight,h,h02,h12,
    Ne.symm h01,Ne.symm h02,Ne.symm h12,↓reduceIte,zero_mul,add_zero,mul_one]
  ring

/-- An arbitrary occupied ordered subtree, with motif values at its actual
child labels. Depth zero here means a bottom sibling group, so it already
has one internal level. No binary-shape assumption is made. -/
inductive CoefficientShape : ℕ → Type
  | bottom (n : ℕ) (χ σ : Fin n → ℝ) : CoefficientShape 0
  | node {b : ℕ} (n : ℕ) (χ σ : Fin n → ℝ)
      (children : Fin n → CoefficientShape b) : CoefficientShape (b+1)

namespace CoefficientShape

def Admissible : {b : ℕ} → CoefficientShape b → Prop
  | _, .bottom _ χ σ => ∀ i, IsMotifValue (χ i) (σ i)
  | _, .node _ χ σ children => (∀ i, IsMotifValue (χ i) (σ i)) ∧ ∀ i, (children i).Admissible

def eval : {b : ℕ} → CoefficientShape b → ℝ → ℝ
  | _, .bottom _ χ σ, τ => ∏ i, (χ i-σ i*τ)/2
  | _, .node _ χ σ children, τ => ∏ i, (children i).eval (1-χ i+σ i*τ)

def Choice : {b : ℕ} → CoefficientShape b → Type
  | _, .bottom n _ _ => Fin n → Fin 3
  | _, .node n _ _ children => ((i : Fin n) → (children i).Choice) × (Fin n → Fin 3)

noncomputable instance choiceFintype : {b : ℕ} → (t : CoefficientShape b) → Fintype t.Choice
  | _, .bottom _ _ _ => by unfold Choice; infer_instance
  | _, .node _ _ _ children => by
      letI := fun i => choiceFintype (children i)
      unfold Choice
      infer_instance

def termTree : {b : ℕ} → (t : CoefficientShape b) → t.Choice → OccupiedParityTree (b+1)
  | _, .bottom n _ _, a => .node n (fun _ => .leaf) a
  | _, .node n _ _ children, a => .node n (fun i => (children i).termTree (a.1 i)) a.2

noncomputable def weight : {b : ℕ} → (t : CoefficientShape b) → t.Choice → ℝ
  | _, .bottom _ χ σ, a => ∏ i, bottomRoleWeight (χ i) (σ i) (a i)
  | _, .node _ χ σ children, a => ∏ i,
      (children i).weight (a.1 i) *
        @internalRoleWeight ((children i).termTree (a.1 i)).isOdd (Classical.propDecidable _)
          (χ i) (σ i) (a.2 i)

/-- Full finite coefficient expansion, before any orientation average or
fit-event conditioning. This is the literal algebra behind source
the correlated-anchor estimate, the parity roles being retained in every term. -/
theorem expansion {b : ℕ} (t : CoefficientShape b) (ha : t.Admissible)
    {τ : ℝ} (ht : IsTypeSign τ) :
    t.eval τ = ∑ a : t.Choice, t.weight a * (if (t.termTree a).isOdd then τ else 1) := by
  classical
  induction t generalizing τ with
  | bottom n χ σ =>
    have H := arbitrary_role_expansion (fun i => bottomRoleWeight (χ i) (σ i)) τ
    simp_rw [bottomRole_sum,sign_pow_parity ht] at H
    trans ∑ a : Fin n → Fin 3, (∏ i, bottomRoleWeight (χ i) (σ i) (a i)) *
      (if Odd (signedRoleCount a) then τ else 1)
    · exact H
    · apply Finset.sum_congr rfl
      intro a _
      apply congrArg (fun z => (∏ i, bottomRoleWeight (χ i) (σ i) (a i))*z)
      change _ = @ite ℝ (Odd (signedRoleCount a)) (Classical.propDecidable _) τ 1
      split_ifs <;> rfl
  | @node b n χ σ children ih =>
    change (∏ i, (children i).eval (1-χ i+σ i*τ)) = _
    have he (i : Fin n) := ih i (ha.2 i) (motif_child_sign (ha.1 i) ht)
    simp_rw [he]
    rw [Finset.prod_univ_sum]
    simp only [Fintype.piFinset_univ]
    change (∑ a : (i : Fin n) → (children i).Choice,
      ∏ i, (children i).weight (a i)*
        (if ((children i).termTree (a i)).isOdd then 1-χ i+σ i*τ else 1)) =
      ∑ a : ((i : Fin n) → (children i).Choice) × (Fin n → Fin 3),
        (∏ i, (children i).weight (a.1 i)*
          internalRoleWeight ((children i).termTree (a.1 i)).isOdd (χ i) (σ i) (a.2 i))*
        (@ite ℝ (Odd (signedRoleCount a.2)) (Classical.propDecidable _) τ 1)
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    have H := arbitrary_role_expansion (fun i =>
      internalRoleWeight ((children i).termTree (a i)).isOdd (χ i) (σ i)) τ
    simp_rw [internalRole_sum,sign_pow_parity ht] at H
    rw [Finset.prod_mul_distrib,H,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a' _
    rw [Finset.prod_mul_distrib,mul_assoc]
    congr 2
    split_ifs <;> rfl

/-- Nonzero terms automatically satisfy the source active-odd rule. -/
theorem term_valid {b : ℕ} (t : CoefficientShape b) (a : t.Choice)
    (h : t.weight a ≠ 0) : (t.termTree a).valid := by
  classical
  induction t with
  | bottom n χ σ => exact ⟨fun _ _ => trivial,fun _ => trivial⟩
  | @node b n χ σ children ih =>
    have hp (i : Fin n) : (children i).weight (a.1 i) *
        internalRoleWeight ((children i).termTree (a.1 i)).isOdd (χ i) (σ i) (a.2 i) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ i)
    constructor
    · intro i hai
      by_contra hn
      have hz := (mul_ne_zero_iff.mp (hp i)).2
      simp [internalRoleWeight,hn,hai] at hz
    · intro i
      exact ih i (a.1 i) (mul_ne_zero_iff.mp (hp i)).1

/-- The difference of hypotheses consists exactly of odd root terms. -/
theorem difference_expansion {b : ℕ} (t : CoefficientShape b) (ha : t.Admissible) :
    t.eval 1-t.eval (-1) = 2*∑ a : t.Choice,
      if (t.termTree a).isOdd then t.weight a else 0 := by
  classical
  rw [expansion t ha (Or.inl rfl),expansion t ha (Or.inr rfl),
    ← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

/-- A nonzero surviving term without a singleton odd vertex has the full
forced binary number of leaves. This follows from the actual expansion,
not an assumed parity interface. -/
theorem surviving_leaves {b : ℕ} (t : CoefficientShape b) (a : t.Choice)
    (hw : t.weight a ≠ 0) (ho : (t.termTree a).isOdd)
    (hn : (t.termTree a).noSingleton) : 2^(b+1) ≤ (t.termTree a).leafCount :=
  (t.termTree a).forced_leaves (t.term_valid a hw) hn ho

end CoefficientShape
end TraceReconstruction


noncomputable section
namespace TraceReconstruction
namespace OccupiedParityTree

/-- The actual binary selection sits inside an arbitrary occupied parity
term, retaining its unselected children rather than assuming binary input. -/
inductive Forced : {b : ℕ} → OccupiedParityTree b → Type
  | leaf : Forced .leaf
  | node {b n : ℕ} {children : Fin n → OccupiedParityTree b} {roles : Fin n → Fin 3}
      (a c : Fin n) (hne : a≠c) (ha : roles a≠0) (hc : roles c≠0)
      (left : Forced (children a)) (right : Forced (children c)) :
      Forced (.node n children roles)

/-- Every surviving nonsingleton term has an embedded binary subtree.
The selection depends only on the role-marked shape. -/
theorem forced_nonempty {b : ℕ} (t : OccupiedParityTree b)
    (hv : t.valid) (hn : t.noSingleton) (ho : t.isOdd) : Nonempty t.Forced := by
  classical
  induction t with
  | leaf => exact ⟨.leaf⟩
  | @node b n children roles ih =>
    have hod : Odd (signedRoleCount roles) := ho
    have ha : 2 ≤ activeRoleCount roles := by
      have := signedRoleCount_le_active roles
      have := hod.pos
      have := hn.1 hod
      omega
    obtain ⟨a,ha,c,hc,hne⟩ := Finset.one_lt_card.mp ha
    have ha' : roles a≠0 := (Finset.mem_filter.mp ha).2
    have hc' : roles c≠0 := (Finset.mem_filter.mp hc).2
    obtain ⟨la⟩ := ih a (hv.2 a) (hn.2 a) (hv.1 a ha')
    obtain ⟨lc⟩ := ih c (hv.2 c) (hn.2 c) (hv.1 c hc')
    exact ⟨.node a c hne ha' hc' la lc⟩

/-- Occupied shapes have at least one selected leaf below every vertex. -/
def occupied : {b : ℕ} → OccupiedParityTree b → Prop
  | _, .leaf => True
  | _, .node n children _ => 0<n ∧ ∀ i, (children i).occupied

/-- Number of vertices at a given distance below the root. -/
def levelCount : {b : ℕ} → OccupiedParityTree b → ℕ → ℕ
  | _, _, 0 => 1
  | _, .leaf, _+1 => 0
  | _, .node _ children _, k+1 => ∑ i, (children i).levelCount k

theorem leafCount_pos {b : ℕ} (t : OccupiedParityTree b) (ht : t.occupied) :
    0<t.leafCount := by
  induction t with
  | leaf => exact Nat.zero_lt_one
  | @node b n children roles ih =>
    let i : Fin n := ⟨0,ht.1⟩
    have hp := ih i (ht.2 i)
    change 0 < ∑ k, (children k).leafCount
    exact hp.trans_le (Finset.single_le_sum (fun k _ => Nat.zero_le ((children k).leafCount)) (Finset.mem_univ i))

theorem levelCount_le_leaves {b : ℕ} (t : OccupiedParityTree b) (ht : t.occupied)
    (k : ℕ) : t.levelCount k ≤ t.leafCount := by
  induction t generalizing k with
  | leaf => cases k <;> norm_num [levelCount,leafCount]
  | @node b n children roles ih =>
    cases k with
    | zero => exact leafCount_pos (.node n children roles) ht
    | succ k => exact Finset.sum_le_sum (fun i _ => ih i (ht.2 i) k)

/-- Two chosen coordinates supply an additive gain in a finite sum. -/
theorem sum_two_improvements {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι → ℕ) {a c : ι} (hne : a≠c) (A B : ℕ)
    (hrest : ∀ i, i≠a → i≠c → x i≤y i)
    (ha : x a+A≤y a+B) (hc : x c+A≤y c+B) :
    (∑ i, x i)+2*A ≤ (∑ i, y i)+2*B := by
  have hc' : c∈Finset.univ.erase a := by simp [hne.symm]
  have hx1 := Finset.sum_erase_add Finset.univ x (Finset.mem_univ a)
  have hy1 := Finset.sum_erase_add Finset.univ y (Finset.mem_univ a)
  have hx2 := Finset.sum_erase_add (Finset.univ.erase a) x hc'
  have hy2 := Finset.sum_erase_add (Finset.univ.erase a) y hc'
  have hrem : (∑ i∈(Finset.univ.erase a).erase c, x i) ≤
      ∑ i∈(Finset.univ.erase a).erase c, y i := by
    apply Finset.sum_le_sum
    intro i hi
    exact hrest i (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      (Finset.mem_erase.mp hi).1
  omega

theorem Forced.leaf_lower {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :
    2^b ≤ t.leafCount := by
  classical
  induction F with
  | leaf => simp [leafCount]
  | @node b n children roles a c hne ha hc left right ihl ihr =>
    have hh := sum_two_improvements (fun _ : Fin n => 0)
      (fun i => (children i).leafCount) hne (2^b) 0
      (fun _ _ _ => Nat.zero_le _) (by simpa using ihl) (by simpa using ihr)
    simpa only [Finset.sum_const_zero,zero_add,add_zero,zero_mul,pow_succ,Nat.mul_comm,leafCount] using hh

/-- At every positive nonroot level, each unforced occupied vertex costs
 an extra leaf. This is the exact combinatorial inequality used when
 additional (nonbinary) labels are summed in the correlated-anchor estimate. -/
theorem Forced.level_extra {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (ht : t.occupied) (k : ℕ) :
    t.levelCount k+2^b ≤ t.leafCount+2^k := by
  classical
  induction F generalizing k with
  | leaf => cases k <;> simp [levelCount,leafCount]
  | @node b n children roles a c hne ha hc left right ihl ihr =>
    cases k with
    | zero =>
      have hl := (Forced.node a c hne ha hc left right).leaf_lower
      simpa only [levelCount,pow_zero,Nat.add_comm] using Nat.add_le_add_left hl 1
    | succ k =>
      have hh := sum_two_improvements
        (fun i => (children i).levelCount k) (fun i => (children i).leafCount)
        hne (2^b) (2^k) (fun i _ _ => levelCount_le_leaves _ (ht.2 i) k)
        (ihl (ht.2 a) k) (ihr (ht.2 c) k)
      simpa only [levelCount,leafCount,pow_succ,Nat.mul_comm] using hh

theorem Forced.nonforced_vertices_le_extra_leaves {b : ℕ} {t : OccupiedParityTree b}
    (F : t.Forced) (ht : t.occupied) (k : ℕ) :
    t.levelCount k-2^k ≤ t.leafCount-2^b := by
  have := F.level_extra ht k
  have := F.leaf_lower
  omega

end OccupiedParityTree
end TraceReconstruction

end
end
end

end OAI
