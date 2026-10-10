import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TriangularLateStationarity

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def matrixPairing (K : Matrix V V ℤ) : (V → ℤ) →+ (V → ℤ) →+ ℤ where
  toFun x := (Matrix.toBilin' K x).toAddMonoidHom
  map_zero' := by ext y; simp
  map_add' x y := by ext z; simp

lemma matrixPairing_apply (K : Matrix V V ℤ) (x y : V → ℤ) :
    matrixPairing K x y = ∑ a, ∑ b, x a * K a b * y b :=
  Matrix.toBilin'_apply _ _ _

@[simp] lemma matrixPairing_single (K : Matrix V V ℤ) (a b : V) :
    matrixPairing K (Pi.single a 1) (Pi.single b 1) = K a b :=
  Matrix.toBilin'_single ..

lemma matrixPairing_single_left (K : Matrix V V ℤ) (a : V) (m : V → ℤ) :
    matrixPairing K (Pi.single a 1) m = ∑ b, K a b * m b := by
  rw [matrixPairing_apply,Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

lemma matrixPairing_skew (K : Matrix V V ℤ) (hK : ∀ a b, K a b = -K b a)
    (x y : V → ℤ) : matrixPairing K x y = -matrixPairing K y x := by
  rw [matrixPairing_apply,matrixPairing_apply,Finset.sum_comm]
  simp only [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hK b a]
  ring

lemma matrixPairing_self (K : Matrix V V ℤ) (hK : ∀ a b, K a b = -K b a)
    (m : V → ℤ) : matrixPairing K m m = 0 := by
  have := matrixPairing_skew K hK m m
  omega

variable {n : ℕ} {B : Type*} [Fintype B] [DecidableEq B]

def chartMatrix (level : B → Fin n) (bb : B → B → ℤ) : Matrix (Vertex n B) (Vertex n B) ℤ
  | .inl _, .inl _ => 0
  | .inl a, .inr b => (if a = (level b).succ then 1 else 0) -
      (if a = (level b).castSucc then 1 else 0)
  | .inr b, .inl a => (if a = (level b).castSucc then 1 else 0) -
      (if a = (level b).succ then 1 else 0)
  | .inr b, .inr c => bb b c

noncomputable def chartPairing (level : B → Fin n) (bb : B → B → ℤ) :=
  matrixPairing (chartMatrix level bb)

omit [Fintype B] [DecidableEq B] in
lemma chartMatrix_skew (level : B → Fin n) (bb : B → B → ℤ)
    (hbb : ∀ b c, bb b c = -bb c b) (a c : Vertex n B) :
    chartMatrix level bb a c = -chartMatrix level bb c a := by
  cases a <;> cases c <;> simp only [chartMatrix]
  · rfl
  · ring
  · ring
  · apply hbb

lemma chartPairing_self (level : B → Fin n) (bb : B → B → ℤ)
    (hbb : ∀ b c, bb b c = -bb c b) (m : Lattice n B) :
    chartPairing level bb m m = 0 :=
  matrixPairing_self _ (chartMatrix_skew level bb hbb) m

omit [DecidableEq B] in
lemma total_as_sum (level : B → Fin n) (m : Lattice n B) (k : ℕ) :
    extendedTotal level m k = ∑ b, if (level b).val+1=k then m (.inr b) else 0 := by
  unfold extendedTotal
  split_ifs with hk
  · change (∑ b, if level b = ⟨k-1,by omega⟩ then m (.inr b) else 0) = _
    apply Finset.sum_congr rfl
    intro b _
    have hh : level b = (⟨k-1,by omega⟩ : Fin n) ↔ (level b).val+1=k := by
      constructor
      · intro h; have := congrArg Fin.val h; dsimp at this; omega
      · intro h; apply Fin.ext; dsimp; omega
    simp only [hh]
  · symm
    apply Finset.sum_eq_zero
    intro b _
    have hne : ¬(level b).val+1=k := by have := (level b).isLt; omega
    simp [hne]

lemma chartPairing_anchor (level : B → Fin n) (bb : B → B → ℤ)
    (a : Fin (n+1)) (m : Lattice n B) :
    chartPairing level bb (anchor a) m =
      extendedTotal level m a.val - extendedTotal level m (a.val+1) := by
  change matrixPairing (chartMatrix level bb) (Pi.single (.inl a) 1) m = _
  rw [matrixPairing_single_left,Fintype.sum_sum_type]
  simp only [chartMatrix,zero_mul,Finset.sum_const_zero,zero_add]
  rw [total_as_sum,total_as_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  have h1 : a = (level b).succ ↔ (level b).val+1=a.val := by
    rw [Fin.ext_iff]; simp only [Fin.val_succ]; omega
  have h2 : a = (level b).castSucc ↔ (level b).val+1=a.val+1 := by
    rw [Fin.ext_iff]; simp only [Fin.val_castSucc]; omega
  simp only [h1,h2]
  split_ifs <;> ring

lemma chartPairing_delta (level : B → Fin n) (bb : B → B → ℤ)
    (b : B) (m : Lattice n B) :
    chartPairing level bb (delta level b) m =
      2*extendedTotal level m ((level b).val+1) - extendedTotal level m (level b).val -
        extendedTotal level m ((level b).val+2) := by
  simp only [delta,map_sub,AddMonoidHom.sub_apply,chartPairing_anchor,
    Fin.val_succ,Fin.val_castSucc]
  ring

lemma chart_tropical_stationary (level : B → Fin n) (hl : Function.Surjective level)
    (bb : B → B → ℤ) (hbb : ∀ b c, bb b c = -bb c b)
    (cycle : List B) (hcycle : ∀ b, b ∈ cycle) (m : Lattice n B) (N : ℕ)
    (hs : ∀ L i, 0 ≤ cutDeficit level i N L
      (history (chartPairing level bb) level cycle m L)) :
    (∀ i, levelTotal level i m = 0) ∧
      (∀ b, 0 ≤ chartPairing level bb (eventRoot level 0 b) m) ∧
      (∀ L, history (chartPairing level bb) level cycle m L = m) :=
  tropical_history_stationary _ (chartPairing_self level bb hbb) level hl cycle hcycle
    (chartPairing_delta level bb) m N hs

end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators

abbrev Cell (n : ℕ) := (i : Fin n) × Fin (i.val+1)
def cellLevel {n : ℕ} (b : Cell n) : Fin n := b.1
def cellRow {n : ℕ} (b : Cell n) : ℕ := b.2.val

def phaseEarlier {n : ℕ} (b c : Cell n) : Prop :=
  cellRow c < cellRow b ∨ (cellRow b = cellRow c ∧ b.1 < c.1)
instance {n : ℕ} (b c : Cell n) : Decidable (phaseEarlier b c) :=
  inferInstanceAs (Decidable (_ ∨ (_ ∧ _)))

lemma cell_ext {n : ℕ} {b c : Cell n} (hl : b.1=c.1) (hr : cellRow b=cellRow c) : b=c := by
  cases b with | mk i r =>
    cases c with | mk j s =>
      dsimp only at hl
      subst j
      have HH:r=s:=Fin.ext hr
      subst s
      rfl

lemma phaseEarlier_trichotomy {n : ℕ} (b c : Cell n) :
    phaseEarlier b c ∨ b=c ∨ phaseEarlier c b := by
  by_cases hr : cellRow b=cellRow c
  · rcases lt_trichotomy b.1 c.1 with h|h|h
    · exact Or.inl (Or.inr ⟨hr,h⟩)
    · exact Or.inr (Or.inl (cell_ext h hr))
    · exact Or.inr (Or.inr (Or.inr ⟨hr.symm,h⟩))
  · rcases lt_or_gt_of_ne hr with h|h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl (Or.inl h)

@[simp] lemma phaseEarlier_irrefl {n : ℕ} (b : Cell n) : ¬phaseEarlier b b := by
  simp [phaseEarlier]
lemma phaseEarlier_asymm {n : ℕ} {b c : Cell n} (h : phaseEarlier b c) :
    ¬phaseEarlier c b := by
  unfold phaseEarlier at *
  rcases h with h|⟨h,h'⟩ <;> intro H
  · rcases H with H|⟨H,_⟩ <;> omega
  · rcases H with H|⟨_,H⟩
    · omega
    · exact lt_asymm h' H

def bridgePositive {n : ℕ} (b c : Cell n) : ℤ :=
  if b.1=c.1 ∧ phaseEarlier c b then 1
  else if c.1.val+1=b.1.val ∧ phaseEarlier b c then 1 else 0

def triangularBB {n : ℕ} (b c : Cell n) : ℤ := bridgePositive b c-bridgePositive c b

lemma triangularBB_skew {n : ℕ} (b c : Cell n) : triangularBB b c= -triangularBB c b := by
  unfold triangularBB
  ring

noncomputable def triangularOmega (n : ℕ) := chartPairing (@cellLevel n) (@triangularBB n)
lemma triangularOmega_self {n : ℕ} (m : Lattice n (Cell n)) : triangularOmega n m m=0 :=
  chartPairing_self _ _ triangularBB_skew m

lemma eventRoot_anchor {n : ℕ} (b : Cell n) (a : Fin (n+1)) :
    triangularOmega n (eventRoot cellLevel 0 b) (anchor a) =
      (if a=b.1.castSucc then 1 else 0)-(if a=b.1.succ then 1 else 0) := by
  simp only [eventRoot,Nat.cast_zero,zero_smul,add_zero,map_sub,AddMonoidHom.sub_apply]
  change matrixPairing (chartMatrix cellLevel triangularBB) (bridge b) (anchor a)-
    matrixPairing (chartMatrix cellLevel triangularBB) (anchor b.1.castSucc) (anchor a)=_
  simp only [bridge,anchor,matrixPairing_single,chartMatrix,cellLevel,sub_zero]
  rfl

lemma eventRoot_bridge_value {n : ℕ} (b c : Cell n) :
    triangularOmega n (eventRoot cellLevel 0 b) (bridge c) =
      if c.1=b.1 then
        (if phaseEarlier c b then 2 else if c=b then 1 else 0)
      else if c.1.val+1=b.1.val ∨ b.1.val+1=c.1.val then
        (if phaseEarlier c b then -1 else 0)
      else 0 := by
  simp only [eventRoot,Nat.cast_zero,zero_smul,add_zero,map_sub,AddMonoidHom.sub_apply]
  change matrixPairing (chartMatrix cellLevel triangularBB) (bridge b) (bridge c)-
    matrixPairing (chartMatrix cellLevel triangularBB) (anchor b.1.castSucc) (bridge c)=_
  simp only [bridge,anchor,matrixPairing_single]
  change triangularBB b c - ((if b.1.castSucc=c.1.succ then 1 else 0)-
    (if b.1.castSucc=c.1.castSucc then 1 else 0)) =
      (if c.1=b.1 then (if phaseEarlier c b then 2 else if c=b then 1 else 0)
      else if c.1.val+1=b.1.val ∨ b.1.val+1=c.1.val then
        (if phaseEarlier c b then -1 else 0) else 0)
  have h1 : b.1.castSucc=c.1.succ ↔ b.1.val=c.1.val+1 := by rw [Fin.ext_iff]; rfl
  have h2 : b.1.castSucc=c.1.castSucc ↔ b.1=c.1 := Fin.castSucc_inj
  simp only [triangularBB,bridgePositive,h1,h2]
  rcases phaseEarlier_trichotomy b c with H|H|H
  · have H' := phaseEarlier_asymm H
    have Hne : c≠b := by intro h; subst c; exact phaseEarlier_irrefl b H
    simp only [H,H',Hne,ite_false,and_false,and_true]
    by_cases hl : b.1=c.1
    · have hv := congrArg Fin.val hl
      simp only [hl,ite_true]
      split_ifs <;> omega
    · have hl' := Ne.symm hl
      simp only [hl,hl',ite_false]
      split_ifs <;> omega
  · subst c
    simp
  · have H' := phaseEarlier_asymm H
    simp only [H,H',ite_false,ite_true,and_false,and_true]
    by_cases hl : b.1=c.1
    · have hv := congrArg Fin.val hl
      simp only [hl,ite_true]
      split_ifs <;> omega
    · have hl' := Ne.symm hl
      simp only [hl,hl',ite_false]
      split_ifs <;> omega

end ElementaryPositivity.TriangularDynamics

end

end OAI
