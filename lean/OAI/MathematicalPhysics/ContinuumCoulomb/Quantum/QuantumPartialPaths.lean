import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathsGraph
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingSize
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathDegrees

namespace OAI

/-! Subdivide any selected subset of a finite exchange graph in one calibrated layer. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph Matrix
open scoped BigOperators Classical

variable {ν : Type*} [Fintype ν] {n : ℕ}

def qmaSelectedIndex (s : Finset ν) (i : Fin s.card) : ν := (s.equivFin.symm i).val

omit [Fintype ν] in
theorem qmaSelectedIndex_mem (s : Finset ν) (i : Fin s.card) : qmaSelectedIndex s i ∈ s :=
  (s.equivFin.symm i).property

def qmaSelectedSite (left right : ν → Fin n) (s : Finset ν) (i : Fin s.card) : Fin 2 → Fin n :=
  ![left (qmaSelectedIndex s i),right (qmaSelectedIndex s i)]

omit [Fintype ν] in
theorem qmaSelectedSite_injective (left right : ν → Fin n) (hn : ∀ e, left e ≠ right e)
    (s : Finset ν) (i : Fin s.card) : Function.Injective (qmaSelectedSite left right s i) := by
  intro a b h
  have hn' := hn (qmaSelectedIndex s i)
  fin_cases a <;> fin_cases b
  · rfl
  · exact False.elim (hn' h)
  · exact False.elim (hn' h.symm)
  · rfl

omit [Fintype ν] in
theorem qmaSelected_sum {M : Type*} [AddCommMonoid M] (s : Finset ν) (f : ν → M) :
    (∑ i : Fin s.card, f (qmaSelectedIndex s i)) = ∑ i : {i // i ∈ s}, f i.val :=
  s.equivFin.symm.sum_comp (fun i => f i.val)

theorem qmaSelected_partition {M : Type*} [AddCommMonoid M] (s : Finset ν) (f : ν → M) :
    (∑ i : {i // i ∉ s}, f i.val) + (∑ i : Fin s.card, f (qmaSelectedIndex s i)) =
      ∑ i, f i := by
  rw [qmaSelected_sum]
  rw [← Finset.sum_subtype s (fun _ => Iff.rfl) f,
    ← Finset.sum_subtype sᶜ (fun _ => Finset.mem_compl) f]
  exact Finset.sum_compl_add_sum s f

theorem qmaPartialPaths_source (left right : ν → Fin n) (w : ν → ℝ) (t : ℝ) (s : Finset ν) :
    qmaExchangeMatrix (fun e : {e // e ∉ s} => left e.val) (fun e => right e.val)
        (fun e => w e.val) t +
      ∑ i : Fin s.card, (w (qmaSelectedIndex s i):ℂ) •
        sourceHeisenbergMatrix n (qmaSelectedSite left right s i 0) (qmaSelectedSite left right s i 1) =
      qmaExchangeMatrix left right w t := by
  simp only [qmaSelectedSite,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  have h := qmaSelected_partition s
    (fun i => (w i:ℂ) • sourceHeisenbergMatrix n (left i) (right i))
  simp only [qmaExchangeMatrix]
  calc
    _ = ((∑ e : {e // e ∉ s}, (w e.val:ℂ) • sourceHeisenbergMatrix n (left e.val) (right e.val)) +
        ∑ i : Fin s.card, (w (qmaSelectedIndex s i):ℂ) •
          sourceHeisenbergMatrix n (left (qmaSelectedIndex s i)) (right (qmaSelectedIndex s i))) +
          (t:ℂ) • 1 := by ac_rfl
    _ = _ := congrArg (fun x => x+(t:ℂ) • 1) h

def qmaPartialPathsScale (w : ν → ℝ) (t : ℝ) (s : Finset ν) (N : ℝ) : ℝ :=
  let B := 3*(∑ e : {e // e ∉ s}, |w e.val|)+|t|
  let A := 3*∑ i : Fin s.card, (1+2*|w (qmaSelectedIndex s i)|)
  let D := B+4*∑ i : Fin s.card, (1+|w (qmaSelectedIndex s i)|)^2
  qmaRoutingScale A D N

def qmaPartialPaths (left right : ν → Fin n) (w : ν → ℝ) (t N : ℝ)
    (s : Finset ν) (even : Fin s.card → Bool) :=
  qmaPathsGraph (fun e : {e // e ∉ s} => left e.val) (fun e => right e.val) (fun e => w e.val)
    t (qmaPartialPathsScale w t s N) (qmaSelectedSite left right s) even
    (fun i => w (qmaSelectedIndex s i))

theorem qmaPartialPaths_accuracy (left right : ν → Fin n) (hn : ∀ e, left e ≠ right e)
    (w : ν → ℝ) (t : ℝ) (s : Finset ν) (even : Fin s.card → Bool) {N : ℝ} (hN : 0 < N) :
    |sourceMatrixBottom (n+s.card*2) (qmaPartialPaths left right w t N s even) -
      sourceMatrixBottom n (qmaExchangeMatrix left right w t)| ≤ 1/N := by
  have h := qmaPathsGraph_accuracy (fun e : {e // e ∉ s} => left e.val) (fun e => right e.val)
    (fun e => hn e.val) (fun e => w e.val) t (qmaSelectedSite left right s)
    (qmaSelectedSite_injective left right hn s) even (fun i => w (qmaSelectedIndex s i)) hN
  dsimp only at h
  rw [qmaPartialPaths_source] at h
  exact h


abbrev QMAPartialPathsEdge (s : Finset ν) :=
  {e // e ∉ s} ⊕ (Fin s.card ⊕ (Fin s.card × Fin 2))

def qmaPartialPathsLeft (left right : ν → Fin n) (s : Finset ν) : QMAPartialPathsEdge s → Fin (n+s.card*2) :=
  qmaParallelGraphLeft (fun e : {e // e ∉ s} => left e.val) (qmaSelectedSite left right s)

def qmaPartialPathsRight (right : ν → Fin n) (s : Finset ν) (even : Fin s.card → Bool) :
    QMAPartialPathsEdge s → Fin (n+s.card*2) :=
  qmaParallelGraphRight (fun e : {e // e ∉ s} => right e.val) (fun i => qmaPathMember (even i))

omit [Fintype ν] in
theorem qmaPartialPaths_distinct (left right : ν → Fin n) (hn : ∀ e, left e ≠ right e)
    (s : Finset ν) (even : Fin s.card → Bool) :
    ∀ e, qmaPartialPathsLeft left right s e ≠ qmaPartialPathsRight right s even e :=
  qmaParallelGraph_distinct (fun e : {e // e ∉ s} => left e.val) (fun e => right e.val)
    (fun e => hn e.val) _ _

theorem qmaPartialPaths_edge_count (s : Finset ν) :
    Fintype.card (QMAPartialPathsEdge s) = Fintype.card ν+2*s.card := by
  have hs : s.card ≤ Fintype.card ν := Finset.card_le_univ s
  simp only [QMAPartialPathsEdge,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,
    Fintype.card_subtype_compl,Fintype.card_coe]
  omega

theorem qmaPartialPaths_old_degree (left right : ν → Fin n) (hn : ∀ e, left e ≠ right e)
    (s : Finset ν) (even : Fin s.card → Bool) (v : Fin n) :
    qmaGraphDegree (qmaPartialPathsLeft left right s) (qmaPartialPathsRight right s even)
      (old n s.card v) = qmaGraphDegree left right v := by
  dsimp only [qmaPartialPathsLeft,qmaPartialPathsRight]
  rw [qmaPaths_old_degree _ _ _ (qmaSelectedSite_injective left right hn s)]
  simp only [qmaGraphDegree,Fintype.sum_sum_type]
  change (∑ e : {e // e ∉ s}, if left e.val = v ∨ right e.val = v then 1 else 0) +
    (∑ i : Fin s.card, if left (qmaSelectedIndex s i) = v ∨
      right (qmaSelectedIndex s i) = v then 1 else 0) =
    ∑ e, if left e = v ∨ right e = v then 1 else 0
  exact qmaSelected_partition s (fun e => if left e = v ∨ right e = v then 1 else 0)

theorem qmaPartialPaths_fresh_degree (left right : ν → Fin n) (s : Finset ν)
    (even : Fin s.card → Bool) (e : Fin s.card) (b : Fin 2) :
    qmaGraphDegree (qmaPartialPathsLeft left right s) (qmaPartialPathsRight right s even)
      (fresh n s.card e b) ≤ 3 :=
  qmaPaths_new_degree _ _ _ _ _ _

end ContinuumCoulomb

end

end OAI
