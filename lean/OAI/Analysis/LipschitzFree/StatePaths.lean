import OAI.Analysis.LipschitzFree.Words

namespace OAI

/-!
# Counting finite-state paths with bounded transitions
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section

namespace DiscreteFree.StatePaths
open scoped BigOperators Classical

universe u
variable {S : Type u} (r : S → S → Prop)

def Based : S → ℕ → Type u
  | _, 0 => PUnit
  | j, n+1 => Σ k : {k : S // r j k}, Based k.val n

instance [Fintype S] (j : S) (n : ℕ) : Fintype (Based r j n) := by
  induction n generalizing j with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    letI (k : S) : Fintype (Based r k n) := ih k
    exact inferInstanceAs (Fintype (Σ k : {k : S // r j k}, Based r k.val n))

def vertex (j : S) : {n : ℕ} → Based r j n → Fin (n+1) → S
  | 0, _, _ => j
  | _n+1, p, i => Fin.cases j (fun i => vertex p.1.val p.2 i) i

@[simp] theorem at_zero (j : S) (n : ℕ) (p : Based r j n) : vertex r j p 0 = j := by
  cases n <;> rfl

@[simp] theorem at_succ (j : S) (n : ℕ) (p : Based r j (n+1)) (i : Fin (n+1)) :
    vertex r j p i.succ = vertex r p.1.val p.2 i := rfl

theorem at_transition (j : S) (n : ℕ) (p : Based r j n) (i : Fin n) :
    r (vertex r j p i.castSucc) (vertex r j p i.succ) := by
  induction n generalizing j with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · change r j (vertex r p.1.val p.2 0)
      rw [at_zero]
      exact p.1.property
    · exact ih p.1.val p.2 i

def ofSequence : {n : ℕ} → (a : Fin (n+1) → S) →
    (∀ i : Fin n, r (a i.castSucc) (a i.succ)) → Based r (a 0) n
  | 0, _, _ => PUnit.unit
  | _n+1, a, h => ⟨⟨a 1, h 0⟩, ofSequence (fun i => a i.succ) (fun i => h i.succ)⟩

theorem at_ofSequence {n : ℕ} (a : Fin (n+1) → S)
    (h : ∀ i : Fin n, r (a i.castSucc) (a i.succ)) :
    vertex r (a 0) (ofSequence r a h) = a := by
  induction n with
  | zero =>
    funext i
    have hi : i = 0 := Fin.ext (by omega)
    rw [hi]
    rfl
  | succ n ih =>
    funext i
    refine Fin.cases rfl (fun i => ?_) i
    exact congrFun (ih (fun i => a i.succ) (fun i => h i.succ)) i

theorem card_based_le [Fintype S] (Q : ℕ)
    (hQ : ∀ j, Fintype.card {k : S // r j k} ≤ Q) (j : S) (n : ℕ) :
    Fintype.card (Based r j n) ≤ Q ^ n := by
  induction n generalizing j with
  | zero =>
    change Fintype.card PUnit ≤ 1
    exact Fintype.card_unique.le
  | succ n ih =>
    change Fintype.card (Σ k : {k : S // r j k}, Based r k.val n) ≤ _
    rw [Fintype.card_sigma]
    calc
      (∑ k : {k : S // r j k}, Fintype.card (Based r k.val n)) ≤
          ∑ _k : {k : S // r j k}, Q ^ n := Finset.sum_le_sum (fun k _ => ih k.val)
      _ = Fintype.card {k : S // r j k} * Q ^ n := by simp
      _ ≤ Q * Q ^ n := Nat.mul_le_mul_right _ (hQ j)
      _ = Q ^ (n+1) := (pow_succ' _ _).symm

def Path (n : ℕ) := Σ j : S, Based r j n

instance [Fintype S] (n : ℕ) : Fintype (Path r n) := inferInstanceAs (Fintype (Σ j : S, Based r j n))

def Path.vertex {n : ℕ} (p : Path r n) : Fin (n+1) → S := StatePaths.vertex r p.1 p.2

theorem card_path_le [Fintype S] (Q : ℕ)
    (hQ : ∀ j, Fintype.card {k : S // r j k} ≤ Q) (n : ℕ) :
    Fintype.card (Path r n) ≤ Fintype.card S * Q ^ n := by
  change Fintype.card (Σ j : S, Based r j n) ≤ _
  rw [Fintype.card_sigma]
  simpa using Finset.sum_le_sum (s := (Finset.univ : Finset S))
    (fun j _ => card_based_le r Q hQ j n)

end DiscreteFree.StatePaths

end

end

end OAI
