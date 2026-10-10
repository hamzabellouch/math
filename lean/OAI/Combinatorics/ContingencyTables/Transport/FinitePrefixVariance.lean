import OAI.Combinatorics.ContingencyTables.Transport.FinitePartitionVariance
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI

/-! # Variance telescoping for literal finite coordinate prefixes -/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators Classical

def restriction {A : Type*} {q : ℕ} (k : ℕ) (hk : k ≤ q)
    (a : Fin q → A) : Fin k → A := fun i => a ⟨i.val,lt_of_lt_of_le i.isLt hk⟩

def prefixSnocEquiv (A : Type*) (k : ℕ) : ((Fin k → A)×A) ≃ (Fin (k+1) → A) :=
  (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => A))

lemma restriction_snoc {A : Type*} {q k : ℕ} (hk : k < q) (a : Fin q → A) :
    prefixSnocEquiv A k (restriction k (Nat.le_of_lt hk) a,a ⟨k,hk⟩)=
      restriction (k+1) hk a := by
  change Fin.snoc (restriction k (Nat.le_of_lt hk) a) (a ⟨k,hk⟩)=restriction (k+1) hk a
  have hi : restriction k (Nat.le_of_lt hk) a=Fin.init (restriction (k+1) hk a) := rfl
  rw [hi]
  exact Fin.snoc_init_self _

variable {A : Type*} [Fintype A] {q : ℕ}

noncomputable def prefixVariance (w H : (Fin q → A) → ℝ) (k : ℕ) (hk : k ≤ q) : ℝ :=
  partitionVariance w H (restriction k hk)

noncomputable def prefixContribution (w H : (Fin q → A) → ℝ) (k : Fin q) : ℝ :=
  partitionContribution w H (restriction k.val (Nat.le_of_lt k.isLt)) (fun a => a k)

theorem prefixVariance_step (w H : (Fin q → A) → ℝ) (hw : ∀ a,0 ≤ w a) (k : Fin q) :
    prefixVariance w H k.val (Nat.le_of_lt k.isLt)=
      prefixVariance w H (k.val+1) k.isLt+prefixContribution w H k := by
  have hp := partition_refinement w H hw (restriction k.val (Nat.le_of_lt k.isLt)) (fun a => a k)
  have he := partitionVariance_reindex (prefixSnocEquiv A k.val) w H
    (fun a => (restriction k.val (Nat.le_of_lt k.isLt) a,a k))
  have hfun : (fun a => prefixSnocEquiv A k.val (restriction k.val (Nat.le_of_lt k.isLt) a,a k))=
      restriction (k.val+1) k.isLt := by
    funext a
    exact restriction_snoc k.isLt a
  rw [hfun] at he
  rw [← he] at hp
  exact hp

lemma prefixVariance_zero (w H : (Fin q → A) → ℝ) : prefixVariance w H 0 (Nat.zero_le q)=variance w H := by
  unfold prefixVariance partitionVariance
  rw [Fintype.sum_unique]
  congr 1
  funext a
  unfold fibreWeight
  rw [ite_eq_left (Subsingleton.elim _ _)]

lemma prefixVariance_final (w H : (Fin q → A) → ℝ) (hw : ∀ a,0 ≤ w a) :
    prefixVariance w H q le_rfl=0 := by
  change partitionVariance w H id=0
  exact partitionVariance_identity w H hw

/-- Each physical exposure depth incurs its own budget once. -/
theorem variance_le_prefix_budget (w H : (Fin q → A) → ℝ) (hw : ∀ a,0 ≤ w a)
    (B : ℝ) (hb : ∀ k : Fin q,prefixContribution w H k ≤ B) :
    variance w H ≤ q*B := by
  have hacc : ∀ k (hk : k ≤ q),variance w H ≤ prefixVariance w H k hk+k*B := by
    intro k
    induction k with
    | zero =>
      intro hk
      rw [prefixVariance_zero]
      simp only [Nat.cast_zero,zero_mul,add_zero,le_refl]
    | succ k ih =>
      intro hk
      have hkl : k < q := by omega
      have hstep := prefixVariance_step w H hw ⟨k,hkl⟩
      have hprevious := ih (Nat.le_of_lt hkl)
      have hbound := hb ⟨k,hkl⟩
      dsimp only at hstep hbound
      rw [hstep] at hprevious
      rw [Nat.cast_succ]
      linarith
  have h := hacc q le_rfl
  rw [prefixVariance_final w H hw,zero_add] at h
  exact h

end ContingencyTables.FiniteExposureVariance

end OAI
