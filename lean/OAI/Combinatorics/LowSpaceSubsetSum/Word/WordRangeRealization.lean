import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordRealization
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.FiniteProductSamplerCoupling

namespace OAI

/-! # Exact bounded word programs for range and permutation calls -/

noncomputable section
namespace LowSpaceSubsetSum.WordRealization

def enlarge {w N M : ℕ} {α : Type} [Fintype α] {S : SamplerCoupling α}
    (X : Realization w N S) (h : N ≤ M) : Realization w M S where
  program := X.program
  faithful := X.faithful
  bounded := by
    have hb := WordProgram.bound_add X.program N X.bounded (M-N)
    simpa only [Nat.sub_add_cancel h] using hb

def prod {w N M : ℕ} {α β : Type} [Fintype α] [Fintype β]
    {S : SamplerCoupling α} {T : SamplerCoupling β}
    (X : Realization w N S) (Y : Realization w M T) :
    Realization w (N+M) (S.prod T) :=
  map (bind X (fun _ => β) (fun _ => T) (fun _ => Y)) (Equiv.sigmaEquivProd α β)

def range (w n D : ℕ) (hD : 1 < D) (hw : Nat.clog 2 D ≤ w) :
    Realization w (n^3) (rangeCoupling hD n) := by
  let : Nonempty (Fin D) := ⟨⟨0, by omega⟩⟩
  let : Nonempty {x : Fin (2 ^ Nat.clog 2 D) // rangeEligible D x} :=
    ⟨(rangeEligibleEquiv D).symm ⟨0, by omega⟩⟩
  exact map (rejection w (Nat.clog 2 D) hw (n^3) (rangeEligible D)) (rangeEligibleEquiv D)

def fin (w n D : ℕ) [NeZero D] (hw : Nat.clog 2 D ≤ w) :
    Realization w (n^3) (finCoupling n D) := by
  unfold finCoupling
  split
  next h => exact range w n D h hw
  next h => exact enlarge (pure (⟨0, Nat.pos_of_ne_zero (NeZero.ne D)⟩ : Fin D)) (Nat.zero_le _)

def pi (w N : ℕ) : (k : ℕ) → (A : Fin k → Type) → [∀ i, Fintype (A i)] →
    (S : ∀ i, SamplerCoupling (A i)) → (∀ i, Realization w N (S i)) →
    Realization w (k*N) (SamplerCoupling.pi k A S)
  | 0, A, _, _, _ => by
    simpa only [Nat.zero_mul, SamplerCoupling.pi] using
      (pure (w := w) (fun i : Fin 0 => (Fin.elim0 i : A i)))
  | k+1, A, _, S, X => by
    have h := map (prod (X 0)
      (pi w N k (fun i => A i.succ) (fun i => S i.succ) (fun i => X i.succ)))
      (Fin.consEquiv A)
    simpa only [SamplerCoupling.pi, Nat.add_mul, Nat.one_mul, Nat.add_comm] using h

def permutation (w n : ℕ) : (k : ℕ) → Nat.clog 2 k ≤ w →
    Realization w (k*n^3) (permutationCoupling n k)
  | 0, _ => by
    simpa only [Nat.zero_mul, permutationCoupling] using (pure (w := w) (Equiv.refl (Fin 0)))
  | k+1, hw => by
    have hk : Nat.clog 2 k ≤ w :=
      (Nat.clog_mono_right 2 (by omega : k ≤ k+1)).trans hw
    have h := map (prod (fin w n (k+1) hw) (permutation w n k hk))
      Equiv.Perm.decomposeFin.symm
    simpa only [permutationCoupling, Nat.add_mul, Nat.one_mul, Nat.add_comm] using h

def finiteChoice (w n : ℕ) (A : Type) [Fintype A] [Nonempty A]
    (hw : Nat.clog 2 (Fintype.card A) ≤ w) :
    Realization w (n^3) (finiteChoiceCoupling n A) :=
  map (fin w n (Fintype.card A) hw) (Fintype.equivFin A).symm

def finitePermutation (w n : ℕ) (A : Type) [Fintype A] [DecidableEq A]
    (hw : Nat.clog 2 (Fintype.card A) ≤ w) :
    Realization w (Fintype.card A*n^3) (finitePermutationCoupling n A) :=
  map (permutation w n (Fintype.card A) hw) (Equiv.permCongr (Fintype.equivFin A).symm)

end LowSpaceSubsetSum.WordRealization

end

end OAI
