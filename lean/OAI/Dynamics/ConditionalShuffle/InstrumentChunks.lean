import OAI.Dynamics.ConditionalShuffle.InstrumentAppend

namespace OAI

noncomputable section
namespace Revealed.Instrument
open scoped Classical
open Thorp Thorp.Fourier Revealed.Disintegration

def chunks (S : Type) (t : ℕ) : (n : ℕ) → (Fin n → Fin t → S) ≃ (Fin (t*n) → S)
  | 0 => by simpa only [Nat.mul_zero] using (Equiv.ofUnique (Fin 0 → Fin t → S) (Fin 0 → S))
  | n+1 => ((Fin.snocEquiv (fun _ : Fin (n+1) => Fin t → S)).symm.trans
      (Equiv.prodComm _ _)).trans ((Equiv.prodCongr (chunks S t n) (Equiv.refl _)).trans
      (Fin.appendEquiv (t*n) t))

lemma chunks_snoc {S : Type} (t n : ℕ) (p : Fin n → Fin t → S) (q : Fin t → S) :
    chunks S t (n+1) (Fin.snoc p q) = Fin.append (chunks S t n p) q := by
  simp [chunks, Fin.appendEquiv]

variable {E S G Ω : Type} [Fintype S] [Fintype G] [Group G] [Fintype Ω] [Nonempty Ω]
variable (I : Data E S G Ω)

lemma block_base (e : E) (t n : ℕ) (p : Fin n → Fin t → S) :
    base (block I t) e n p = base I e (t*n) (chunks S t n p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      obtain ⟨⟨q,p⟩,rfl⟩ := (Fin.snocEquiv (fun _ : Fin (n+1) => Fin t → S)).surjective p
      erw [base_snoc, chunks_snoc]
      change base I (base (block I t) e n p) t q = base I e (t*n+t) (Fin.append (chunks S t n p) q)
      rw [base_append, ih]

lemma block_weights (e : E) (t n : ℕ) (p : Fin n → Fin t → S) :
    weights (block I t) e n p = weights I e (t*n) (chunks S t n p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      obtain ⟨⟨q,p⟩,rfl⟩ := (Fin.snocEquiv (fun _ : Fin (n+1) => Fin t → S)).surjective p
      erw [weights_snoc, chunks_snoc, block_probability, block_base, ih]
      exact (weights_append I e (t*n) t (chunks S t n p) q).symm

lemma block_product (e : E) (t n : ℕ) (p : Fin n → Fin t → S)
    (hp : weights (block I t) e n p ≠ 0) :
    realProduct n (kernels (block I t) e n p) =
      realProduct (t*n) (kernels I e (t*n) (chunks S t n p)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      obtain ⟨⟨q,p⟩,rfl⟩ := (Fin.snocEquiv (fun _ : Fin (n+1) => Fin t → S)).surjective p
      erw [weights_snoc] at hp
      have hp0 := (mul_ne_zero_iff.mp hp).1
      have hq := (mul_ne_zero_iff.mp hp).2
      rw [block_probability] at hq
      erw [kernels_snoc, realProduct_snoc, ih p hp0, chunks_snoc]
      change realConv (conditional (pathJoint I (base (block I t) e n p) t) q)
        (realProduct (t*n) (kernels I e (t*n) (chunks S t n p))) =
        realProduct (t*n+t) (kernels I e (t*n+t) (Fin.append (chunks S t n p) q))
      rw [conditional_pathJoint I _ t q hq, block_base, kernels_append, realProduct_append]

theorem distance_block (e : E) (t n : ℕ) : distance (block I t) e n = distance I e (t*n) := by
  unfold distance
  rw [← Equiv.sum_comp (chunks S t n)]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : weights (block I t) e n p = 0
  · rw [← block_weights, hp, zero_mul, zero_mul]
  · rw [block_product I e t n p hp, block_weights]

end Revealed.Instrument

end

end OAI
