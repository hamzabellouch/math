import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseMarginal

namespace OAI

namespace MetricKMedian.SparseEnumeratedBatch
open Finset
variable {E : Type} [DecidableEq E] [Fintype E] {n : ℕ}

def law (enum : Fin n ≃ E) (Z : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) :
    SparseIntegerLaw (Finset E) :=
  (SparsePhysicalBatch.law (Z.map enum.symm.toEmbedding)
    (fun a => (C (enum a)).map enum.symm.toEmbedding) p (fun a => q (enum a)) hp
    (fun a => hq (enum a))).map (fun A => A.map enum.toEmbedding)

omit [DecidableEq E] [Fintype E] in
theorem length (enum : Fin n ≃ E) (Z : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) :
    (law enum Z C p q hp hq).length ≤ 2*((n+1)^4+1) :=
  SparsePhysicalBatch.length _ _ _ _ _ _

theorem marginal_error (enum : Fin n ≃ E) (Z : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {φ : ℝ} {N : ℕ} (hφ : 0 ≤ φ) (hqq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ (1+φ)*p)
    (hC : ∀ e, (C e).card ≤ N) (hself : ∀ e, e∉C e) (e : E) :
    |(law enum Z C p q hp hq).real.prob (fun A => e∈A)-(p:ℝ)/2| ≤
      (N:ℝ)*(p:ℝ)^2/2+φ*(p:ℝ)/2 := by
  rw [law,SparseIntegerLaw.prob_map]
  have hs : ∀ a : Fin n, a ∉ (C (enum a)).map enum.symm.toEmbedding := by
    intro a ha
    simp only [mem_map_equiv,Equiv.symm_symm] at ha
    exact hself _ ha
  have hh := SparsePhysicalBatch.marginal_error (Z.map enum.symm.toEmbedding)
    (fun a => (C (enum a)).map enum.symm.toEmbedding) p (fun a => q (enum a)) hp
    (fun a => hq (enum a)) hφ (fun a => hqq (enum a))
    (fun a => by simpa only [card_map] using hC (enum a)) hs (enum.symm e)
  simpa only [mem_map_equiv,Equiv.apply_symm_apply] using hh

theorem pair_le (enum : Fin n ≃ E) (Z : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    (e f : E) (hef : e≠f) :
    (law enum Z C p q hp hq).real.prob (fun A => e∈A ∧ f∈A) ≤
      ((p:ℝ)^2+(q e:ℝ)*(q f:ℝ))/2 := by
  rw [law,SparseIntegerLaw.prob_map]
  have hh := SparsePhysicalBatch.pair_le (Z.map enum.symm.toEmbedding)
    (fun a => (C (enum a)).map enum.symm.toEmbedding) p (fun a => q (enum a)) hp
    (fun a => hq (enum a)) (enum.symm e) (enum.symm f) (fun h => hef (enum.symm.injective h))
  simpa only [mem_map_equiv,Equiv.apply_symm_apply] using hh

theorem marginal_le (enum : Fin n ≃ E) (Z : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {Q : ℝ} (hpQ : (p:ℝ) ≤ Q) (hqQ : ∀ e, (q e:ℝ) ≤ Q) (e : E) :
    (law enum Z C p q hp hq).real.prob (fun A => e∈A) ≤ Q/2 := by
  rw [law,SparseIntegerLaw.prob_map]
  have hh := SparsePhysicalBatch.marginal_le (Z.map enum.symm.toEmbedding)
    (fun a => (C (enum a)).map enum.symm.toEmbedding) p (fun a => q (enum a)) hp
    (fun a => hq (enum a)) hpQ (fun a => hqQ (enum a)) (enum.symm e)
  simpa only [mem_map_equiv,Equiv.apply_symm_apply] using hh

def sortedEnumeration (E : Type) [LinearOrder E] [Fintype E] : Fin (Fintype.card E) ≃ E :=
  (Fintype.orderIsoFinOfCardEq E rfl).toEquiv

end MetricKMedian.SparseEnumeratedBatch

end OAI
