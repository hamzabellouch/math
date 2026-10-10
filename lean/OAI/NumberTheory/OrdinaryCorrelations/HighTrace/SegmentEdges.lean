import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ClosedLine

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.SignedTrace
open OrdinaryCorrelations.SignedTrace
open Finset Classical
namespace ClosedLine
variable {h ℓ : ℕ}

def segmentEdges (_ : ClosedLine h ℓ) (a b : Fin (ℓ+1)) : Finset (Fin ℓ) :=
  univ.filter (fun e => min a.val b.val ≤ e.val ∧ e.val < max a.val b.val)

noncomputable def segmentSupport (w : ClosedLine h ℓ) (a b : Fin (ℓ+1)) : Finset ℕ :=
  (w.segmentEdges a b).biUnion (fun e => (w.label e).primeFactors)

lemma mem_segmentSupport_iff (w : ClosedLine h ℓ) (a b : Fin (ℓ+1))
    (p : ℕ) (hp : Nat.Prime p) :
    p ∈ w.segmentSupport a b ↔
      ∃ e : Fin ℓ, min a.val b.val ≤ e.val ∧ e.val < max a.val b.val ∧ p ∣ w.label e := by
  simp only [segmentSupport,mem_biUnion,segmentEdges,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨e,he,hp⟩
    exact ⟨e,he.1,he.2,(Nat.mem_primeFactors.mp hp).2.1⟩
  · rintro ⟨e,he,he',hd⟩
    exact ⟨e,⟨he,he'⟩,Nat.mem_primeFactors.mpr ⟨hp,hd,by have := w.label_pos e; omega⟩⟩

noncomputable def segmentCoefficient (w : ClosedLine h ℓ) (q : ℕ) (a b : Fin (ℓ+1)) : ℤ :=
  (if a ≤ b then 1 else -1) *
    ∑ e ∈ w.segmentEdges a b,
      if q ∣ w.label e then w.sign e*(h:ℤ)*(w.label e/q:ℕ) else 0

lemma segmentCoefficient_zero (w : ClosedLine h ℓ) (q : ℕ) (hq : Nat.Prime q)
    (a b : Fin (ℓ+1)) (hnot : q ∉ w.segmentSupport a b) :
    w.segmentCoefficient q a b = 0 := by
  unfold segmentCoefficient
  suffices (∑ e ∈ w.segmentEdges a b,
      if q ∣ w.label e then w.sign e*(h:ℤ)*(w.label e/q:ℕ) else 0) = 0 by rw [this,mul_zero]
  apply sum_eq_zero
  intro e he
  apply ite_eq_right
  intro hd
  have hi := (mem_filter.mp he).2
  exact hnot ((w.mem_segmentSupport_iff a b q hq).mpr ⟨e,hi.1,hi.2,hd⟩)
end ClosedLine
end OrdinaryCorrelations.SignedTrace

end

end OAI
