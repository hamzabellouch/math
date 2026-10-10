import OAI.NumberTheory.Jacobsthal.Estimates.ParentProgression
import OAI.NumberTheory.Jacobsthal.Estimates.SourceEdgeClasses
import OAI.NumberTheory.Jacobsthal.Sieve.AlignedPrimeCongruence

namespace OAI

namespace Erdos970

section

namespace ErdosInverseHits
open ErdosInverseCounts

noncomputable def sourceParentBase (p q : ℕ) [NeZero p] (hqp : q.Coprime p)
    (hq : Squarefree q) (a : ℕ → ℕ) : ℕ :=
  primeHitRepresentative q hq a+q*parentSlope p q hqp (a p) (primeHitRepresentative q hq a)

theorem sourceParentBase_bounds (p q : ℕ) [NeZero p] (hqp : q.Coprime p)
    (hq : Squarefree q) (a : ℕ → ℕ) :
    1 ≤ sourceParentBase p q hqp hq a ∧ sourceParentBase p q hqp hq a ≤ p*q :=
  parent_start_bounds p q hqp (a p) _ (primeHitRepresentative_spec q hq a).1
    (primeHitRepresentative_spec q hq a).2.1

theorem source_parent_hits_iff (p q : ℕ) [NeZero p] (hp : p.Prime) (hqp : q.Coprime p)
    (hq : Squarefree q) (a : ℕ → ℕ) (n : ℕ) :
    (∀ r ∈ (p*q).primeFactors,n%r = a r%r) ↔ Nat.ModEq (p*q) n (sourceParentBase p q hqp hq a) := by
  rw [Nat.primeFactors_mul hp.ne_zero hq.ne_zero,hp.primeFactors,
    Finset.forall_mem_union]
  simp only [Finset.mem_singleton,forall_eq]
  rw [(primeHitRepresentative_spec q hq a).2.2 n]
  exact parent_hit_iff p q hqp (a p) (primeHitRepresentative q hq a) n

noncomputable def parentSurvivorCoordinates (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (p q : ℕ) [NeZero p] (hqp : q.Coprime p) (hq : Squarefree q) : Finset ℕ := by
  classical
  exact (Finset.range (hitLength Y (p*q) (sourceParentBase p q hqp hq a))).filter
    (fun j => ∀ t ∈ small,(sourceParentBase p q hqp hq a+p*q*j)%t ≠ a t%t)

theorem modulusCandidates_eq_parent_image (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (p q : ℕ) [NeZero p] (hp : p.Prime) (hqp : q.Coprime p) (hq : Squarefree q) :
    modulusCandidates Y small a (p*q) =
      (parentSurvivorCoordinates Y small a p q hqp hq).image
        (fun j => sourceParentBase p q hqp hq a+p*q*j) := by
  classical
  have hM : 0 < p*q := mul_pos hp.pos (Nat.pos_of_ne_zero hq.ne_zero)
  have hb := sourceParentBase_bounds p q hqp hq a
  ext n
  rw [mem_modulusCandidates]
  simp only [parentSurvivorCoordinates,Finset.mem_image,Finset.mem_filter,Finset.mem_range]
  constructor
  · rintro ⟨hn1,hnY,hpr,hs⟩
    have hres := (source_parent_hits_iff p q hp hqp hq a n).mp hpr
    obtain ⟨j,rfl⟩ := exists_positive_coordinate (p*q) _ n hM hb.1 hb.2 hn1 hres
    exact ⟨j,⟨(lt_hitLength_iff Y (p*q) _ j hM hb.2).mpr hnY,hs⟩,rfl⟩
  · rintro ⟨j,⟨hj,hs⟩,rfl⟩
    refine ⟨by omega,(lt_hitLength_iff Y (p*q) _ j hM hb.2).mp hj,?_,hs⟩
    apply (source_parent_hits_iff p q hp hqp hq a _).mpr
    change (_+p*q*j)%(p*q) = _%(p*q)
    simp

theorem modulusCount_eq_parent_card (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (p q : ℕ) [NeZero p] (hp : p.Prime) (hqp : q.Coprime p) (hq : Squarefree q) :
    modulusCount Y small a (p*q) =
      ((parentSurvivorCoordinates Y small a p q hqp hq).card : ℤ) := by
  unfold modulusCount
  rw [modulusCandidates_eq_parent_image Y small a p q hp hqp hq,
    Finset.card_image_of_injective]
  intro i j hij
  exact Nat.eq_of_mul_eq_mul_left (mul_pos hp.pos (Nat.pos_of_ne_zero hq.ne_zero))
    (Nat.add_left_cancel hij)

theorem source_parent_length_error (Y p q : ℕ) [NeZero p] (hp : p.Prime)
    (hqp : q.Coprime p) (hq : Squarefree q) (a : ℕ → ℕ) :
    |(hitLength Y (p*q) (sourceParentBase p q hqp hq a) : ℝ)-(Y : ℝ)/(p*q)| ≤ 1 := by
  have hb := sourceParentBase_bounds p q hqp hq a
  simpa only [Nat.cast_mul] using hitLength_error Y (p*q) (sourceParentBase p q hqp hq a)
    (mul_pos hp.pos (Nat.pos_of_ne_zero hq.ne_zero)) hb.1 hb.2

end ErdosInverseHits

end

section

namespace ErdosInverseHits
open ErdosInverseCounts NumberTheoryLean NumberTheoryLean.SievePartition ErdosInverseCRT

noncomputable def parentEdgeResidue (p q u : ℕ) [NeZero p] (hqp : q.Coprime p)
    (hq : Squarefree q) (hpu : p.Coprime u) (hqu : q.Coprime u) (a : ℕ → ℕ) : ZMod u :=
  sourceEdgeResidue p q u hpu hqu (a u) (primeHitRepresentative q hq a)
    (parentSlope p q hqp (a p) (primeHitRepresentative q hq a))

theorem parent_edge_hit_iff (p q u : ℕ) [NeZero p] (hqp : q.Coprime p)
    (hq : Squarefree q) (hpu : p.Coprime u) (hqu : q.Coprime u) (a : ℕ → ℕ) (j : ℕ) :
    residueBad a u (sourceParentBase p q hqp hq a+p*q*j) ↔
      (j : ZMod u) = parentEdgeResidue p q u hqp hq hpu hqu a := by
  change Nat.ModEq u (sourceParentBase p q hqp hq a+p*q*j) (a u) ↔ _
  rw [← ZMod.natCast_eq_natCast_iff]
  have h := source_progression_edge_hit p q u hpu hqu (a u)
    (primeHitRepresentative q hq a) (parentSlope p q hqp (a p) (primeHitRepresentative q hq a)) j
  simpa only [sourceParentBase,parentEdgeResidue,Int.cast_add,Int.cast_mul,Int.cast_natCast,
    Nat.cast_add,Nat.cast_mul,mul_add,mul_assoc,add_assoc,mul_left_comm (q : ZMod u) (p : ZMod u)] using h

theorem modulusCandidates_eq_edge_image (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (p q u : ℕ) [NeZero p] (hp : p.Prime) (hu : u.Prime) (hqp : q.Coprime p)
    (hq : Squarefree q) (hpu : p.Coprime u) (hqu : q.Coprime u) :
    modulusCandidates Y small a (p*q*u) =
      ((parentSurvivorCoordinates Y small a p q hqp hq).filter
        (fun j : ℕ => (j : ZMod u) = parentEdgeResidue p q u hqp hq hpu hqu a)).image
          (fun j => sourceParentBase p q hqp hq a+p*q*j) := by
  classical
  rw [Nat.mul_comm (p*q) u,modulusCandidates_prime_mul Y small a u (p*q) hu
    (mul_ne_zero hp.ne_zero hq.ne_zero),modulusCandidates_eq_parent_image Y small a p q hp hqp hq]
  ext n
  simp only [Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨⟨j,hj,rfl⟩,hhit⟩
    exact ⟨j,⟨hj,(parent_edge_hit_iff p q u hqp hq hpu hqu a j).mp hhit⟩,rfl⟩
  · rintro ⟨j,⟨hj,hhit⟩,rfl⟩
    exact ⟨⟨j,hj,rfl⟩,(parent_edge_hit_iff p q u hqp hq hpu hqu a j).mpr hhit⟩

theorem modulusCount_eq_edge_card (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (p q u : ℕ) [NeZero p] (hp : p.Prime) (hu : u.Prime) (hqp : q.Coprime p)
    (hq : Squarefree q) (hpu : p.Coprime u) (hqu : q.Coprime u) :
    modulusCount Y small a (p*q*u) =
      (((parentSurvivorCoordinates Y small a p q hqp hq).filter
        (fun j : ℕ => (j : ZMod u) = parentEdgeResidue p q u hqp hq hpu hqu a)).card : ℤ) := by
  classical
  unfold modulusCount
  rw [modulusCandidates_eq_edge_image Y small a p q u hp hu hqp hq hpu hqu,
    Finset.card_image_of_injective]
  intro i j hij
  exact Nat.eq_of_mul_eq_mul_left (mul_pos hp.pos (Nat.pos_of_ne_zero hq.ne_zero))
    (Nat.add_left_cancel hij)

end ErdosInverseHits

end

end Erdos970

end OAI
