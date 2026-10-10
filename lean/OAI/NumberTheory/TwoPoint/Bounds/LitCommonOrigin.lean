import OAI.NumberTheory.TwoPoint.Bounds.ResidueCentering

namespace OAI

/-! Consistent lit residues admit one integer origin for every selected departure. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem lit_consistency_common_origin {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    (B : ℕ) (p : ι → ℕ) (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hpB : ∀ i, p i ≤ B) (L : Finset τ) (label : τ → ι) (offset : τ → ℤ)
    (base : ι → Fin B)
    (hL : LitConsistent L label
      (fun t => forcedResidue B (p (label t)) (hprime _).pos (hpB _) (offset t))) :
    ∃ n : ℤ, ∀ t ∈ L, (p (label t) : ℤ) ∣ n + offset t := by
  let (i : ι) : NeZero (p i) := ⟨(hprime i).ne_zero⟩
  have hcop : Pairwise (fun i j => (p i).Coprime (p j)) := by
    intro i j hij
    exact (Nat.coprime_primes (hprime i) (hprime j)).mpr (fun he => hij (hinj he))
  let target (t : τ) := forcedResidue B (p (label t)) (hprime _).pos (hpB _) (offset t)
  let r (i : ι) : ZMod (p i) := ((litForcedTarget L label target base i).val : ZMod (p i))
  obtain ⟨n, hn⟩ := exists_common_integer_residue p hcop r
  refine ⟨n, ?_⟩
  intro t ht
  apply (residue_offset_divisibility (r (label t)) n (offset t) (hn _)).mpr
  change ((litForcedTarget L label target base (label t)).val : ZMod (p (label t))) = _
  rw [litForcedTarget_at L label target base hL t ht]
  exact ZMod.natCast_zmod_val _

end TwoPointCorrelations

end OAI
