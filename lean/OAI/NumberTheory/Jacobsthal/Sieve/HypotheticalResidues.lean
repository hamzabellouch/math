import OAI.NumberTheory.Jacobsthal.Estimates.RationalCandidateSets

namespace OAI

namespace Erdos970

section

namespace ErdosHypotheticalTag
open ErdosInverseAlignment ErdosAlignedProgression ErdosInverseCounts
attribute [local instance] Classical.decEq

noncomputable def hypotheticalResidue (r : ℚ) (p : ℕ) [NeZero p] : ℕ :=
  ((r.num : ZMod p)*(r.den : ZMod p)⁻¹).val

noncomputable def hypotheticalClass (a : ℕ → ℕ) (r : ℚ) (p : ℕ) [NeZero p] : ℕ → ℕ :=
  Function.update a p (hypotheticalResidue r p)

theorem hypothetical_other (a : ℕ → ℕ) (r : ℚ) (p : ℕ) [NeZero p]
    (s : ℕ) (hsp : s ≠ p) : hypotheticalClass a r p s = a s :=
  Function.update_of_ne hsp _ _

theorem hypothetical_aligns (a : ℕ → ℕ) (r : ℚ) (p : ℕ) [NeZero p]
    (hp : p.Prime) (hD : r.den.Coprime p) :
    aligns (fun s => (hypotheticalClass a r p s : ℤ)) r p := by
  let : Fact p.Prime := ⟨hp⟩
  have hd0 : (r.den : ZMod p) ≠ 0 := by
    intro h
    exact (hp.coprime_iff_not_dvd.mp hD.symm) ((ZMod.natCast_eq_zero_iff _ _).mp h)
  simp only [aligns, hypotheticalClass, Function.update_self, hypotheticalResidue,
    Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [mul_left_comm, mul_inv_cancel₀ hd0, mul_one]

theorem hypothetical_mod_agrees (a : ℕ → ℕ) (r : ℚ) (p : ℕ) [NeZero p] (hp : p.Prime)
    (ha : aligns (fun s => (a s : ℤ)) r p) (s : ℕ) :
    hypotheticalClass a r p s % s = a s % s := by
  by_cases hsp : s = p
  · subst s
    have hD := aligned_den_coprime_prime a r p hp ha
    have hh := hypothetical_aligns a r p hp hD
    exact (aligned_prime_hit_iff a r p (hypotheticalClass a r p p) hp ha).mpr
      ((aligns_iff_modEq (fun s => (hypotheticalClass a r p s : ℤ)) r p).mp hh)
  · rw [hypothetical_other a r p s hsp]

theorem hypothetical_candidates_agree (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (d p : ℕ) [NeZero p] (hp : p.Prime)
    (ha : aligns (fun s => (a s : ℤ)) r p) :
    modulusCandidates Y small (hypotheticalClass a r p) d = modulusCandidates Y small a d := by
  ext t
  simp only [mem_modulusCandidates, hypothetical_mod_agrees a r p hp ha]

theorem hypothetical_count_agrees (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (d p : ℕ) [NeZero p] (hp : p.Prime)
    (ha : aligns (fun s => (a s : ℤ)) r p) :
    modulusCount Y small (hypotheticalClass a r p) d = modulusCount Y small a d := by
  rw [modulusCount, modulusCount, hypothetical_candidates_agree Y small a r d p hp ha]

end ErdosHypotheticalTag

end

end Erdos970

end OAI
