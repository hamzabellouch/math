import OAI.NumberTheory.Ostmann.Construction.InitialAtomGuards
import OAI.NumberTheory.Ostmann.Arithmetic.SampledTupleAmplitude

namespace OAI

/-! # The initial atom unit guard is precisely the Poisson frequency support -/

namespace Ostmann
open scoped Classical

theorem intCast_isUnit_iff_natAbs_coprime (p : ℕ) (v : ℤ) :
    IsUnit (v : ZMod p) ↔ p.Coprime v.natAbs := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_nat_coprime,
    Int.natAbs_natCast, Nat.coprime_comm]

theorem mem_tupleFrequencies_iff {I : Type*} [Fintype I] [Nonempty I]
    (p : I → ℕ) (hp : ∀ i, 2 ≤ p i) (N : ℕ) (v : ℤ) :
    v ∈ tupleFrequencies p N ↔ v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) ∧
      ∀ i, (p i).Coprime v.natAbs := by
  simp only [tupleFrequencies, Finset.mem_filter, intCast_isUnit_iff_natAbs_coprime]
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · rintro ⟨hr, hu⟩
    refine ⟨hr, ?_, hu⟩
    intro hz
    obtain ⟨i⟩ := ‹Nonempty I›
    have hi := hu i
    rw [hz, Int.natAbs_zero, Nat.coprime_zero_right] at hi
    have hh := hp i
    omega

end Ostmann

end OAI
