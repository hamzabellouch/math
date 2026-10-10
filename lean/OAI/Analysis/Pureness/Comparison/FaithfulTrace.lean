import OAI.Analysis.Pureness.Comparison.UniformTwoNorm
import Mathlib.RingTheory.TwoSidedIdeal.Lattice

namespace OAI
namespace CuntzComparison

variable (A : Type*) [CStarAlgebra A]

class IsSimpleCStarAlgebra : Prop extends Nontrivial A where
  eq_bot_or_eq_top : ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤

variable {A} [PartialOrder A] [StarOrderedRing A]

namespace TracialState

noncomputable def nullIdeal (τ : TracialState A) : TwoSidedIdeal A :=
  .mk' {a | τ.twoNorm a = 0}
    τ.twoNorm_zero
    (fun {a b} ha hb => le_antisymm
      (by
        change τ.twoNorm a = 0 at ha
        change τ.twoNorm b = 0 at hb
        simpa only [ha, hb, add_zero] using τ.twoNorm_add_le a b)
      (τ.twoNorm_nonneg _))
    (fun {a} ha => by simpa [twoNorm] using ha)
    (fun {a b} hb => le_antisymm
      (by
        change τ.twoNorm b = 0 at hb
        simpa only [hb, mul_zero] using τ.twoNorm_mul_left a b)
      (τ.twoNorm_nonneg _))
    (fun {a b} ha => le_antisymm
      (by
        change τ.twoNorm a = 0 at ha
        simpa only [ha, mul_zero] using τ.twoNorm_mul_right b a)
      (τ.twoNorm_nonneg _))

@[simp] theorem mem_nullIdeal (τ : TracialState A) (a : A) :
    a ∈ τ.nullIdeal ↔ τ.twoNorm a = 0 := by simp [nullIdeal]

theorem isClosed_nullIdeal (τ : TracialState A) : IsClosed (τ.nullIdeal : Set A) := by
  have hs : (τ.nullIdeal : Set A) = τ.twoNorm ⁻¹' {0} := by
    ext a
    exact mem_nullIdeal τ a
  rw [hs]
  exact isClosed_singleton.preimage τ.continuous_twoNorm

theorem one_not_mem_nullIdeal (τ : TracialState A) : (1 : A) ∉ τ.nullIdeal := by
  simp

theorem nullIdeal_eq_bot [IsSimpleCStarAlgebra A] (τ : TracialState A) :
    τ.nullIdeal = ⊥ := by
  rcases IsSimpleCStarAlgebra.eq_bot_or_eq_top τ.nullIdeal τ.isClosed_nullIdeal with h | h
  · exact h
  · exact (τ.one_not_mem_nullIdeal (h.symm ▸ TwoSidedIdeal.mem_top A)).elim

theorem twoNorm_eq_zero_iff [IsSimpleCStarAlgebra A] (τ : TracialState A) (a : A) :
    τ.twoNorm a = 0 ↔ a = 0 := by
  rw [← mem_nullIdeal, τ.nullIdeal_eq_bot, TwoSidedIdeal.mem_bot]

theorem faithful [IsSimpleCStarAlgebra A] (τ : TracialState A) {a : A}
    (ha : τ.toPositiveLinearMap (star a * a) = 0) : a = 0 := by
  apply (τ.twoNorm_eq_zero_iff a).mp
  simp [twoNorm_eq, ha]

end TracialState

theorem uniformTwoNorm_eq_zero_iff [IsSimpleCStarAlgebra A]
    [Nonempty (TracialState A)] (a : A) : uniformTwoNorm a = 0 ↔ a = 0 := by
  constructor
  · intro ha
    let τ : TracialState A := Classical.choice inferInstance
    apply (τ.twoNorm_eq_zero_iff a).mp
    exact le_antisymm (by simpa only [ha] using twoNorm_le_uniform τ a)
      (τ.twoNorm_nonneg a)
  · rintro rfl
    exact uniformTwoNorm_zero

end CuntzComparison

end OAI
