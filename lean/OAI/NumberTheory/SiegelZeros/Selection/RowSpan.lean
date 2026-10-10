import Mathlib.LinearAlgebra.Matrix.Rank

namespace OAI

namespace SiegelZeros


namespace WeightedTorusJets.W28

open Module

variable {K ι ρ : Type*} [Field K] [Fintype ι] [Fintype ρ]

theorem mulVecLin_injective_iff_rowSpan_eq_top (A : Matrix ρ ι K) :
    Function.Injective A.mulVecLin ↔
      Submodule.span K (Set.range A.row) = ⊤ := by
  constructor
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    rw [← A.rank_eq_finrank_span_row]
    exact LinearMap.finrank_range_of_inj h
  · intro h
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    have hn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    have hr : finrank K (LinearMap.range A.mulVecLin) = finrank K (ι → K) := by
      change A.rank = _
      rw [A.rank_eq_finrank_span_row, h, finrank_top]
    rw [hr] at hn
    exact Nat.add_left_cancel (hn.trans (Nat.add_zero _).symm)

theorem annihilation_iff_rowSpan_eq_top (A : Matrix ρ ι K) :
    (∀ c : ι → K, A.mulVec c = 0 → c = 0) ↔
      Submodule.span K (Set.range A.row) = ⊤ := by
  rw [← mulVecLin_injective_iff_rowSpan_eq_top]
  exact (LinearMap.ker_eq_bot' (f := A.mulVecLin)).symm.trans LinearMap.ker_eq_bot

end WeightedTorusJets.W28


end SiegelZeros

end OAI
