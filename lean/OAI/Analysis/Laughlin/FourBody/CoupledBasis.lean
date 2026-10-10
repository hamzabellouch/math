import OAI.Analysis.Laughlin.FourBody.CopyOrthogonality
import OAI.Analysis.Laughlin.Pair.CoupledBasis

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

abbrev FourCoupledIndex (Q : ℕ) :=
  Σ r : OddPairLabel Q, GenericCoupledIndex (2*Q-2) (genericCoupledWeight Q Q (oddPairDeficit r))

noncomputable def fourCoupledBasis (Q : ℕ) :
    Matrix (Fin (2*Q-2+1) × WedgePairIndex Q) (FourCoupledIndex Q) ℝ :=
  fun i s => fourBodyCopy Q (oddPairDeficit s.1) (oddPairDeficit s.1+s.2.1.val)
    (oddPairDeficit_le s.1) (by have := s.2.1.isLt; omega)
    (by have := s.2.1.isLt; omega) s.2.2.val i

theorem fourCoupledIndex_card (Q : ℕ) :
    Fintype.card (FourCoupledIndex Q) = Fintype.card (Fin (2*Q-2+1) × WedgePairIndex Q) := by
  rw [Fintype.card_sigma]
  simp_rw [genericCoupledIndex_card,Fintype.card_prod,Fintype.card_fin]
  rw [← Finset.mul_sum]
  congr 1
  simpa only [Fintype.card_sigma,Fintype.card_fin] using pairCoupledIndex_card Q

theorem fourCoupledBasis_isometry (Q : ℕ) :
    (fourCoupledBasis Q)ᵀ * fourCoupledBasis Q = 1 := by
  ext s t
  simp only [Matrix.mul_apply,Matrix.transpose_apply,fourCoupledBasis,Matrix.one_apply]
  by_cases h : s=t
  · subst t
    rw [ite_eq_left rfl]
    simpa only [vectorNormSq,pow_two] using
      fourBodyCopy_norm Q (oddPairDeficit s.1) (oddPairDeficit s.1+s.2.1.val)
        s.2.2.val (oddPairDeficit_le s.1) (oddPairDeficit_odd s.1) _ _
        (by have := s.2.2.isLt; simpa only [Nat.add_sub_cancel_left] using Nat.le_of_lt_succ this)
  · rw [ite_eq_right h]
    rcases s with ⟨r,⟨z,n⟩⟩
    rcases t with ⟨s,⟨w,m⟩⟩
    dsimp only at *
    by_cases hrs : r=s
    · subst s
      apply fourBodyCopy_orthogonal_outer _ _ _ _ _ _ _ (oddPairDeficit_odd r)
        (by omega) (by omega)
      by_cases hzw : z=w
      · subst w
        right
        intro he
        exact h (by have hn : n=m := Fin.ext he; subst m; rfl)
      · left
        intro he
        exact hzw (Fin.ext (by omega))
    · apply fourBodyCopy_orthogonal_pair _ _ _ _ _ _ _ _ _
        (oddPairDeficit_odd r) (oddPairDeficit_odd s)
      intro he
      exact hrs (Fin.ext (by dsimp [oddPairDeficit] at he; omega))

theorem fourCoupledBasis_complete (Q : ℕ) :
    fourCoupledBasis Q * (fourCoupledBasis Q)ᵀ = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq (m := FourCoupledIndex Q)
    (n := Fin (2*Q-2+1) × WedgePairIndex Q) (R := ℝ)
    (fourCoupledIndex_card Q)).mp (fourCoupledBasis_isometry Q)

end Laughlin.Spin

end OAI
