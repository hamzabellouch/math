import OAI.Analysis.Laughlin.Pair.CoupledIsometry
import OAI.Analysis.Laughlin.Spin.Basis

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

abbrev OddPairLabel (Q : ℕ) := Fin ((Q+1)/2)
def oddPairDeficit {Q : ℕ} (r : OddPairLabel Q) : ℕ := 2*r.val+1

theorem oddPairDeficit_le {Q : ℕ} (r : OddPairLabel Q) : oddPairDeficit r ≤ Q := by
  have := r.isLt
  dsimp [oddPairDeficit]
  omega

theorem oddPairDeficit_odd {Q : ℕ} (r : OddPairLabel Q) : Odd (oddPairDeficit r) :=
  ⟨r.val,rfl⟩

abbrev PairCoupledIndex (Q : ℕ) :=
  Σ r : OddPairLabel Q, Fin (genericCoupledWeight Q Q (oddPairDeficit r)+1)

noncomputable def pairCoupledBasis (Q : ℕ) : Matrix (WedgePairIndex Q) (PairCoupledIndex Q) ℝ :=
  fun i s => pairCoupledWedge Q (oddPairDeficit s.1) (oddPairDeficit_le s.1) s.2.val i

def wedgePairEquiv (Q : ℕ) : WedgePairIndex Q ≃ Σ j : Fin (Q+1), Fin j.val where
  toFun i := ⟨i.val.2,⟨i.val.1.val,i.property⟩⟩
  invFun s := ⟨(⟨s.2.val,by have := s.1.isLt; have := s.2.isLt; omega⟩,s.1),s.2.isLt⟩
  left_inv i := by apply Subtype.ext; rfl
  right_inv s := by cases s; rfl

theorem wedgePairIndex_card_real (Q : ℕ) :
    (Fintype.card (WedgePairIndex Q) : ℝ) = (Q : ℝ)*(Q+1)/2 := by
  rw [Fintype.card_congr (wedgePairEquiv Q)]
  simp only [Fintype.card_sigma,Fintype.card_fin,Nat.cast_sum]
  rw [fin_sum_values]
  push_cast
  ring

theorem pairCoupledIndex_card (Q : ℕ) :
    Fintype.card (PairCoupledIndex Q) = Fintype.card (WedgePairIndex Q) := by
  have h : (Fintype.card (PairCoupledIndex Q) : ℝ) = (Fintype.card (WedgePairIndex Q) : ℝ) := by
    rw [wedgePairIndex_card_real]
    simp only [Fintype.card_sigma,Fintype.card_fin,Nat.cast_sum]
    have hc (r : OddPairLabel Q) :
        ((genericCoupledWeight Q Q (oddPairDeficit r)+1 : ℕ) : ℝ) =
          2*(Q : ℝ)-1-4*(r.val : ℝ) := by
      have hr := oddPairDeficit_le r
      unfold genericCoupledWeight
      rw [Nat.cast_add,Nat.cast_sub (by omega : 2*oddPairDeficit r ≤ Q+Q)]
      simp only [oddPairDeficit,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
      ring
    simp_rw [hc]
    rw [Finset.sum_sub_distrib,Finset.sum_const,← Finset.mul_sum,fin_sum_values]
    simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hp : Q+1=2*((Q+1)/2) ∨ Q=2*((Q+1)/2) := by omega
    rcases hp with hp | hp
    · have he : (Q : ℝ)+1=2*(((Q+1)/2 : ℕ) : ℝ) := by exact_mod_cast hp
      nlinarith
    · have he : (Q : ℝ)=2*(((Q+1)/2 : ℕ) : ℝ) := by exact_mod_cast hp
      nlinarith
  exact_mod_cast h

theorem pairCoupledBasis_isometry (Q : ℕ) :
    (pairCoupledBasis Q)ᵀ * pairCoupledBasis Q = 1 := by
  ext s t
  simp only [Matrix.mul_apply,Matrix.transpose_apply,pairCoupledBasis,Matrix.one_apply]
  by_cases h : s=t
  · subst t
    rw [ite_eq_left rfl]
    simpa only [vectorNormSq,pow_two] using
      pairCoupledWedge_norm Q (oddPairDeficit s.1) s.2.val (oddPairDeficit_le s.1)
        (oddPairDeficit_odd s.1) (by have := s.2.isLt; omega)
  · rw [ite_eq_right h]
    apply pairCoupledWedge_orthogonal _ _ _ _ _ _ _ (oddPairDeficit_odd s.1) (oddPairDeficit_odd t.1)
    rcases s with ⟨r,n⟩
    rcases t with ⟨s,m⟩
    by_cases hrs : r=s
    · subst s
      right
      intro he
      exact h (by have hn : n=m := Fin.ext he; subst m; rfl)
    · left
      intro he
      apply hrs
      apply Fin.ext
      dsimp [oddPairDeficit] at he
      omega

theorem pairCoupledBasis_complete (Q : ℕ) :
    pairCoupledBasis Q * (pairCoupledBasis Q)ᵀ = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq (m := PairCoupledIndex Q) (n := WedgePairIndex Q)
    (R := ℝ) (pairCoupledIndex_card Q)).mp (pairCoupledBasis_isometry Q)

end Laughlin.Spin

end OAI
