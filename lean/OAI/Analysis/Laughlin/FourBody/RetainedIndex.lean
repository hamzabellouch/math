import OAI.Analysis.Laughlin.FourBody.RetainedInclusions

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

def fourCoupledDeficit {Q : ℕ} (s : FourCoupledIndex Q) : ℕ :=
  oddPairDeficit s.1+s.2.1.val

def retainedFourIndex (Q D : ℕ) (hQ : D+2 ≤ Q)
    (r : OddPairLabel D) (n : Fin (fourSpinWeight Q D+1)) : FourCoupledIndex Q :=
  ⟨⟨r.val, by have := r.isLt; omega⟩,
    ⟨⟨D-oddPairDeficit r, by
      have := oddPairDeficit_le r
      dsimp [genericCoupledWeight,oddPairDeficit] at *
      omega⟩,
      ⟨n.val, by
        have h := four_nested_weight Q D (oddPairDeficit r) hQ (oddPairDeficit_le r)
        change n.val < genericCoupledWeight (2*Q-2) (genericCoupledWeight Q Q (oddPairDeficit r)) (D-oddPairDeficit r)+1
        rw [h]
        exact n.isLt⟩⟩⟩

theorem retainedFourIndex_deficit (Q D : ℕ) (hQ : D+2 ≤ Q)
    (r : OddPairLabel D) (n : Fin (fourSpinWeight Q D+1)) :
    fourCoupledDeficit (retainedFourIndex Q D hQ r n) = D := by
  dsimp [fourCoupledDeficit,retainedFourIndex]
  have := oddPairDeficit_le r
  dsimp [oddPairDeficit] at *
  omega

theorem retainedFourIndex_column (Q D : ℕ) (hQ : D+2 ≤ Q)
    (r : OddPairLabel D) (n : Fin (fourSpinWeight Q D+1)) (i : FourWedgeIndex Q) :
    (fourCoupledBasis Q i (retainedFourIndex Q D hQ r n) : ℂ) =
      retainedFourInclusion Q D hQ r i n := by
  have hd := retainedFourIndex_deficit Q D hQ r n
  change (fourBodyCopy Q (oddPairDeficit r) _ _ _ _ n.val i : ℂ) = _
  rw [retainedFourInclusion_column]
  unfold fourCoupledDeficit at hd
  simp only [hd]

def retainedFourIndexEquiv (Q D : ℕ) (hQ : D+2 ≤ Q) :
    (OddPairLabel D × Fin (fourSpinWeight Q D+1)) ≃
      {s : FourCoupledIndex Q // fourCoupledDeficit s = D} where
  toFun x := ⟨retainedFourIndex Q D hQ x.1 x.2,retainedFourIndex_deficit Q D hQ x.1 x.2⟩
  invFun s :=
    (⟨s.val.1.val, by have := s.property; dsimp [fourCoupledDeficit,oddPairDeficit] at *; omega⟩,
     ⟨s.val.2.2.val, by
       have hd := s.property
       have hw := four_nested_weight Q D (oddPairDeficit s.val.1) hQ
         (by dsimp [fourCoupledDeficit] at hd; omega)
       have hz : D-oddPairDeficit s.val.1=s.val.2.1.val := by
         dsimp [fourCoupledDeficit] at hd; omega
       rw [hz] at hw
       rw [← hw]
       exact s.val.2.2.isLt⟩)
  left_inv x := by apply Prod.ext <;> apply Fin.ext <;> rfl
  right_inv s := by
    apply Subtype.ext
    rcases s with ⟨⟨r,⟨z,n⟩⟩,hd⟩
    dsimp [fourCoupledDeficit] at hd
    have hz : D-oddPairDeficit r=z.val := by omega
    dsimp [retainedFourIndex]
    congr 2
    · exact Fin.ext hz
    · apply (Fin.heq_ext_iff (by congr 2)).mpr
      rfl

theorem fourCoupledDeficit_pos {Q : ℕ} (s : FourCoupledIndex Q) :
    1 ≤ fourCoupledDeficit s := by dsimp [fourCoupledDeficit,oddPairDeficit]; omega

end Laughlin.Spin

end OAI
