import OAI.Analysis.Laughlin.FourBody.PhysicalMatrix
import OAI.Analysis.Laughlin.FourBody.RetainedInclusions

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def retainedFourReal (Q D : ℕ) (hQ : D+2 ≤ Q) (r : OddPairLabel D) :
    Matrix (FourWedgeIndex Q) (Fin (fourSpinWeight Q D+1)) ℝ :=
  fun i n => fourBodyCopy Q (oddPairDeficit r) D
    (by have := oddPairDeficit_le r; omega)
    (by have := oddPairDeficit_le r; omega)
    (by have := oddPairDeficit_le r; unfold genericCoupledWeight; omega) n.val i

theorem retainedFourReal_complex (Q D : ℕ) (hQ : D+2 ≤ Q) (r : OddPairLabel D) :
    (retainedFourReal Q D hQ r).map Complex.ofReal = retainedFourInclusion Q D hQ r := rfl

theorem retainedFourReal_outer_trace (Q D T p j k q l i : ℕ) (hQ : D+2 ≤ Q)
    (hTQ : T+2 ≤ Q) (r s : OddPairLabel D) (hp : p+j+k=T) (hq : q+l+i=T) :
    Matrix.trace ((retainedFourReal Q D hQ r)ᵀ *
      realOuter (fourSignedUnit Q p j k) (fourSignedUnit Q q l i) * retainedFourReal Q D hQ s) =
      if D ≤ T then fourBodyCoefficient Q (oddPairDeficit r) D T p j k *
        fourBodyCoefficient Q (oddPairDeficit s) D T q l i else 0 := by
  rw [trace_cross_outer]
  by_cases hDT : D ≤ T
  · rw [ite_eq_left hDT]
    let n : Fin (fourSpinWeight Q D+1) := ⟨T-D,by unfold fourSpinWeight; omega⟩
    rw [Finset.sum_eq_single n]
    · change dotProduct (fourBodyCopy Q (oddPairDeficit r) D _ _ _ (T-D)) (fourSignedUnit Q p j k) *
        dotProduct (fourBodyCopy Q (oddPairDeficit s) D _ _ _ (T-D)) (fourSignedUnit Q q l i) = _
      rw [fourBodyCopy_signed_at_level Q (oddPairDeficit r) D T p j k
        (oddPairDeficit_odd r) (oddPairDeficit_le r) hDT hTQ hp,
        fourBodyCopy_signed_at_level Q (oddPairDeficit s) D T q l i
        (oddPairDeficit_odd s) (oddPairDeficit_le s) hDT hTQ hq]
    · intro m hm hmn
      change dotProduct (fourBodyCopy Q (oddPairDeficit r) D _ _ _ m.val) (fourSignedUnit Q p j k) * _ = 0
      rw [fourBodyCopy_signed_off Q (oddPairDeficit r) D m.val p j k _ (oddPairDeficit_le r) _ _ (by
        intro he; apply hmn; apply Fin.ext; dsimp [n]; omega),zero_mul]
    · simp
  · rw [ite_eq_right hDT]
    apply Finset.sum_eq_zero
    intro n hn
    change dotProduct (fourBodyCopy Q (oddPairDeficit r) D _ _ _ n.val) (fourSignedUnit Q p j k) * _ = 0
    rw [fourBodyCopy_signed_off Q (oddPairDeficit r) D n.val p j k _ (oddPairDeficit_le r) _ _ (by omega),zero_mul]

theorem fourBodyTermMatrix_trace (Q D t : ℕ) (hQ : D+2 ≤ Q) (r s : OddPairLabel D)
    (e f : ℕ × ℕ × ℤ) (he : t ≤ e.1+e.2.1) (hf : t ≤ f.1+f.2.1)
    (hTQ : e.1+e.2.1+(f.1+f.2.1-t)+2 ≤ Q) :
    Matrix.trace ((retainedFourReal Q D hQ r)ᵀ * fourBodyTermMatrix Q t e f *
      retainedFourReal Q D hQ s) = -fourErrorEntry Q D (oddPairDeficit r) (oddPairDeficit s) t e f := by
  rw [fourBodyTermMatrix,Matrix.mul_smul,Matrix.smul_mul,Matrix.trace_smul,
    retainedFourReal_outer_trace Q D (e.1+e.2.1+(f.1+f.2.1-t)) _ _ _ _ _ _ hQ hTQ r s rfl (by omega)]
  unfold fourErrorEntry
  dsimp only
  split_ifs <;> simp only [smul_eq_mul] <;> ring

end Laughlin.Spin

end OAI
