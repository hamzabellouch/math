import OAI.Analysis.Laughlin.Spin.Endpoint
import OAI.Analysis.Laughlin.Spin.LadderGroupIntertwining

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

noncomputable def genericCoupledInclusion (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    Matrix (SpinIndex A B) (Fin (genericCoupledWeight A B z+1)) ℝ :=
  fun i n => genericUnitDescendant A B z hA hB n.val i

theorem genericCoupledInclusion_raising (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    totalRaise A B*genericCoupledInclusion A B z hA hB =
      genericCoupledInclusion A B z hA hB*raiseMatrix (genericCoupledWeight A B z) := by
  funext i n
  change (totalRaise A B *ᵥ genericUnitDescendant A B z hA hB n.val) i =
    ∑ k, genericUnitDescendant A B z hA hB k.val i * raiseMatrix (genericCoupledWeight A B z) k n
  rw [raiseMatrix_column]
  by_cases hn : 0 < n.val
  · rw [dite_eq_left hn]
    have h := genericUnitDescendant_raising_succ A B z (n.val-1) hA hB (by omega)
    rw [show n.val-1+1=n.val by omega] at h
    have he := congrFun h i
    simpa [ladder,Nat.cast_sub (show n.val-1 ≤ genericCoupledWeight A B z by omega),mul_comm] using he
  · rw [dite_eq_right hn]
    have hz : n.val=0 := by omega
    rw [hz,genericUnitDescendant_zero,genericHighest_raising_zero]
    rfl

theorem genericCoupledInclusion_lowering (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    (totalRaise A B)ᵀ*genericCoupledInclusion A B z hA hB =
      genericCoupledInclusion A B z hA hB*(raiseMatrix (genericCoupledWeight A B z))ᵀ := by
  funext i n
  change ((totalRaise A B)ᵀ *ᵥ genericUnitDescendant A B z hA hB n.val) i =
    ∑ k, genericUnitDescendant A B z hA hB k.val i * raiseMatrix (genericCoupledWeight A B z) n k
  conv_rhs => simp only [mul_comm (genericUnitDescendant A B z hA hB _ i)]
  rw [raiseMatrix_row]
  by_cases hn : n.val < genericCoupledWeight A B z
  · rw [dite_eq_left hn]
    have h := congrFun (genericUnitDescendant_lowering A B z n.val hA hB hn) i
    simpa [ladder,Nat.cast_sub (Nat.le_of_lt hn)] using h
  · rw [dite_eq_right hn]
    have hz : n.val=genericCoupledWeight A B z := by omega
    rw [hz,genericUnitDescendant_lowest]
    rfl

theorem genericCoupledInclusion_SU2 (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (g : Rotation.SourceSU2) :
    (Rotation.sourceSpinRepresentation A g ⊗ₖ Rotation.sourceSpinRepresentation B g)*
      (genericCoupledInclusion A B z hA hB).map Complex.ofReal =
      (genericCoupledInclusion A B z hA hB).map Complex.ofReal*
        Rotation.sourceSpinRepresentation (genericCoupledWeight A B z) g := by
  apply Rotation.ladder_intertwiner_SU2 A B z (genericCoupledWeight A B z)
    (by unfold genericCoupledWeight; omega)
  · intro i n hn
    simp only [Matrix.map_apply,genericCoupledInclusion,genericUnitDescendant_off A B z n.val hA hB i hn,
      Complex.ofReal_zero]
  · ext i n
    have h := congrArg Complex.ofReal (congrFun (congrFun (genericCoupledInclusion_raising A B z hA hB) i) n)
    simpa [Rotation.totalRaiseComplex,Rotation.spinRaiseComplex,Matrix.mul_apply] using h
  · ext i n
    have h := congrArg Complex.ofReal (congrFun (congrFun (genericCoupledInclusion_lowering A B z hA hB) i) n)
    simpa [Rotation.totalRaiseComplex,Rotation.spinRaiseComplex,Matrix.mul_apply,Matrix.transpose_apply] using h

noncomputable def physicalCoupledInclusion (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :=
  (-1 : ℂ)^z • (genericCoupledInclusion A B z hA hB).map Complex.ofReal

theorem physicalCoupledInclusion_SU2 (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (g : Rotation.SourceSU2) :
    (Rotation.sourceSpinRepresentation A g ⊗ₖ Rotation.sourceSpinRepresentation B g)*
      physicalCoupledInclusion A B z hA hB =
      physicalCoupledInclusion A B z hA hB*
        Rotation.sourceSpinRepresentation (genericCoupledWeight A B z) g := by
  simp only [physicalCoupledInclusion,Matrix.mul_smul,Matrix.smul_mul,genericCoupledInclusion_SU2]

end Laughlin.Spin

end OAI
