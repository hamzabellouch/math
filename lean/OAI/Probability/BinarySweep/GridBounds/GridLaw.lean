import Mathlib
import OAI.Probability.BinarySweep.Analytic.OneAxis
import OAI.Probability.BinarySweep.GridBounds.BoardLaw
import OAI.Probability.BinarySweep.Mixing.BinarySplitChoices

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
open GridSplit

def gridLaw {b : ℕ} (bits : Fin b → ℕ) : Equiv.Perm (GridSlot bits) → ℝ :=
  pushLaw (gridWeight bits 1) (gridSweep bits)

lemma pushLaw_inverse {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : A → ℝ) : pushLaw (pushLaw p e) e.symm=p := by
  rw [pushLaw_comp]
  have he : e.symm ∘ e = id := funext e.symm_apply_apply
  rw [he,pushLaw_id]

lemma pushLaw_injective {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) : Function.Injective (fun p : A → ℝ => pushLaw p e) := by
  intro p q he
  have hh := congrArg (fun w => pushLaw w e.symm) he
  simpa only [pushLaw_inverse] using hh

lemma binary_splitLaw (m n : ℕ) :
    pushLaw (binaryLaw (m+n)) Signed.splitWord.permCongr=
      boardLaw (binaryLaw m) (binaryLaw n) := by
  unfold binaryLaw
  rw [finiteLaw_pushLaw,finiteLaw_pushLaw,finiteLaw_pushLaw,pushLaw_comp]
  let e := BinarySplit.choicesEquiv (m:=m) (n:=n)
  have hs : Signed.splitWord.permCongr ∘ binarySweep (m+n)=
      (fun LR : (Slot n → SweepCoins m) × (Slot m → SweepCoins n) =>
        columnPerm (binarySweep n ∘ LR.2)*rowPerm (binarySweep m ∘ LR.1)) ∘ e :=
    funext BinarySplit.binarySweep_split
  rw [hs,←uniformLaw_equiv e,pushLaw_equiv]
  have hu : uniformLaw ((Slot n → SweepCoins m)×(Slot m → SweepCoins n))=
      fun LR => (∏y,uniformLaw (SweepCoins m) (LR.1 y))*
        (∏x,uniformLaw (SweepCoins n) (LR.2 x)) := by
    rw [uniformLaw_prod]
    simp only [uniformLaw_pi (I:=Slot n) (A:=fun _ => SweepCoins m),
      uniformLaw_pi (I:=Slot m) (A:=fun _ => SweepCoins n)]
  rw [hu]
  exact boardSampleLaw _ _ _ _

lemma grid_splitLaw {m n : ℕ} (bits : Fin (m+n) → ℕ) :
    pushLaw (gridLaw bits) (slotEquiv (m:=m) (n:=n) bits).permCongr=
      boardLaw (gridLaw (leftBits (m:=m) (n:=n) bits)) (gridLaw (rightBits (m:=m) (n:=n) bits)) := by
  let : DecidableEq (GridSlot (leftBits (m:=m) (n:=n) bits)) := inferInstance
  let : DecidableEq (GridSlot (rightBits (m:=m) (n:=n) bits)) := inferInstance
  let : Fintype (GridChoices (leftBits (m:=m) (n:=n) bits)) := inferInstance
  let : Fintype (GridChoices (rightBits (m:=m) (n:=n) bits)) := inferInstance
  unfold gridLaw
  rw [pushLaw_comp]
  exact board_equiv_sample
    (gridWeight (leftBits (m:=m) (n:=n) bits) 1)
    (gridWeight (rightBits (m:=m) (n:=n) bits) 1)
    (gridSweep (leftBits (m:=m) (n:=n) bits))
    (gridSweep (rightBits (m:=m) (n:=n) bits))
    (GridSplit.choicesEquiv (m:=m) (n:=n) bits) _ _
    (gridWeight_split (m:=m) (n:=n) bits 1) (gridSweep_split (m:=m) (n:=n) bits)

lemma oneAxis_gridLaw (bits : Fin 1 → ℕ) :
    pushLaw (gridLaw bits) (oneAxisSlotEquiv bits).permCongr=binaryLaw (bits 0) := by
  unfold gridLaw
  rw [pushLaw_comp]
  have hw : gridWeight bits 1=binaryLaw (bits 0) ∘ oneAxisChoiceEquiv bits := by
    funext c
    simp [oneAxis_gridWeight,lineLaw]
  have hs : (oneAxisSlotEquiv bits).permCongr ∘ gridSweep bits=oneAxisChoiceEquiv bits := by
    funext c
    rw [Function.comp_apply,←oneAxisSweepEquiv_apply]
    exact (oneAxisSlotEquiv bits).permCongr.apply_symm_apply _
  rw [hw,hs]
  have hh := pushLaw_equiv (oneAxisChoiceEquiv bits) (binaryLaw (bits 0)) id
  simpa only [Function.id_comp,pushLaw_id] using hh

theorem gridLaw_binary : ∀b : ℕ, 1≤b → ∀bits : Fin b → ℕ,
    ∃d : ℕ, d=∑j,bits j ∧ ∃e : GridSlot bits ≃ Slot d,
      pushLaw (gridLaw bits) e.permCongr=binaryLaw d := by
  intro b
  induction b using Nat.case_strong_induction_on with
  | hz => intro hb; omega
  | hi b ih =>
    intro hb bits
    by_cases hb0 : b=0
    · subst b
      exact ⟨bits 0,by simp,oneAxisSlotEquiv bits,oneAxis_gridLaw bits⟩
    obtain ⟨dL,hdL,eL,heL⟩ := ih b (by omega) (by omega) (leftBits (n:=1) bits)
    let eR := oneAxisSlotEquiv (rightBits (m:=b) bits)
    have heR := oneAxis_gridLaw (rightBits (m:=b) bits)
    let dR := rightBits (m:=b) (n:=1) bits 0
    let ep := Equiv.prodCongr eL eR
    let e := ((slotEquiv (m:=b) (n:=1) bits).trans ep).trans Signed.splitWord.symm
    refine ⟨dL+dR,?_,e,?_⟩
    · rw [Fin.sum_univ_add,←hdL]
      simp [dR]
    · apply pushLaw_injective Signed.splitWord.permCongr
      change pushLaw (pushLaw (gridLaw bits) e.permCongr) Signed.splitWord.permCongr=
        pushLaw (binaryLaw (dL+dR)) Signed.splitWord.permCongr
      rw [binary_splitLaw,pushLaw_comp]
      have he : Signed.splitWord.permCongr ∘ e.permCongr=
          ep.permCongr ∘ (slotEquiv (m:=b) (n:=1) bits).permCongr := by
        funext σ
        apply Equiv.ext
        intro xy
        simp [e,Equiv.permCongr_apply]
      let : DecidableEq (GridSlot (leftBits (m:=b) (n:=1) bits) × GridSlot (rightBits (m:=b) (n:=1) bits)) := inferInstance
      rw [he,←pushLaw_comp (gridLaw bits) (slotEquiv (m:=b) (n:=1) bits).permCongr ep.permCongr]
      rw [grid_splitLaw (m:=b) (n:=1)]
      change pushLaw (boardLaw _ _) (Equiv.prodCongr eL eR).permCongr = _
      rw [boardLaw_congr eL eR,heL,heR]

end BinaryCoordinateSweeps

end

end OAI
