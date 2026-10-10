import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedScalarExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedModulusExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedMeasuredTransport

namespace OAI

/-! # Range draws with an executed modulus initialization -/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedMeasured

def rangeInitialized (w n D : ℕ) (hD : 1 < D) (hw : Nat.clog 2 D ≤ w) :
    Execution (WordSeedRealization.range w n D hD hw) where
  run stream cursor :=
    let scalar := WordSeedModulusExecution.run D
    let r := (range w n D hD hw scalar.modulus
      (WordSeedModulusExecution.run_modulus D)).run stream cursor
    ⟨r.accepted,r.cursor,scalar.work+r.work+1,max 16 (r.cells+8),r.retained⟩
  value stream cursor :=
    (range w n D hD hw (WordSeedModulusExecution.run D).modulus
      (WordSeedModulusExecution.run_modulus D)).value stream cursor

theorem rangeInitialized_bounded (w n D : ℕ) (hD : 1 < D) (hw : Nat.clog 2 D ≤ w) :
    (rangeInitialized w n D hD hw).Bounded
      (13*n^3+5*Nat.clog 2 D+17) (2*n^3+104) (n^3+18) := by
  intro stream cursor
  have h := range_bounded w n D hD hw (WordSeedModulusExecution.run D).modulus
    (WordSeedModulusExecution.run_modulus D) stream cursor
  dsimp only [rangeInitialized]
  rw [WordSeedModulusExecution.run_work]
  exact ⟨by omega,max_le (by omega) (by omega),h.2.2⟩

def fin (w n D : ℕ) [NeZero D] (hw : Nat.clog 2 D ≤ w) :
    Execution (WordSeedRealization.fin w n D hw) :=
  if h : 1 < D then
    transportSampler (by simp only [finCoupling,dite_eq_left h])
      (source_fin_pos w n D hw h) (rangeInitialized w n D h hw)
  else
    transportSampler (by simp only [finCoupling,dite_eq_right h])
      (source_fin_neg w n D hw h)
      (enlarge (pure (w := w) (⟨0,Nat.pos_of_ne_zero (NeZero.ne D)⟩ : Fin D))
        (Nat.zero_le (n^3)))

theorem fin_bounded (w n D : ℕ) [NeZero D] (hw : Nat.clog 2 D ≤ w) :
    (fin w n D hw).Bounded (13*n^3+5*Nat.clog 2 D+17) (2*n^3+104) (n^3+18) := by
  unfold fin
  split
  next h =>
    exact transportSampler_bounded _ _ _ _ _ _ (rangeInitialized_bounded w n D h hw)
  next h =>
    apply bounded_mono _ (transportSampler_bounded _ _ _ 1 4 4
      (enlarge_bounded _ _ _ _ _ (pure_bounded _))) <;> omega

end LowSpaceSubsetSum.WordSeedMeasured

end

end OAI
