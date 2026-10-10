import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantCompensationErrorSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantOriginalMeanApproximation

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantOriginalMeanFactorization
open Construction Conclusion Filter HistoryGiantCompensationError HistoryGiantReferenceMean
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem norm_compensationFactor (C : InitialSourceChoice d Bs BD Bz k L E)
    (x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (s t : ℤ) (c e : Choices (l:=l) C) :
    ‖compensationFactor C x y s t c e‖ =
      ((decodeHistory C.sources _ (frequencyBound Bs BD Bz k L) l
        (sourceState C.sources _ x s) c).compensationProduct:ℝ)*
      ((decodeHistory C.sources _ (frequencyBound Bs BD Bz k L) l
        (sourceState C.sources _ y t) e).compensationProduct:ℝ) := by
  simp only [compensationFactor,norm_mul,norm_natCast]

theorem selected_compensationFactor_error_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase → C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 → |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀l≤k,
      ∀(x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
        (s t : ℤ)(c e : Choices (l:=l) C),
      choicesMass C.sources _ _ l c≠0 → choicesMass C.sources _ _ l e≠0 →
      ‖compensationFactor C x y s t c e‖*(30*Real.exp (-Real.exp (ScaleBudget.giant.target*L))) ≤
        Real.exp (-Real.exp ((21/2000:ℝ)*L)) := by
  filter_upwards [selected_compensation_error_eventually d Bs BD Bz 0 (by norm_num) hk] with L hL
  intro E C hG hcl hcu hb hd l hl x y s t c e hc he
  rw [norm_compensationFactor]
  simpa only [mul_one] using hL E C hG hcl hcu hb hd (2*(bulkSize k L/2)) l hl
    (frequencyBound Bs BD Bz k L) (sourceState C.sources _ x s) (sourceState C.sources _ y t)
    c e (Template.assignedSlots_matches C.sources _ x) (Template.assignedSlots_matches C.sources _ y)
    hc he 1 (by norm_num) (by simp [rawLogBudget])

end Ostmann.Arithmetic.HistoryGiantOriginalMeanFactorization

end

end OAI
