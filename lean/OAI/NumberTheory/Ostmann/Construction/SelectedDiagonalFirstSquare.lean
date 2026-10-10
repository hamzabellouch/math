import OAI.NumberTheory.Ostmann.Construction.DiagonalSingleEnergy
import OAI.NumberTheory.Ostmann.Construction.SelectedCounterpartFirstSquare
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalNormalizer

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
namespace InitialSourceChoice
open Conclusion Arithmetic.HistoryProductWindows
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (s l : ℕ) (X : ℝ) (outside : List ℕ)
local notation "b₀" => (bulkSize k L/2)
local notation "seed" => Template.initial (2*b₀) k
local notation "T" => Template.remainder (l+1) (Template.current seed l)
local notation "U" => Template.extracted (l+1) (Template.current seed l)
local notation "V" => frequencyBound Bs BD Bz k L
local notation "bins" => Arithmetic.sourceStateBins b₀ s C.bulkBin C.spectatorBin

def selectedFirstSquare (p : ℕ) (u : SourceAssignment C.sources U)
    (x : RemainingSample C.sources T C.giant) (v : AllowedFrequency V l) : ℝ :=
  (remainingPrior C.sources T C.giant).mass x*
    diagonalSmallTerm d C.sources seed V C.giant outside l p u (x,v)*
      ‖diagonalCoefficientTerm d C.sources seed V C.giant X C.giantCenter bins outside l p u (x,v)‖^2

theorem selectedFirstSquare_nonneg (p : ℕ) (u : SourceAssignment C.sources U)
    (x : RemainingSample C.sources T C.giant) (v : AllowedFrequency V l) :
    0≤C.selectedFirstSquare s l X outside p u x v :=
  mul_nonneg (mul_nonneg ((remainingPrior _ _ _).mass_nonneg _)
    (diagonalSmallMultiplier_nonneg _ _ _ _ _)) (sq_nonneg _)

theorem counterpart_mass_first_square_bound (hl : l<k)
    (p : ℕ) (u : SourceAssignment C.sources U)
    (hu : (assignmentPrior C.sources U).mass u≠0)
    (x : RemainingSample C.sources T C.giant) (v : AllowedFrequency V l)
    (e : Equiv.Perm (RemainingIndex T)) (he : CounterpartCompatible C.sources T C.giant x e) :
    ((((assignedSlots C.sources U u).map SmallSlot.value).prod:ℝ)*
      Ostmann.smoothPartition (Real.log p-C.giantCenter))*
      (remainingPrior C.sources T C.giant).mass (reconstructCounterpart C.sources T C.giant x e he)*
      C.selectedFirstSquare s l X outside p u x v≤
    (C.selectedDiagonalNormalizer l*externalPivotWeight C.giantCenter p*
      Real.exp (nominalInheritedWidth k l+nominalRemovedWidth k l))*
      C.selectedFirstSquare s l X outside p u x v := by
  by_cases hx : (remainingPrior C.sources T C.giant).mass x=0
  · simp only [selectedFirstSquare,hx,zero_mul,mul_zero,le_refl]
  by_cases hA : diagonalCoefficientTerm d C.sources seed V C.giant X C.giantCenter bins outside l p u (x,v)=0
  · simp only [selectedFirstSquare,hA,norm_zero,zero_pow (by decide : 2≠0),mul_zero,le_refl]
  have hK := (C.counterpart_bound_of_first_coefficient s l hl X outside p u x v.val hu hx hA e he).2
  have hmass := C.remaining_mass_scalar_extraction seed (fun q hq => hq) (l+1) l
    (C.compensationLogScale l) (stepGap BD Bz k L l) p u (reconstructCounterpart C.sources T C.giant x e he)
  rw [hmass]
  apply mul_le_mul_of_nonneg_right _ (C.selectedFirstSquare_nonneg s l X outside p u x v)
  exact mul_le_mul_of_nonneg_left hK
    (mul_nonneg (C.selectedDiagonalNormalizer_nonneg l) (externalPivotWeight_nonneg _ _))

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
