import OAI.NumberTheory.Ostmann.Construction.DiagonalBadPair
import OAI.NumberTheory.Ostmann.Construction.DiagonalBadPairCount
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalFirstSquare

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
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
local notation "Bad" => diagonalBadPermutation (2*b₀) k l

def selectedRemainingEnergy (p : ℕ) (u : SourceAssignment C.sources U) : ℝ :=
  (remainingPrior C.sources T C.giant).mean (fun x => ∑v : AllowedFrequency V l,
    diagonalSmallTerm d C.sources seed V C.giant outside l p u (x,v)*
      ‖diagonalCoefficientTerm d C.sources seed V C.giant X C.giantCenter bins outside l p u (x,v)‖^2)

theorem selectedFirstSquare_sum (p : ℕ) (u : SourceAssignment C.sources U) :
    (∑v : AllowedFrequency V l,∑x,C.selectedFirstSquare s l X outside p u x v)=
      C.selectedRemainingEnergy s l X outside p u := by
  unfold selectedFirstSquare selectedRemainingEnergy FinitePrior.mean
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum,mul_assoc]

theorem fixed_bad_weighted_le_single_energy (hl : l<k)
    (p : ℕ) (u : SourceAssignment C.sources U)
    (hu : (assignmentPrior C.sources U).mass u≠0)
    (hsep : ∀i : Fin (T).length,C.giant.DisjointMass (C.sources T[i].origin)) :
    ((((assignedSlots C.sources U u).map SmallSlot.value).prod:ℝ)*
      Ostmann.smoothPartition (Real.log p-C.giantCenter))*
      (∑e,if Bad e then fixedSmallCounterpartExpression d C.sources seed V C.giant X C.giantCenter
        bins outside l p u e else 0).re≤
    C.selectedDiagonalNormalizer l*(Nat.card {e // Bad e}:ℝ)*
      Real.exp (nominalInheritedWidth k l+nominalRemovedWidth k l)*
      externalPivotWeight C.giantCenter p*C.selectedRemainingEnergy s l X outside p u := by
  let w : ℝ := (((assignedSlots C.sources U u).map SmallSlot.value).prod:ℝ)*
    Ostmann.smoothPartition (Real.log p-C.giantCenter)
  let K : ℝ := Real.exp (nominalInheritedWidth k l+nominalRemovedWidth k l)
  let c : ℝ := C.selectedDiagonalNormalizer l*externalPivotWeight C.giantCenter p*K
  have hw : 0≤w := mul_nonneg (Nat.cast_nonneg _) (Ostmann.smoothPartition_nonneg _)
  have hc : 0≤c := mul_nonneg
    (mul_nonneg (C.selectedDiagonalNormalizer_nonneg _) (externalPivotWeight_nonneg _ _)) (Real.exp_pos _).le
  have hbound (v : AllowedFrequency V l) := badCounterpartPair_first_square_le
    C.sources T C.giant Bad w c (fun x => C.selectedFirstSquare s l X outside p u x v) hc
    (fun x => C.selectedFirstSquare_nonneg s l X outside p u x v)
    (fun x e he _ => C.counterpart_mass_first_square_bound s l X outside hl p u hu x v e he)
  have hpair := fixedSmallCounterpartExpression_transferBad_le_square d C.sources (2*b₀) k V
    C.giant X C.giantCenter bins outside l p u hsep
  calc
    _ ≤ w*(∑v : AllowedFrequency V l,∑z : BadCounterpartPair C.sources T C.giant Bad,
        ((remainingPrior C.sources T C.giant).mass z.val.1*
          (remainingPrior C.sources T C.giant).mass
            (reconstructCounterpart C.sources T C.giant z.val.1 z.val.2 z.property.1)*
          diagonalSmallTerm d C.sources seed V C.giant outside l p u (z.val.1,v))*
          ‖diagonalCoefficientTerm d C.sources seed V C.giant X C.giantCenter bins outside l p u (z.val.1,v)‖^2) :=
      mul_le_mul_of_nonneg_left hpair hw
    _ = ∑v : AllowedFrequency V l,∑z : BadCounterpartPair C.sources T C.giant Bad,
        w*(remainingPrior C.sources T C.giant).mass
          (reconstructCounterpart C.sources T C.giant z.val.1 z.val.2 z.property.1)*
          C.selectedFirstSquare s l X outside p u z.val.1 v := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro z hz
      unfold selectedFirstSquare
      ring
    _ ≤ ∑v : AllowedFrequency V l,(Nat.card {e // Bad e}:ℝ)*c*
        (∑x,C.selectedFirstSquare s l X outside p u x v) :=
      Finset.sum_le_sum (fun v _ => hbound v)
    _ = (Nat.card {e // Bad e}:ℝ)*c*C.selectedRemainingEnergy s l X outside p u := by
      rw [←Finset.mul_sum,C.selectedFirstSquare_sum s l X outside p u]
    _ = _ := by dsimp only [c,K]; ring

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
