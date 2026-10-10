import OAI.NumberTheory.Ostmann.Construction.CounterpartCutoff
import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindexFinal

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace Ostmann.Construction
namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (seed : List SourceSlot)
    (V : ℕ→ℕ) (X : ℝ) (bins : List ℕ→State→ℝ) (outside : List ℕ)
    (l : ℕ) (B Δ : ℝ)
local notation "T" => Template.remainder (l+1) (Template.current seed l)
local notation "U" => Template.extracted (l+1) (Template.current seed l)

def correctedCounterpartTerm (u : SourceAssignment C.sources U)
    (x : RemainingSample C.sources T C.giant)
    (F : RemainingSample C.sources T C.giant→ℂ) (e : Equiv.Perm (RemainingIndex T)) : ℂ :=
  if he : CounterpartCompatible C.sources T C.giant x e then
    if PreservesRemainingBands T e then
      let y := reconstructCounterpart C.sources T C.giant x e he
      (remainingCounterpart C.sources (Template.current seed l) (l+1) C.giant
        (C.giantCenter+B+Δ) B C.giantCenter (C.cells.center (Conclusion.bulkSize k L/2)) u y:ℂ)*F y
    else 0
  else 0

def correctedSmallCounterpartExpression (p : ℕ) (u : SourceAssignment C.sources U)
    (e : Equiv.Perm (RemainingIndex T)) : ℂ :=
  ∑x : RemainingSample C.sources T C.giant,∑v : AllowedFrequency V l,
    ((remainingPrior C.sources T C.giant).mass x:ℂ)*
      (diagonalSmallTerm d C.sources seed V C.giant outside l p u (x,v):ℂ)*
      diagonalCoefficientTerm d C.sources seed V C.giant X C.giantCenter bins outside l p u (x,v)*
      conj (C.correctedCounterpartTerm seed l B Δ u x
        (fun y => diagonalCoefficientTerm d C.sources seed V C.giant X C.giantCenter bins outside l p u (y,v)) e)

theorem fixedCounterpartTerm_scalar_extraction
    (hseed : ∀q∈seed,q∈Template.initial (2*(Conclusion.bulkSize k L/2)) k)
    (p : ℕ) (u : SourceAssignment C.sources U) (x : RemainingSample C.sources T C.giant)
    (F : RemainingSample C.sources T C.giant→ℂ) (e : Equiv.Perm (RemainingIndex T)) :
    (((((assignedSlots C.sources U u).map SmallSlot.value).prod:ℝ)*
      Ostmann.smoothPartition (Real.log p-C.giantCenter)):ℂ)*
      fixedCounterpartTerm C.sources T C.giant x F e=
    ((C.remainingNormalization T*Real.exp (-Δ)*externalPivotWeight C.giantCenter p):ℂ)*
      C.correctedCounterpartTerm seed l B Δ u x F e := by
  unfold fixedCounterpartTerm correctedCounterpartTerm
  split_ifs with hc hb
  · have h := C.remaining_mass_scalar_extraction seed hseed (l+1) l B Δ p u
      (reconstructCounterpart C.sources T C.giant x e hc)
    have hh := congrArg (fun a : ℝ => (a:ℂ)) h
    simp only [Complex.ofReal_mul] at hh ⊢
    rw [←mul_assoc,hh]
    ring
  · simp only [mul_zero]
  · simp only [mul_zero]

theorem fixedSmallCounterpartExpression_scalar_extraction
    (hseed : ∀q∈seed,q∈Template.initial (2*(Conclusion.bulkSize k L/2)) k)
    (p : ℕ) (u : SourceAssignment C.sources U) (e : Equiv.Perm (RemainingIndex T)) :
    (((((assignedSlots C.sources U u).map SmallSlot.value).prod:ℝ)*
      Ostmann.smoothPartition (Real.log p-C.giantCenter)):ℂ)*
      fixedSmallCounterpartExpression d C.sources seed V C.giant X C.giantCenter bins outside l p u e=
    ((C.remainingNormalization T*Real.exp (-Δ)*externalPivotWeight C.giantCenter p):ℂ)*
      C.correctedSmallCounterpartExpression seed V X bins outside l B Δ p u e := by
  unfold fixedSmallCounterpartExpression correctedSmallCounterpartExpression
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro v hv
  have h := congrArg (fun z : ℂ => conj z)
    (C.fixedCounterpartTerm_scalar_extraction seed l B Δ hseed p u x
      (fun y => diagonalCoefficientTerm d C.sources seed V C.giant X C.giantCenter bins outside l p u (y,v)) e)
  simp only [map_mul,Complex.conj_ofReal] at h
  calc
    _ = (((remainingPrior C.sources T C.giant).mass x:ℂ)*
      (diagonalSmallTerm d C.sources seed V C.giant outside l p u (x,v):ℂ)*
      diagonalCoefficientTerm d C.sources seed V C.giant X C.giantCenter bins outside l p u (x,v))*
      (((((assignedSlots C.sources U u).map SmallSlot.value).prod:ℝ)*
        Ostmann.smoothPartition (Real.log p-C.giantCenter):ℝ):ℂ)*
      conj (fixedCounterpartTerm C.sources T C.giant x
        (fun y => diagonalCoefficientTerm d C.sources seed V C.giant X C.giantCenter bins outside l p u (y,v)) e) := by simp only [Complex.ofReal_mul]; ring
    _ = _ := by simp only [Complex.ofReal_mul]; rw [mul_assoc,h]; ring

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
