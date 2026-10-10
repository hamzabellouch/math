import Mathlib

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Invariant233.CoordinateSwap

variable {X : Type*} [MeasurableSpace X]

def flatten : ((ℕ → X) × (ℕ → X)) ≃ᵐ (Fin 2 × ℕ → X) :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.curry (Fin 2) ℕ X).symm

def swapIndex (I : Finset ℕ) : Fin 2 × ℕ ≃ Fin 2 × ℕ where
  toFun p := (if p.2 ∈ I then Equiv.swap 0 1 p.1 else p.1, p.2)
  invFun p := (if p.2 ∈ I then Equiv.swap 0 1 p.1 else p.1, p.2)
  left_inv p := by rcases p with ⟨a,n⟩; by_cases hn : n ∈ I <;> simp [hn]
  right_inv p := by rcases p with ⟨a,n⟩; by_cases hn : n ∈ I <;> simp [hn]

def swapEquiv (I : Finset ℕ) : ((ℕ → X) × (ℕ → X)) ≃ᵐ ((ℕ → X) × (ℕ → X)) :=
  (flatten.trans (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 × ℕ => X) (swapIndex I))).trans
    flatten.symm

theorem measurePreserving_flatten (μ : Measure X) [IsProbabilityMeasure μ] :
    MeasurePreserving (flatten (X := X))
      ((Measure.infinitePi (fun _ : ℕ => μ)).prod (Measure.infinitePi (fun _ : ℕ => μ)))
      (Measure.infinitePi (fun _ : Fin 2 × ℕ => μ)) := by
  have hp := MeasurePreserving.symm MeasurableEquiv.finTwoArrow
    (measurePreserving_finTwoArrow (Measure.infinitePi (fun _ : ℕ => μ)))
  have hc : MeasurePreserving (MeasurableEquiv.curry (Fin 2) ℕ X).symm
      (Measure.infinitePi (fun _ : Fin 2 => Measure.infinitePi (fun _ : ℕ => μ)))
      (Measure.infinitePi (fun _ : Fin 2 × ℕ => μ)) := by
    exact ⟨(MeasurableEquiv.curry (Fin 2) ℕ X).symm.measurable,
      Measure.infinitePi_map_curry_symm (fun _ : Fin 2 => fun _ : ℕ => μ)⟩
  apply hp.trans
  simpa only [Measure.infinitePi_eq_pi] using hc

theorem measurePreserving_swap (μ : Measure X) [IsProbabilityMeasure μ] (I : Finset ℕ) :
    MeasurePreserving (swapEquiv (X := X) I)
      ((Measure.infinitePi (fun _ : ℕ => μ)).prod (Measure.infinitePi (fun _ : ℕ => μ)))
      ((Measure.infinitePi (fun _ : ℕ => μ)).prod (Measure.infinitePi (fun _ : ℕ => μ))) := by
  have hr : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 × ℕ => X) (swapIndex I))
      (Measure.infinitePi (fun _ : Fin 2 × ℕ => μ))
      (Measure.infinitePi (fun _ : Fin 2 × ℕ => μ)) :=
    ⟨(MeasurableEquiv.piCongrLeft _ _).measurable,
      Measure.infinitePi_map_piCongrLeft (fun _ : Fin 2 × ℕ => μ) (swapIndex I)⟩
  exact ((measurePreserving_flatten μ).trans hr).trans
    (MeasurePreserving.symm flatten (measurePreserving_flatten μ))

theorem swapEquiv_fst (I : Finset ℕ) (xz : (ℕ → X) × (ℕ → X)) (i : ℕ) :
    (swapEquiv I xz).1 i = if i ∈ I then xz.2 i else xz.1 i := by
  by_cases hi : i ∈ I <;>
    simp [swapEquiv, flatten, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
      swapIndex, hi, MeasurableEquiv.finTwoArrow, MeasurableEquiv.piFinTwo,
      MeasurableEquiv.curry]

theorem swapEquiv_snd (I : Finset ℕ) (xz : (ℕ → X) × (ℕ → X)) (i : ℕ) :
    (swapEquiv I xz).2 i = if i ∈ I then xz.1 i else xz.2 i := by
  by_cases hi : i ∈ I <;>
    simp [swapEquiv, flatten, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
      swapIndex, hi, MeasurableEquiv.finTwoArrow, MeasurableEquiv.piFinTwo,
      MeasurableEquiv.curry]

end Invariant233.CoordinateSwap

end OAI
