import OAI.Combinatorics.Ryser.Construction.LinearPlacement
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]

def embeddedUnits (σ : k →+* F) : kˣ →* Fˣ := Units.map σ.toMonoidHom

theorem embeddedUnits_injective (σ : k →+* F) : Function.Injective (embeddedUnits σ) :=
  Units.map_injective σ.injective

def smallUnitSubgroup (σ : k →+* F) : Subgroup Fˣ := (embeddedUnits σ).range

abbrev CosetIndex (σ : k →+* F) := Fˣ ⧸ smallUnitSubgroup σ

def unitCoset (σ : k →+* F) (a : Fˣ) : CosetIndex σ := QuotientGroup.mk a

def cosetRepresentative (σ : k →+* F) (c : CosetIndex σ) : Fˣ := by
  classical
  exact if c = 1 then 1 else c.out

@[simp] theorem cosetRepresentative_one (σ : k →+* F) :
    cosetRepresentative σ 1 = 1 := by
  classical
  simp [cosetRepresentative]

@[simp] theorem unitCoset_representative (σ : k →+* F) (c : CosetIndex σ) :
    unitCoset σ (cosetRepresentative σ c) = c := by
  classical
  by_cases hc : c = 1
  · subst c
    simp [cosetRepresentative, unitCoset]
  · simp only [cosetRepresentative, ite_eq_right hc, unitCoset]
    exact Quotient.out_eq' c

theorem cosetRepresentative_injective (σ : k →+* F) :
    Function.Injective (cosetRepresentative σ) := by
  intro c d hcd
  have h := congrArg (unitCoset σ) hcd
  simpa only [unitCoset_representative] using h

theorem unitCoset_eq_iff (σ : k →+* F) (a b : Fˣ) :
    unitCoset σ a = unitCoset σ b ↔
      ∃ u : kˣ, embeddedUnits σ u = a / b := by
  change (a : Fˣ ⧸ smallUnitSubgroup σ) = b ↔ _
  rw [QuotientGroup.eq_iff_div_mem]
  rfl

theorem unitCoset_eq_one_iff (σ : k →+* F) (a : Fˣ) :
    unitCoset σ a = 1 ↔ ∃ u : kˣ, embeddedUnits σ u = a := by
  change (a : Fˣ ⧸ smallUnitSubgroup σ) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  rfl

theorem exists_embeddedUnit_mul_representative (σ : k →+* F) (a : Fˣ) :
    ∃ u : kˣ, a = embeddedUnits σ u * cosetRepresentative σ (unitCoset σ a) := by
  have hc : unitCoset σ a =
      unitCoset σ (cosetRepresentative σ (unitCoset σ a)) := by simp
  obtain ⟨u, hu⟩ := (unitCoset_eq_iff σ _ _).mp hc
  refine ⟨u, ?_⟩
  rw [hu, div_mul_cancel]

abbrev ConfigurationGroup (σ : k →+* F) := Option (CosetIndex σ)

def identityGroup (σ : k →+* F) : ConfigurationGroup σ := some 1

def extraGroup (σ : k →+* F) : ConfigurationGroup σ := none

theorem natCard_smallUnitSubgroup (σ : k →+* F) :
    Nat.card (smallUnitSubgroup σ) = Nat.card k - 1 := by
  calc
    Nat.card (smallUnitSubgroup σ) = Nat.card kˣ :=
      (Nat.card_congr (MonoidHom.ofInjective (embeddedUnits_injective σ)).toEquiv).symm
    _ = Nat.card k - 1 := Nat.card_units k

theorem natCard_cosetIndex_mul (σ : k →+* F) :
    Nat.card (CosetIndex σ) * (Nat.card k - 1) = Nat.card F - 1 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (smallUnitSubgroup σ)
  rw [Nat.card_units, natCard_smallUnitSubgroup] at h
  exact h.symm

section Finite

variable [instFintypek : Fintype k] [Fintype F]

instance (σ : k →+* F) : Fintype (CosetIndex σ) := Fintype.ofFinite _

theorem card_cosetIndex_mul (σ : k →+* F) :
    Fintype.card (CosetIndex σ) * (Fintype.card k - 1) = Fintype.card F - 1 := by
  simpa only [Nat.card_eq_fintype_card] using natCard_cosetIndex_mul σ

theorem card_configurationGroup (σ : k →+* F) :
    Fintype.card (ConfigurationGroup σ) = Fintype.card (CosetIndex σ) + 1 := let _ := instFintypek;
  Fintype.card_option

end Finite

end RyserCoveringCounterexample.Construction

end

end OAI
