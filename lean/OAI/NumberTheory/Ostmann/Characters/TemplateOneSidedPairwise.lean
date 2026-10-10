import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceAmplitude
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSplitBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open Preliminaries
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

def fixedPrimeSupport (p : I → ℕ) (L S : I) : Prop :=
  ∀i ∈ frozenVertices L S,∀h ∈ frozenVertices L S,i ≠ h → (p i).Coprime (p h)

def unaryPrimeSupport (p : I → ℕ) (L S : I) (q : ℕ) : Prop :=
  ∀i ∈ frozenVertices L S,q.Coprime (p i)

theorem twoPrimeAssignment_pairwise_iff (p : I → ℕ) (L S : I) (hLS : L ≠ S) (q r : ℕ) :
    Pairwise (fun i h => (twoPrimeAssignment p L S q r i).Coprime
      (twoPrimeAssignment p L S q r h)) ↔
      fixedPrimeSupport p L S ∧ unaryPrimeSupport p L S q ∧
        unaryPrimeSupport p L S r ∧ q.Coprime r := by
  constructor
  · intro h
    refine ⟨?_,?_,?_,?_⟩
    · intro i hi v hv hiv
      simpa only [twoPrimeAssignment_frozen p L S q r i hi,
        twoPrimeAssignment_frozen p L S q r v hv] using h hiv
    · intro i hi
      have hLi : L ≠ i := ((mem_frozenVertices L S i).mp hi).2.symm
      simpa only [twoPrimeAssignment_long p L S hLS q r,
        twoPrimeAssignment_frozen p L S q r i hi] using h hLi
    · intro i hi
      have hSi : S ≠ i := ((mem_frozenVertices L S i).mp hi).1.symm
      simpa only [twoPrimeAssignment_short,twoPrimeAssignment_frozen p L S q r i hi] using h hSi
    · simpa only [twoPrimeAssignment_long p L S hLS q r,twoPrimeAssignment_short] using h hLS
  · rintro ⟨hf,hq,hr,hqr⟩ i v hiv
    by_cases hiL : i=L
    · subst i
      by_cases hvS : v=S
      · subst v
        simpa only [twoPrimeAssignment_long p L S hLS q r,twoPrimeAssignment_short] using hqr
      · have hv : v ∈ frozenVertices L S := (mem_frozenVertices L S v).mpr ⟨hvS,hiv.symm⟩
        simpa only [twoPrimeAssignment_long p L S hLS q r,twoPrimeAssignment_frozen p L S q r v hv]
          using hq v hv
    · by_cases hiS : i=S
      · subst i
        by_cases hvL : v=L
        · subst v
          simpa only [twoPrimeAssignment_long p L S hLS q r,twoPrimeAssignment_short] using hqr.symm
        · have hv : v ∈ frozenVertices L S := (mem_frozenVertices L S v).mpr ⟨hiv.symm,hvL⟩
          simpa only [twoPrimeAssignment_short,twoPrimeAssignment_frozen p L S q r v hv]
            using hr v hv
      · have hi : i ∈ frozenVertices L S := (mem_frozenVertices L S i).mpr ⟨hiS,hiL⟩
        by_cases hvL : v=L
        · subst v
          simpa only [twoPrimeAssignment_long p L S hLS q r,twoPrimeAssignment_frozen p L S q r i hi]
            using (hq i hi).symm
        · by_cases hvS : v=S
          · subst v
            simpa only [twoPrimeAssignment_short,twoPrimeAssignment_frozen p L S q r i hi]
              using (hr i hi).symm
          · have hv : v ∈ frozenVertices L S := (mem_frozenVertices L S v).mpr ⟨hvS,hvL⟩
            simpa only [twoPrimeAssignment_frozen p L S q r i hi,
              twoPrimeAssignment_frozen p L S q r v hv] using hf i hi v hv hiv

def longPrimeSupportMask (p : I → ℕ) (L S : I) (q : ℕ) : ℂ :=
  if fixedPrimeSupport p L S ∧ unaryPrimeSupport p L S q then 1 else 0

def shortPrimeSupportMask (p : I → ℕ) (L S : I) (r : ℕ) : ℂ :=
  if unaryPrimeSupport p L S r then 1 else 0

theorem twoPrimeAssignment_support_indicator (p : I → ℕ) (L S : I) (hLS : L ≠ S) (q r : ℕ) :
    (if Pairwise (fun i h => (twoPrimeAssignment p L S q r i).Coprime
      (twoPrimeAssignment p L S q r h)) then (1:ℂ) else 0) =
    longPrimeSupportMask p L S q * shortPrimeSupportMask p L S r *
      (if q.Coprime r then 1 else 0) := by
  rw [twoPrimeAssignment_pairwise_iff p L S hLS q r]
  unfold longPrimeSupportMask shortPrimeSupportMask
  by_cases hf : fixedPrimeSupport p L S <;>
    by_cases hq : unaryPrimeSupport p L S q <;>
    by_cases hr : unaryPrimeSupport p L S r <;>
    by_cases hc : q.Coprime r <;> simp [hf,hq,hr,hc]

theorem twoPrimeAssignment_support_indicator_of_coprime (p : I → ℕ) (L S : I)
    (hLS : L ≠ S) (q r : ℕ) (hqr : q.Coprime r) :
    (if Pairwise (fun i h => (twoPrimeAssignment p L S q r i).Coprime
      (twoPrimeAssignment p L S q r h)) then (1:ℂ) else 0) =
      longPrimeSupportMask p L S q * shortPrimeSupportMask p L S r := by
  rw [twoPrimeAssignment_support_indicator p L S hLS q r,ite_eq_left hqr,mul_one]

theorem longPrimeSupportMask_norm_le (p : I → ℕ) (L S : I) (q : ℕ) :
    ‖longPrimeSupportMask p L S q‖ ≤ 1 := by unfold longPrimeSupportMask; split_ifs <;> simp

theorem shortPrimeSupportMask_norm_le (p : I → ℕ) (L S : I) (r : ℕ) :
    ‖shortPrimeSupportMask p L S r‖ ≤ 1 := by unfold shortPrimeSupportMask; split_ifs <;> simp

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
