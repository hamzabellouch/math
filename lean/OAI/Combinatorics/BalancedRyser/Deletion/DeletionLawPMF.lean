import OAI.Combinatorics.BalancedRyser.Deletion.Deletion
import OAI.Combinatorics.BalancedRyser.Deletion.DeletionCoordinates
import OAI.Combinatorics.BalancedRyser.Deletion.DeletionLawNormalization

namespace OAI

noncomputable section

namespace Balanced.DeletionLaw
open scoped _root_.Balanced

open Finset

abbrev ValidArray (q n : ℕ) :=
  {D : DeletionSet q n // ∀ i, (D i).card = 3}

variable {q n : ℕ} {κ : Weight q n}

theorem sum_conditionedDeletionMass_valid
    (hκ : IsSubprobabilityKernel κ) (hdistinct : DistinctOutput κ)
    (hsuccess : 0 < successMass κ) :
    ∑ D : ValidArray q n, conditionedDeletionMass κ D.val = 1 := by
  classical
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun D : DeletionSet q n => ∀ i, (D i).card = 3) (conditionedDeletionMass κ)
  have hzero : (∑ D : {D : DeletionSet q n // ¬ ∀ i, (D i).card = 3},
      conditionedDeletionMass κ D.val) = 0 := by
    exact sum_eq_zero (fun D _ =>
      conditionedDeletionMass_eq_zero_of_invalid hκ hdistinct D.val D.property)
  rw [hzero, add_zero, sum_conditionedDeletionMass hsuccess] at hsplit
  exact hsplit

def returnedArrayLaw (hκ : IsSubprobabilityKernel κ)
    (hdistinct : DistinctOutput κ) (hsuccess : 0 < successMass κ) :
    PMF (ValidArray q n) :=
  PMF.ofFintype (fun D => ENNReal.ofReal (conditionedDeletionMass κ D.val)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun D _ => conditionedDeletionMass_nonneg hκ D.val)]
    rw [sum_conditionedDeletionMass_valid hκ hdistinct hsuccess]
    simp)

@[simp] theorem returnedArrayLaw_apply (hκ : IsSubprobabilityKernel κ)
    (hdistinct : DistinctOutput κ) (hsuccess : 0 < successMass κ)
    (D : ValidArray q n) :
    returnedArrayLaw hκ hdistinct hsuccess D =
      ENNReal.ofReal (conditionedDeletionMass κ D.val) := rfl

@[simp] theorem returnedArrayLaw_apply_toReal (hκ : IsSubprobabilityKernel κ)
    (hdistinct : DistinctOutput κ) (hsuccess : 0 < successMass κ)
    (D : ValidArray q n) :
    (returnedArrayLaw hκ hdistinct hsuccess D).toReal =
      conditionedDeletionMass κ D.val := by
  rw [returnedArrayLaw_apply, ENNReal.toReal_ofReal (conditionedDeletionMass_nonneg hκ D.val)]

theorem pmf_map_equiv_apply {A B : Type*} (p : PMF A) (e : A ≃ B) (b : B) :
    (p.map e) b = p (e.symm b) := by
  classical
  rw [PMF.map_apply]
  calc
    (∑' a, if b = e a then p a else 0) =
        ∑' a, if e.symm b = a then p a else 0 := by
      apply tsum_congr
      intro a
      have h : b = e a ↔ e.symm b = a := by
        constructor
        · intro h
          rw [h, e.symm_apply_apply]
        · intro h
          rw [← h, e.apply_symm_apply]
      simp only [h]
    _ = p (e.symm b) := by simp

end Balanced.DeletionLaw

namespace Balanced
open scoped _root_.Balanced

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

def validArrayDeletionEquiv :
    DeletionLaw.ValidArray (Fintype.card F) (Fintype.card F + 1) ≃ DeletionSet F 3 :=
  DeletionCoordinates.affineCoordinateLineEquiv F 3

def returnedDeletionLaw
    {κ : DeletionLaw.Weight (Fintype.card F) (Fintype.card F + 1)}
    (hκ : DeletionLaw.IsSubprobabilityKernel κ)
    (hdistinct : DeletionLaw.DistinctOutput κ)
    (hsuccess : 0 < DeletionLaw.successMass κ) : PMF (DeletionSet F 3) :=
  (DeletionLaw.returnedArrayLaw hκ hdistinct hsuccess).map (validArrayDeletionEquiv F)

theorem returnedDeletionLaw_apply_toReal
    {κ : DeletionLaw.Weight (Fintype.card F) (Fintype.card F + 1)}
    (hκ : DeletionLaw.IsSubprobabilityKernel κ)
    (hdistinct : DeletionLaw.DistinctOutput κ)
    (hsuccess : 0 < DeletionLaw.successMass κ) (D : DeletionSet F 3) :
    (returnedDeletionLaw F hκ hdistinct hsuccess D).toReal =
      DeletionLaw.conditionedDeletionMass κ ((validArrayDeletionEquiv F).symm D).val := by
  rw [returnedDeletionLaw, DeletionLaw.pmf_map_equiv_apply,
    DeletionLaw.returnedArrayLaw_apply_toReal]

theorem geometric_uniformDeletionMass_eq (k : ℕ) :
    uniformDeletionMass (F := F) k =
      ((Nat.choose (Fintype.card F) k : ℝ) ^ (Fintype.card F + 1))⁻¹ := by
  unfold uniformDeletionMass
  have hc : Fintype.card (DeletionSet F k) =
      (Nat.choose (Fintype.card F) k) ^ (Fintype.card F + 1) := by
    calc
      Fintype.card (DeletionSet F k) =
          Fintype.card {S : Finset (Line F) // ∀ d : Direction F,
            (S.filter (fun l => l.1 = d)).card = k} :=
        Fintype.card_congr (Equiv.refl _)
      _ = _ := DeletionCoordinates.card_affineDeletionSets F k
  rw [hc, Nat.cast_pow, one_div]

end Balanced

end

end OAI
