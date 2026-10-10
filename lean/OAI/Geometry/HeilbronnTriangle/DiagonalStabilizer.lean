import Mathlib

namespace OAI


noncomputable section

namespace Problem355.DiagonalStabilizer

open Matrix

variable {R : Type*} [CommRing R]

def diagonal3 (D E : R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.diagonal ![1, D, E]

abbrev Ann (a : R) := {x : R // x * a = 0}

abbrev FixingMatrices (D E : R) :=
  {A : Matrix (Fin 3) (Fin 3) R // A * diagonal3 D E = diagonal3 D E}

lemma fixing_entry {D E : R} (A : FixingMatrices D E) (i j : Fin 3) :
    A.val i j * ![1, D, E] j = if i = j then ![1, D, E] j else 0 := by
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M i j) A.property
  by_cases hij : i = j
  · simpa [diagonal3, Matrix.mul_diagonal, Matrix.diagonal_apply, hij] using h
  · simpa [diagonal3, Matrix.mul_diagonal, Matrix.diagonal_apply, hij] using h

lemma fixing_first_column {D E : R} (A : FixingMatrices D E) (i : Fin 3) :
    A.val i 0 = if i = 0 then 1 else 0 := by
  simpa using fixing_entry A i 0

lemma fixing_other_column {D E : R} (A : FixingMatrices D E) (i j : Fin 3) :
    (A.val i j - if i = j then 1 else 0) * ![1, D, E] j = 0 := by
  have h := fixing_entry A i j
  by_cases hij : i = j
  · simpa [hij, sub_mul] using sub_eq_zero.mpr h
  · simpa [hij] using h

def encode {D E : R} (A : FixingMatrices D E) :
    (Fin 3 → Ann D) × (Fin 3 → Ann E) :=
  (fun i => ⟨A.val i 1 - if i = 1 then 1 else 0,
      by simpa using fixing_other_column A i 1⟩,
   fun i => ⟨A.val i 2 - if i = 2 then 1 else 0,
      by simpa using fixing_other_column A i 2⟩)

lemma encode_injective {D E : R} : Function.Injective (encode (D := D) (E := E)) := by
  intro A A' h
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases j
  · change A.val i 0 = A'.val i 0
    exact (fixing_first_column A i).trans (fixing_first_column A' i).symm
  · change A.val i 1 = A'.val i 1
    have hv := congrArg (fun z => ((Prod.fst z) i).val) h
    simpa only [encode, sub_left_inj] using hv
  · change A.val i 2 = A'.val i 2
    have hv := congrArg (fun z => ((Prod.snd z) i).val) h
    simpa only [encode, sub_left_inj] using hv

theorem card_fixingMatrices_le [Finite R] (D E : R) :
    Nat.card (FixingMatrices D E) ≤ Nat.card (Ann D) ^ 3 * Nat.card (Ann E) ^ 3 := by
  simpa only [Nat.card_prod, Nat.card_fun, Nat.card_fin] using
    Nat.card_le_card_of_injective (encode (D := D) (E := E)) encode_injective

abbrev FixingUnits (C : Matrix (Fin 3) (Fin 3) R) :=
  {A : Matrix.GeneralLinearGroup (Fin 3) R // (A.val : Matrix (Fin 3) (Fin 3) R) * C = C}

def forgetUnits {D E : R} (A : FixingUnits (diagonal3 D E)) : FixingMatrices D E :=
  ⟨A.val.val, A.property⟩

lemma forgetUnits_injective {D E : R} :
    Function.Injective (forgetUnits (D := D) (E := E)) := by
  intro A A' h
  apply Subtype.ext
  apply Units.ext
  exact congrArg Subtype.val h

theorem card_fixingUnits_diagonal_le [Finite R] (D E : R) :
    Nat.card (FixingUnits (diagonal3 D E)) ≤
      Nat.card (Ann D) ^ 3 * Nat.card (Ann E) ^ 3 := by
  exact (Nat.card_le_card_of_injective forgetUnits forgetUnits_injective).trans
    (card_fixingMatrices_le D E)

def conjugateFixing {C D : Matrix (Fin 3) (Fin 3) R}
    (P Q : Matrix.GeneralLinearGroup (Fin 3) R)
    (hC : C = (P : Matrix (Fin 3) (Fin 3) R) * D * (Q : Matrix (Fin 3) (Fin 3) R))
    (A : FixingUnits C) : FixingUnits D := by
  refine ⟨P⁻¹ * A.val * P, ?_⟩
  have h := A.property
  simp only [hC] at h
  have h' : (A.val.val * P.val * D) * Q.val = (P.val * D) * Q.val := by
    simpa only [Matrix.mul_assoc] using h
  have h'' : A.val.val * P.val * D = P.val * D := Q.isUnit.mul_right_cancel h'
  apply P.isUnit.mul_left_cancel
  simpa only [Units.val_mul, ← Matrix.mul_assoc, Units.mul_inv, one_mul] using h''

lemma conjugateFixing_injective {C D : Matrix (Fin 3) (Fin 3) R}
    (P Q : Matrix.GeneralLinearGroup (Fin 3) R)
    (hC : C = (P : Matrix (Fin 3) (Fin 3) R) * D * (Q : Matrix (Fin 3) (Fin 3) R)) :
    Function.Injective (conjugateFixing P Q hC) := by
  intro A A' h
  apply Subtype.ext
  have h' := congrArg Subtype.val h
  change P⁻¹ * A.val * P = P⁻¹ * A'.val * P at h'
  exact mul_left_cancel (mul_right_cancel h')

theorem card_fixingUnits_of_diagonal_form_le [Finite R]
    (C : Matrix (Fin 3) (Fin 3) R) (D E : R)
    (P Q : Matrix.GeneralLinearGroup (Fin 3) R)
    (hC : C = (P : Matrix (Fin 3) (Fin 3) R) * diagonal3 D E *
      (Q : Matrix (Fin 3) (Fin 3) R)) :
    Nat.card (FixingUnits C) ≤ Nat.card (Ann D) ^ 3 * Nat.card (Ann E) ^ 3 := by
  exact (Nat.card_le_card_of_injective (conjugateFixing P Q hC)
    (conjugateFixing_injective P Q hC)).trans (card_fixingUnits_diagonal_le D E)

theorem card_stabilizer_of_diagonal_form_le [Finite R]
    (C : Matrix (Fin 3) (Fin 3) R) (D E : R)
    (P Q : Matrix.GeneralLinearGroup (Fin 3) R)
    (hC : C = (P : Matrix (Fin 3) (Fin 3) R) * diagonal3 D E *
      (Q : Matrix (Fin 3) (Fin 3) R)) :
    Nat.card (MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 3) R) C) ≤
      Nat.card (Ann D) ^ 3 * Nat.card (Ann E) ^ 3 := by
  change Nat.card (FixingUnits C) ≤ _
  exact card_fixingUnits_of_diagonal_form_le C D E P Q hC

end Problem355.DiagonalStabilizer

end

end OAI
