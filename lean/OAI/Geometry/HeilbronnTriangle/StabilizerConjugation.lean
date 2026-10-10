import OAI.Geometry.HeilbronnTriangle.ZModAnnihilator

namespace OAI


namespace Problem355

def unitLeftStabilizerEquiv {M : Type*} [Monoid M] (P Q : Mˣ) (D : M) :
    {A : Mˣ // (A : M) * D = D} ≃
      {A : Mˣ // (A : M) * ((P : M) * D * (Q : M)) =
        (P : M) * D * (Q : M)} :=
  (MulAut.conj P).toEquiv.subtypeEquiv fun A => by
    change (A : M) * D = D ↔
      ((P : M) * (A : M) * ((P⁻¹ : Mˣ) : M)) *
        ((P : M) * D * (Q : M)) = (P : M) * D * (Q : M)
    constructor
    · intro h
      simpa only [mul_assoc, Units.inv_mul_cancel_left] using
        congrArg (fun x : M => (P : M) * x * (Q : M)) h
    · intro h
      have hh := congrArg (fun x : M => ((P⁻¹ : Mˣ) : M) * x * ((Q⁻¹ : Mˣ) : M)) h
      simpa only [mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, one_mul, mul_one] using hh

theorem card_unit_left_stabilizer_eq {M : Type*} [Monoid M]
    (P Q : Mˣ) (D : M) :
    Nat.card {A : Mˣ // (A : M) * ((P : M) * D * (Q : M)) =
      (P : M) * D * (Q : M)} =
      Nat.card {A : Mˣ // (A : M) * D = D} :=
  (Nat.card_congr (unitLeftStabilizerEquiv P Q D)).symm

theorem unitLeftStabilizerEquiv_map {M G : Type*} [Monoid M] [CommGroup G]
    (P Q : Mˣ) (D : M) (φ : Mˣ →* G)
    (A : {A : Mˣ // (A : M) * D = D}) :
    φ (unitLeftStabilizerEquiv P Q D A).1 = φ A.1 := by
  change φ (P * A.1 * P⁻¹) = φ A.1
  simp [mul_assoc]

theorem range_unit_left_stabilizer_eq {M G : Type*} [Monoid M] [CommGroup G]
    (P Q : Mˣ) (D : M) (φ : Mˣ →* G) :
    Set.range (fun A : {A : Mˣ // (A : M) * ((P : M) * D * (Q : M)) =
      (P : M) * D * (Q : M)} => φ A.1) =
      Set.range (fun A : {A : Mˣ // (A : M) * D = D} => φ A.1) := by
  ext y
  constructor
  · rintro ⟨A, hA⟩
    obtain ⟨B, rfl⟩ := (unitLeftStabilizerEquiv P Q D).surjective A
    exact ⟨B, (unitLeftStabilizerEquiv_map P Q D φ B).symm.trans hA⟩
  · rintro ⟨A, hA⟩
    exact ⟨unitLeftStabilizerEquiv P Q D A,
      (unitLeftStabilizerEquiv_map P Q D φ A).trans hA⟩

theorem card_unit_matrix_stabilizer_le_of_diagonalization
    (m D E : ℕ) [NeZero m] (hD : D ∣ m) (hE : E ∣ m)
    (C : Matrix (Fin 3) (Fin 3) (ZMod m))
    (P Q : (Matrix (Fin 3) (Fin 3) (ZMod m))ˣ)
    (hC : C = (P : Matrix _ _ _) *
      Matrix.diagonal ![1, (D : ZMod m), (E : ZMod m)] * (Q : Matrix _ _ _)) :
    Nat.card {A : (Matrix (Fin 3) (Fin 3) (ZMod m))ˣ //
      (A : Matrix (Fin 3) (Fin 3) (ZMod m)) * C = C} ≤ D ^ 3 * E ^ 3 := by
  subst C
  rw [card_unit_left_stabilizer_eq]
  exact card_unit_matrix_fixed_diagonal_three_le m D E hD hE

end Problem355

end OAI
