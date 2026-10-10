import OAI.Geometry.HeilbronnTriangle.ZModAnnihilator

namespace OAI


noncomputable section

namespace Problem355.DiagonalDetImage

open Matrix

variable {R : Type*} [CommRing R]

def diagonalThree (D E : R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.diagonal ![1, D, E]

def finalDiagonalUnit (u : Rˣ) : Matrix.GeneralLinearGroup (Fin 3) R :=
  Matrix.GeneralLinearGroup.mk'' (Matrix.diagonal ![1, 1, (u : R)]) (by
    simp [Matrix.det_diagonal, Fin.prod_univ_succ])

@[simp] theorem finalDiagonalUnit_val (u : Rˣ) :
    (finalDiagonalUnit u : Matrix (Fin 3) (Fin 3) R) =
      Matrix.diagonal ![1, 1, (u : R)] := by
  simp [finalDiagonalUnit]

@[simp] theorem finalDiagonalUnit_det (u : Rˣ) :
    Matrix.GeneralLinearGroup.det (finalDiagonalUnit u) = u := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.det, Matrix.det_diagonal, Fin.prod_univ_succ]

theorem finalDiagonalUnit_fixes (D E : R) (u : Rˣ)
    (hu : ((u : R) - 1) * E = 0) :
    (finalDiagonalUnit u : Matrix (Fin 3) (Fin 3) R) * diagonalThree D E =
      diagonalThree D E := by
  have huE : (u : R) * E = E := by
    simpa [sub_mul, sub_eq_zero] using hu
  rw [finalDiagonalUnit_val, diagonalThree, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [huE]

def determinantValues (D E : R) : Set Rˣ :=
  {u | ∃ g : Matrix.GeneralLinearGroup (Fin 3) R,
    (g : Matrix (Fin 3) (Fin 3) R) * diagonalThree D E = diagonalThree D E ∧
      Matrix.GeneralLinearGroup.det g = u}

theorem mem_determinantValues (D E : R) (u : Rˣ)
    (hu : ((u : R) - 1) * E = 0) : u ∈ determinantValues D E :=
  ⟨finalDiagonalUnit u, finalDiagonalUnit_fixes D E u hu, finalDiagonalUnit_det u⟩

theorem card_determinantValues_lower [Fintype R] (D E : R) :
    Nat.card {u : Rˣ // ((u : R) - 1) * E = 0} ≤
      Nat.card (determinantValues D E) := by
  classical
  apply Nat.card_le_card_of_injective
    (fun u => (⟨u.val, mem_determinantValues D E u.val u.property⟩ : determinantValues D E))
  intro u v h
  apply Subtype.ext
  exact congrArg (fun w : determinantValues D E => w.val) h

def annihilatorEquivCongruenceUnits (E : R)
    (hunit : ∀ x : R, x * E = 0 → IsUnit (1 + x)) :
    {x : R // x * E = 0} ≃ {u : Rˣ // ((u : R) - 1) * E = 0} where
  toFun x := ⟨(hunit x.val x.property).unit, by
    rw [IsUnit.unit_spec]
    simpa using x.property⟩
  invFun u := ⟨(u.val : R) - 1, u.property⟩
  left_inv x := by
    apply Subtype.ext
    simp only [IsUnit.unit_spec, add_sub_cancel_left]
  right_inv u := by
    apply Subtype.ext
    apply Units.ext
    simp only [IsUnit.unit_spec]
    ring

theorem isUnit_one_add_of_annihilates_prime_power
    {p k e : ℕ} (hp : p.Prime) (he : e < k)
    (x : ZMod (p ^ k)) (hx : x * (p ^ e : ℕ) = 0) :
    IsUnit (1 + x) := by
  have hp0 : 0 < p := hp.pos
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le e) he
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcast : ((x.val * p ^ e : ℕ) : ZMod (p ^ k)) = 0 := by
    simpa only [Nat.cast_mul, ZMod.natCast_zmod_val] using hx
  have hd : p ^ k ∣ x.val * p ^ e :=
    (ZMod.natCast_eq_zero_iff _ _).mp hcast
  have hd' : p ^ (k - e) ∣ x.val := by
    apply Nat.dvd_of_mul_dvd_mul_right (pow_pos hp0 e)
    simpa only [← pow_add, Nat.sub_add_cancel he.le] using hd
  have hpval : p ∣ x.val :=
    (dvd_pow_self p (by omega : k - e ≠ 0)).trans hd'
  have hpnot : ¬ p ∣ 1 + x.val := by
    intro h
    have hpone : p ∣ 1 := (Nat.dvd_add_iff_left hpval).mpr h
    exact hp.not_dvd_one hpone
  have hu : IsUnit ((1 + x.val : ℕ) : ZMod (p ^ k)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp hk).mpr hpnot
  simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] using hu

theorem card_congruenceUnits_eq_annihilator
    {p k e : ℕ} (hp : p.Prime) (he : e < k) :
    Nat.card {u : (ZMod (p ^ k))ˣ //
      ((u : ZMod (p ^ k)) - 1) * (p ^ e : ℕ) = 0} =
    Nat.card {x : ZMod (p ^ k) // x * (p ^ e : ℕ) = 0} := by
  exact (Nat.card_congr (annihilatorEquivCongruenceUnits ((p ^ e : ℕ) : ZMod (p ^ k))
    (isUnit_one_add_of_annihilates_prime_power hp he))).symm

theorem card_congruenceUnits_prime_power
    {p k e : ℕ} (hp : p.Prime) (he : e < k) :
    Nat.card {u : (ZMod (p ^ k))ˣ //
      ((u : ZMod (p ^ k)) - 1) * (p ^ e : ℕ) = 0} = p ^ e := by
  let : NeZero p := ⟨hp.ne_zero⟩
  rw [card_congruenceUnits_eq_annihilator hp he]
  simpa only [Nat.cast_pow, mul_comm] using
    Problem355.zmod_card_pow_mul_eq_zero p k e he.le

theorem determinantValues_zero (D : R) :
    determinantValues D 0 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro u
  exact mem_determinantValues D 0 u (by simp)

theorem card_determinantValues_prime_power_zero
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (D : ZMod (p ^ k)) :
    Nat.card (determinantValues D ((p ^ k : ℕ) : ZMod (p ^ k))) =
      p ^ (k - 1) * (p - 1) := by
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  simp only [ZMod.natCast_self, determinantValues_zero]
  rw [Nat.card_congr (Equiv.Set.univ _)]
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow hp hk]

theorem card_determinantValues_prime_power_lower
    {p k e : ℕ} (hp : p.Prime) (he : e < k) (D : ZMod (p ^ k)) :
    p ^ e ≤ Nat.card (determinantValues D ((p ^ e : ℕ) : ZMod (p ^ k))) := by
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  simpa only [card_congruenceUnits_prime_power hp he] using
    card_determinantValues_lower D ((p ^ e : ℕ) : ZMod (p ^ k))

theorem card_determinantValues_ratio
    {p k e : ℕ} (hp : p.Prime) (he : e ≤ k) (D : ZMod (p ^ k)) :
    p ^ e * Nat.card (ZMod (p ^ k))ˣ ≤
      p ^ k * Nat.card (determinantValues D ((p ^ e : ℕ) : ZMod (p ^ k))) := by
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rcases he.eq_or_lt with rfl | he
  · simp only [ZMod.natCast_self, determinantValues_zero]
    rw [Nat.card_congr (Equiv.Set.univ _)]
  · have h1 := card_determinantValues_prime_power_lower hp he D
    have h2 : Nat.card (ZMod (p ^ k))ˣ ≤ p ^ k := by
      simpa only [Nat.card_zmod] using
        Nat.card_le_card_of_injective
          (fun u : (ZMod (p ^ k))ˣ => (u : ZMod (p ^ k))) Units.val_injective
    exact (Nat.mul_le_mul_left (p ^ e) h2).trans
      (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (p ^ k) h1)

theorem determinantValues_eq_stabilizer_map (D E : R) :
    determinantValues D E =
      ((MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 3) R)
        (diagonalThree D E)).map Matrix.GeneralLinearGroup.det : Set Rˣ) := by
  ext u
  simp only [determinantValues, Set.mem_ofPred_eq, SetLike.mem_coe,
    Subgroup.mem_map, MulAction.mem_stabilizer_iff]
  rfl

theorem determinant_mem_of_diagonal_form
    (D E : R) (P Q : Matrix.GeneralLinearGroup (Fin 3) R)
    (C : Matrix (Fin 3) (Fin 3) R)
    (hC : C = (P : Matrix (Fin 3) (Fin 3) R) * diagonalThree D E *
      (Q : Matrix (Fin 3) (Fin 3) R))
    (u : Rˣ) (hu : u ∈ determinantValues D E) :
    u ∈ (MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 3) R) C).map
      Matrix.GeneralLinearGroup.det := by
  rcases hu with ⟨g, hg, hdet⟩
  apply Subgroup.mem_map.mpr
  refine ⟨P * g * P⁻¹, ?_, ?_⟩
  · apply MulAction.mem_stabilizer_iff.mpr
    change (↑(P * g * P⁻¹) : Matrix (Fin 3) (Fin 3) R) * C = C
    rw [hC]
    simp only [Units.val_mul]
    calc
      ((P : Matrix (Fin 3) (Fin 3) R) * ↑g * ↑(P⁻¹)) *
          (↑P * diagonalThree D E * ↑Q) =
          (P : Matrix (Fin 3) (Fin 3) R) *
            (↑g * diagonalThree D E) * ↑Q := by
        have hc : (↑(P⁻¹) : Matrix (Fin 3) (Fin 3) R) *
            ((↑P : Matrix (Fin 3) (Fin 3) R) * (diagonalThree D E * (Q : Matrix (Fin 3) (Fin 3) R))) =
            diagonalThree D E * (Q : Matrix (Fin 3) (Fin 3) R) := by
          rw [← Matrix.mul_assoc, P.inv_mul, Matrix.one_mul]
        simpa only [Matrix.mul_assoc] using
          congrArg (fun M : Matrix (Fin 3) (Fin 3) R =>
            (P : Matrix (Fin 3) (Fin 3) R) * ((g : Matrix (Fin 3) (Fin 3) R) * M)) hc
      _ = _ := by rw [hg]
  · simp only [map_mul, map_inv]
    rw [mul_right_comm, mul_inv_cancel, one_mul, hdet]

theorem card_stabilizer_det_image_ratio_of_diagonal_form
    {p k e : ℕ} (hp : p.Prime) (he : e ≤ k)
    (D : ZMod (p ^ k))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k)))
    (C : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k)))
    (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k))) *
      diagonalThree D ((p ^ e : ℕ) : ZMod (p ^ k)) *
      (Q : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k)))) :
    p ^ e * Nat.card (ZMod (p ^ k))ˣ ≤
      p ^ k * Nat.card
        ((MulAction.stabilizer
          (Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k))) C).map
            Matrix.GeneralLinearGroup.det) := by
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  apply (card_determinantValues_ratio hp he D).trans
  apply Nat.mul_le_mul_left
  apply Nat.card_le_card_of_injective
    (fun u : determinantValues D ((p ^ e : ℕ) : ZMod (p ^ k)) =>
      (⟨u.val, determinant_mem_of_diagonal_form D _ P Q C hC u.val u.property⟩ :
        (MulAction.stabilizer
          (Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k))) C).map
            Matrix.GeneralLinearGroup.det))
  intro u v h
  apply Subtype.ext
  exact congrArg (fun w :
    ((MulAction.stabilizer
      (Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k))) C).map
        Matrix.GeneralLinearGroup.det) => w.val) h

end Problem355.DiagonalDetImage

end

end OAI
