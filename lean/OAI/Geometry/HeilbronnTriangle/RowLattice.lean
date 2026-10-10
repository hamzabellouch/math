import OAI.Geometry.HeilbronnTriangle.DiagonalStabilizer
import OAI.Geometry.HeilbronnTriangle.ZModAnnihilator

namespace OAI


noncomputable section

namespace Problem355.RowLattice

open Matrix DiagonalStabilizer

variable {R : Type*} [CommRing R]

abbrev RowKernel (C : Matrix (Fin 3) (Fin 3) R) :=
  {v : Fin 3 → R // v ᵥ* C = 0}

def rowImage (C : Matrix (Fin 3) (Fin 3) R) : AddSubgroup (Fin 3 → R) :=
  C.vecMulLinear.toAddMonoidHom.range

lemma rowImage_index_eq_card_kernel [Finite R] (C : Matrix (Fin 3) (Fin 3) R) :
    (rowImage C).index = Nat.card (RowKernel C) := by
  exact AddSubgroup.index_range

def diagonalKernelEquiv (D E : R) :
    RowKernel (diagonal3 D E) ≃ Ann D × Ann E where
  toFun v :=
    (⟨v.val 1, by
      have h := congrFun v.property 1
      simpa [diagonal3, Matrix.vecMul_diagonal] using h⟩,
     ⟨v.val 2, by
      have h := congrFun v.property 2
      simpa [diagonal3, Matrix.vecMul_diagonal] using h⟩)
  invFun v := ⟨![0, v.1.val, v.2.val], by
    funext i
    fin_cases i
    · simp [diagonal3, Matrix.vecMul_diagonal]
    · simpa [diagonal3, Matrix.vecMul_diagonal] using v.1.property
    · simpa [diagonal3, Matrix.vecMul_diagonal] using v.2.property⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    fin_cases i
    · have h := congrFun v.property 0
      simpa [diagonal3, Matrix.vecMul_diagonal] using h.symm
    · rfl
    · rfl
  right_inv v := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

lemma card_diagonal_kernel (D E : R) :
    Nat.card (RowKernel (diagonal3 D E)) = Nat.card (Ann D) * Nat.card (Ann E) := by
  rw [Nat.card_congr (diagonalKernelEquiv D E), Nat.card_prod]

def kernelEquivOfDiagonalForm {C D : Matrix (Fin 3) (Fin 3) R}
    (P Q : Matrix.GeneralLinearGroup (Fin 3) R)
    (hC : C = (P : Matrix (Fin 3) (Fin 3) R) * D *
      (Q : Matrix (Fin 3) (Fin 3) R)) : RowKernel C ≃ RowKernel D where
  toFun v := ⟨v.val ᵥ* P.val, by
    apply Matrix.vecMul_injective_of_isUnit Q.isUnit
    simpa only [Matrix.vecMul_vecMul, hC, Matrix.zero_vecMul] using v.property⟩
  invFun v := ⟨v.val ᵥ* (P⁻¹).val, by
    calc
      (v.val ᵥ* (P⁻¹).val) ᵥ* C =
          (((v.val ᵥ* (P⁻¹).val) ᵥ* P.val) ᵥ* D) ᵥ* Q.val := by
        simp only [Matrix.vecMul_vecMul, hC, Matrix.mul_assoc]
      _ = 0 := by
        have hp : (v.val ᵥ* (P⁻¹).val) ᵥ* P.val = v.val := by
          rw [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]
        rw [hp, v.property, Matrix.zero_vecMul]⟩
  left_inv v := by
    apply Subtype.ext
    simp only [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
  right_inv v := by
    apply Subtype.ext
    simp only [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]

lemma rowImage_index_of_diagonal_form [Finite R]
    (C : Matrix (Fin 3) (Fin 3) R) (D E : R)
    (P Q : Matrix.GeneralLinearGroup (Fin 3) R)
    (hC : C = (P : Matrix (Fin 3) (Fin 3) R) * diagonal3 D E *
      (Q : Matrix (Fin 3) (Fin 3) R)) :
    (rowImage C).index = Nat.card (Ann D) * Nat.card (Ann E) := by
  rw [rowImage_index_eq_card_kernel,
    Nat.card_congr (kernelEquivOfDiagonalForm P Q hC), card_diagonal_kernel]

def reduction (h : ℕ) : (Fin 3 → ℤ) →+ (Fin 3 → ZMod h) where
  toFun v i := (v i : ZMod h)
  map_zero' := by ext i; simp
  map_add' v w := by ext i; simp

lemma reduction_surjective (h : ℕ) : Function.Surjective (reduction h) := by
  intro v
  choose w hw using fun i : Fin 3 => ZMod.intCast_surjective (v i)
  exact ⟨w, funext hw⟩

def integerRowLattice (h : ℕ) (C : Matrix (Fin 3) (Fin 3) (ZMod h)) :
    AddSubgroup (Fin 3 → ℤ) :=
  (rowImage C).comap (reduction h)

lemma integerRowLattice_index (h : ℕ) (C : Matrix (Fin 3) (Fin 3) (ZMod h)) :
    (integerRowLattice h C).index = (rowImage C).index := by
  exact AddSubgroup.index_comap_of_surjective _ (reduction_surjective h)

theorem integerRowLattice_index_prime_power
    (B k b e : ℕ) [NeZero B] (hb : b ≤ k) (he : e ≤ k)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) *
      diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
      (Q : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))) :
    (integerRowLattice (B ^ k) C).index = B ^ b * B ^ e := by
  have hD : Nat.card (Ann (R := ZMod (B ^ k)) (B ^ b)) = B ^ b := by
    simpa only [Ann, mul_comm] using zmod_card_pow_mul_eq_zero B k b hb
  have hE : Nat.card (Ann (R := ZMod (B ^ k)) (B ^ e)) = B ^ e := by
    simpa only [Ann, mul_comm] using zmod_card_pow_mul_eq_zero B k e he
  rw [integerRowLattice_index, rowImage_index_of_diagonal_form C _ _ P Q hC, hD, hE]

lemma smul_mem_rowImage_diagonal (D E : R) (hDE : D ∣ E) (v : Fin 3 → R) :
    E • v ∈ rowImage (diagonal3 D E) := by
  obtain ⟨a, ha⟩ := hDE
  refine ⟨![E * v 0, a * v 1, v 2], ?_⟩
  change ![E * v 0, a * v 1, v 2] ᵥ* diagonal3 D E = E • v
  funext i
  fin_cases i <;> simp [diagonal3, Matrix.vecMul_diagonal, ha] <;> ring

lemma smul_mem_rowImage_of_diagonal_form
    (C : Matrix (Fin 3) (Fin 3) R) (D E : R) (hDE : D ∣ E)
    (P Q : Matrix.GeneralLinearGroup (Fin 3) R)
    (hC : C = (P : Matrix (Fin 3) (Fin 3) R) * diagonal3 D E *
      (Q : Matrix (Fin 3) (Fin 3) R)) (v : Fin 3 → R) :
    E • v ∈ rowImage C := by
  obtain ⟨w, hw⟩ := smul_mem_rowImage_diagonal D E hDE (v ᵥ* (Q⁻¹).val)
  change w ᵥ* diagonal3 D E = E • (v ᵥ* (Q⁻¹).val) at hw
  refine ⟨w ᵥ* (P⁻¹).val, ?_⟩
  change (w ᵥ* (P⁻¹).val) ᵥ* C = E • v
  calc
    (w ᵥ* (P⁻¹).val) ᵥ* C = (w ᵥ* diagonal3 D E) ᵥ* Q.val := by
      simp only [hC, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, Units.inv_mul, one_mul]
    _ = (E • (v ᵥ* (Q⁻¹).val)) ᵥ* Q.val := by rw [hw]
    _ = E • v := by
      rw [Matrix.smul_vecMul, Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]

lemma rowImage_eq_rowSpan (C : Matrix (Fin 3) (Fin 3) R) :
    rowImage C = (Submodule.span R (Set.range C.row)).toAddSubgroup := by
  exact congrArg Submodule.toAddSubgroup (range_vecMulLinear C)

theorem nsmul_mem_integerRowLattice_prime_power
    (B k b e : ℕ) (hbe : b ≤ e)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) *
      diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
      (Q : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))) (v : Fin 3 → ℤ) :
    (B ^ e) • v ∈ integerRowLattice (B ^ k) C := by
  change reduction (B ^ k) ((B ^ e) • v) ∈ rowImage C
  have hv := smul_mem_rowImage_of_diagonal_form C
    (B ^ b : ZMod (B ^ k)) (B ^ e : ZMod (B ^ k))
    (pow_dvd_pow (B : ZMod (B ^ k)) hbe) P Q hC (reduction (B ^ k) v)
  have hcast : reduction (B ^ k) ((B ^ e) • v) =
      (B ^ e : ZMod (B ^ k)) • reduction (B ^ k) v := by
    ext i
    simp [reduction, nsmul_eq_mul]
  rw [hcast]
  exact hv

instance integerRowLattice_finiteIndex (h : ℕ) [NeZero h]
    (C : Matrix (Fin 3) (Fin 3) (ZMod h)) : (integerRowLattice h C).FiniteIndex where
  index_ne_zero := by
    rw [integerRowLattice_index]
    exact AddSubgroup.FiniteIndex.index_ne_zero

theorem integerRowLattice_finrank (h : ℕ) [NeZero h]
    (C : Matrix (Fin 3) (Fin 3) (ZMod h)) :
    Module.finrank ℤ (integerRowLattice h C) = 3 := by
  simpa using AddSubgroup.finrank_eq_of_finiteIndex (integerRowLattice h C)

lemma rowImage_left_unit (C : Matrix (Fin 3) (Fin 3) R)
    (P : Matrix.GeneralLinearGroup (Fin 3) R) :
    rowImage ((P : Matrix (Fin 3) (Fin 3) R) * C) = rowImage C := by
  ext v
  constructor
  · rintro ⟨w, hw⟩
    change w ᵥ* (P.val * C) = v at hw
    refine ⟨w ᵥ* P.val, ?_⟩
    change (w ᵥ* P.val) ᵥ* C = v
    simpa only [Matrix.vecMul_vecMul] using hw
  · rintro ⟨w, hw⟩
    change w ᵥ* C = v at hw
    refine ⟨w ᵥ* (P⁻¹).val, ?_⟩
    change (w ᵥ* (P⁻¹).val) ᵥ* (P.val * C) = v
    simpa only [Matrix.vecMul_vecMul, ← Matrix.mul_assoc, Units.inv_mul, one_mul] using hw

lemma row_mem_integerRowLattice_of_reduction_eq (h : ℕ)
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (C G : Matrix (Fin 3) (Fin 3) (ZMod h))
    (hA : A.map (Int.castRingHom (ZMod h)) = G * C) (i : Fin 3) :
    A.row i ∈ integerRowLattice h C := by
  change reduction h (A.row i) ∈ rowImage C
  refine ⟨G.row i, ?_⟩
  have hrow := congrArg (fun M : Matrix (Fin 3) (Fin 3) (ZMod h) => M.row i) hA
  exact hrow.symm

end Problem355.RowLattice

end

end OAI
