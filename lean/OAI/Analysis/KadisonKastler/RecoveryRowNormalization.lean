import OAI.Analysis.KadisonKastler.RecoveryRows
import OAI.Analysis.KadisonKastler.RandomizedRows
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

namespace OAI

/-! # Exact normalization of the phase-randomized recovery rows -/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

variable {B : Type*} [CStarAlgebra B] {q N : ℕ} [NeZero q]

/-- The scalar root-of-unity phase, as a unitary in any unital complex
C-star algebra. -/
def scalarPhaseUnitary (B : Type*) [CStarAlgebra B] (z : ZMod q) : unitary B :=
  ⟨ZMod.stdAddChar z • (1 : B), by
    have hz : star (ZMod.stdAddChar z) * ZMod.stdAddChar z = (1 : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul', AddChar.norm_apply]
      norm_num
    have hz' : ZMod.stdAddChar z * star (ZMod.stdAddChar z) = (1 : ℂ) := by
      rw [mul_comm, hz]
    constructor
    · simp only [star_smul, star_one, smul_mul_assoc, mul_smul_comm,
        one_mul, smul_smul, hz', one_smul]
    · simp only [star_smul, star_one, smul_mul_assoc, mul_smul_comm,
        one_mul, smul_smul, hz, one_smul]⟩

@[simp]
theorem scalarPhaseUnitary_coe (z : ZMod q) :
    (scalarPhaseUnitary B z : B) = ZMod.stdAddChar z • (1 : B) := rfl

theorem scalarPhaseUnitary_mem (S : StarSubalgebra ℂ B) (z : ZMod q) :
    (scalarPhaseUnitary B z : B) ∈ S :=
  S.smul_mem S.one_mem _

/-- Scalar multiplication of a unitary by the chosen finite phase. -/
def scalarPhaseTwist (z : ZMod q) (u : unitary B) : unitary B :=
  scalarPhaseUnitary B z * u

@[simp]
theorem scalarPhaseTwist_coe (z : ZMod q) (u : unitary B) :
    (scalarPhaseTwist z u : B) = ZMod.stdAddChar z • (u : B) := by
  change (ZMod.stdAddChar z • (1 : B)) * (u : B) = _
  rw [smul_mul_assoc, one_mul]

/-- The characters attached to the first positive powers. -/
def scalarPowerCharacter (q N : ℕ) [NeZero q] (r : Fin N) : AddChar (ZMod q) ℂ :=
  ZMod.stdAddChar ^ (r.val + 1)

@[simp]
theorem scalarPowerCharacter_apply (r : Fin N) (z : ZMod q) :
    scalarPowerCharacter q N r z = ZMod.stdAddChar z ^ (r.val + 1) := rfl

theorem scalarPowerCharacter_injective (hNq : N < q) :
    Function.Injective (scalarPowerCharacter q N) := by
  intro r s hrs
  have he := congrArg (fun χ : AddChar (ZMod q) ℂ => χ 1) hrs
  simp only [scalarPowerCharacter_apply, ← AddChar.map_nsmul_eq_pow,
    nsmul_eq_mul, mul_one] at he
  have hz := ZMod.injective_stdAddChar he
  have hr : r.val + 1 < q := lt_of_le_of_lt (Nat.succ_le_of_lt r.isLt) hNq
  have hs : s.val + 1 < q := lt_of_le_of_lt (Nat.succ_le_of_lt s.isLt) hNq
  have hv := congrArg ZMod.val hz
  rw [ZMod.val_natCast_of_lt hr, ZMod.val_natCast_of_lt hs] at hv
  apply Fin.ext
  omega

theorem scalarPowerCharacter_orthogonal (hNq : N < q) (r s : Fin N) :
    (𝔼 z : ZMod q, star (scalarPowerCharacter q N r z) * scalarPowerCharacter q N s z) =
      if r = s then 1 else 0 :=
  additiveCharacters_orthogonal _ (scalarPowerCharacter_injective hNq) r s

theorem inverseScalarPowerCharacter_orthogonal (hNq : N < q) (r s : Fin N) :
    (𝔼 z : ZMod q, star ((scalarPowerCharacter q N r)⁻¹ z) *
      (scalarPowerCharacter q N s)⁻¹ z) = if r = s then 1 else 0 :=
  additiveCharacters_orthogonal (fun r : Fin N => (scalarPowerCharacter q N r)⁻¹)
    (inv_injective.comp (scalarPowerCharacter_injective hNq)) r s

theorem inverseScalarPowerCharacter_apply (r : Fin N) (z : ZMod q) :
    (scalarPowerCharacter q N r)⁻¹ z = star (ZMod.stdAddChar z ^ (r.val + 1)) := by
  rw [AddChar.inv_apply', AddChar.inv_apply_eq_conj]
  rfl

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The represented phased polynomial is exactly the finite phase sum. -/
theorem represented_phase_polynomial (ρ : B →⋆ₐ[ℂ] (K →L[ℂ] K))
    (u : unitary B) (z : ZMod q) (ξ : K) :
    ρ (unitaryHaarPolynomial N (scalarPhaseTwist z u)) ξ =
      (Real.sqrt (N : ℝ))⁻¹ • finitePhaseSum
        (fun r : Fin N => scalarPowerCharacter q N r)
        (fun r => ρ ((u : B) ^ (r.val + 1)) ξ) z := by
  simp only [unitaryHaarPolynomial, unitaryHaarSum, scalarPhaseTwist_coe,
    smul_pow, map_smul, map_sum, smul_apply, _root_.sum_apply,
    finitePhaseSum, scalarPowerCharacter_apply]
  exact Complex.coe_smul _ _

/-- The adjoint polynomial uses the inverse phase characters and the adjoints
of the same unitary powers. -/
theorem represented_adjoint_phase_polynomial (ρ : B →⋆ₐ[ℂ] (K →L[ℂ] K))
    (u : unitary B) (z : ZMod q) (ξ : K) :
    ρ (star (unitaryHaarPolynomial N (scalarPhaseTwist z u))) ξ =
      (Real.sqrt (N : ℝ))⁻¹ • finitePhaseSum
        (fun r : Fin N => ⇑((scalarPowerCharacter q N r)⁻¹ : AddChar (ZMod q) ℂ))
        (fun r => ρ (star ((u : B) ^ (r.val + 1))) ξ) z := by
  simp only [unitaryHaarPolynomial, unitaryHaarSum, scalarPhaseTwist_coe,
    smul_pow, star_smul, star_sum, map_smul, map_sum, smul_apply,
    _root_.sum_apply, finitePhaseSum, inverseScalarPowerCharacter_apply]
  rw [show star (((Real.sqrt (N : ℝ))⁻¹ : ℝ) : ℂ) =
      (((Real.sqrt (N : ℝ))⁻¹ : ℝ) : ℂ) from by exact Complex.conj_ofReal _]
  exact Complex.coe_smul _ _

theorem norm_represented_unitary_power (ρ : B →⋆ₐ[ℂ] (K →L[ℂ] K))
    (u : unitary B) (m : ℕ) (ξ : K) : ‖ρ ((u : B) ^ m) ξ‖ = ‖ξ‖ := by
  have h := Unitary.norm_map (Unitary.map (StarMonoidHom.ofClass ρ) (u ^ m)) ξ
  exact h

theorem norm_represented_adjoint_unitary_power (ρ : B →⋆ₐ[ℂ] (K →L[ℂ] K))
    (u : unitary B) (m : ℕ) (ξ : K) : ‖ρ (star ((u : B) ^ m)) ξ‖ = ‖ξ‖ := by
  have h := Unitary.norm_map (Unitary.map (StarMonoidHom.ofClass ρ) (star (u ^ m))) ξ
  exact h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {n : ℕ}

theorem recoveryForwardRow_phase_apply (M : VonNeumannAlgebra H)
    (u : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (z : ZMod q) (a : Fin n) (ξ : Generator.FiniteHilbert (Fin n) H) :
    recoveryForwardRow M N a (scalarPhaseTwist z u) ξ =
      Real.sqrt (n : ℝ) • ((Real.sqrt (N : ℝ))⁻¹ • finitePhaseSum
        (fun r : Fin N => scalarPowerCharacter q N r)
        (fun r => (((u : Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r.val + 1)).val) ξ) z) a := by
  change (Real.sqrt (n : ℝ) : ℂ) •
    (((unitaryHaarPolynomial N (scalarPhaseTwist z u)).val) ξ) a = _
  have hpoly := represented_phase_polynomial (N := N)
    (matrixVonNeumann (ι := Fin n) M).toStarSubalgebra.subtype u z ξ
  change (unitaryHaarPolynomial N (scalarPhaseTwist z u)).val ξ =
    (Real.sqrt (N : ℝ))⁻¹ • finitePhaseSum
      (fun r : Fin N => scalarPowerCharacter q N r)
      (fun r => (((u : Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r.val + 1)).val) ξ) z at hpoly
  rw [hpoly]
  exact Complex.coe_smul _ _

theorem recoveryBackwardRow_phase_apply (M : VonNeumannAlgebra H)
    (u : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (z : ZMod q) (a : Fin n) (ξ : Generator.FiniteHilbert (Fin n) H) :
    recoveryBackwardRow M N a (scalarPhaseTwist z u) ξ =
      Real.sqrt (n : ℝ) • ((Real.sqrt (N : ℝ))⁻¹ • finitePhaseSum
        (fun r : Fin N => ⇑((scalarPowerCharacter q N r)⁻¹ : AddChar (ZMod q) ℂ))
        (fun r => ((star ((u : Algebra (matrixVonNeumann (ι := Fin n) M)) ^
          (r.val + 1))).val) ξ) z) a := by
  change (Real.sqrt (n : ℝ) : ℂ) •
    (((star (unitaryHaarPolynomial N (scalarPhaseTwist z u))).val) ξ) a = _
  have hpoly := represented_adjoint_phase_polynomial (N := N)
    (matrixVonNeumann (ι := Fin n) M).toStarSubalgebra.subtype u z ξ
  change (star (unitaryHaarPolynomial N (scalarPhaseTwist z u))).val ξ =
    (Real.sqrt (N : ℝ))⁻¹ • finitePhaseSum
      (fun r : Fin N => ⇑((scalarPowerCharacter q N r)⁻¹ : AddChar (ZMod q) ℂ))
      (fun r => ((star ((u : Algebra (matrixVonNeumann (ι := Fin n) M)) ^
        (r.val + 1))).val) ξ) z at hpoly
  rw [hpoly]
  exact Complex.coe_smul _ _

/-- The random scalar phase and coordinate row have exact forward RMS norm. -/
theorem recoveryForwardRows_finiteRMS (M : VonNeumannAlgebra H)
    (u : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (hN : 0 < N) (hNq : N < q) (ξ : Generator.FiniteHilbert (Fin n) H) :
    finiteRMS (fun za : ZMod q × Fin n =>
      recoveryForwardRow M N za.2 (scalarPhaseTwist za.1 u) ξ) = ‖ξ‖ := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hmean := phase_basis_row_mean_square
    (fun r : Fin N => scalarPowerCharacter q N r) (scalarPowerCharacter_orthogonal hNq)
    (fun r => (((u : Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r.val + 1)).val) ξ)
    ξ (fun r => norm_represented_unitary_power
      (matrixVonNeumann (ι := Fin n) M).toStarSubalgebra.subtype u _ ξ)
  simp only [Fintype.card_fin] at hmean
  simp_rw [finiteRMS, recoveryForwardRow_phase_apply, hmean, Real.sqrt_sq (norm_nonneg ξ)]

/-- The inverse phases give the identical normalization for backward rows. -/
theorem recoveryBackwardRows_finiteRMS (M : VonNeumannAlgebra H)
    (u : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (hN : 0 < N) (hNq : N < q) (ξ : Generator.FiniteHilbert (Fin n) H) :
    finiteRMS (fun za : ZMod q × Fin n =>
      recoveryBackwardRow M N za.2 (scalarPhaseTwist za.1 u) ξ) = ‖ξ‖ := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hmean := phase_basis_row_mean_square
    (fun r : Fin N => ⇑((scalarPowerCharacter q N r)⁻¹ : AddChar (ZMod q) ℂ))
    (inverseScalarPowerCharacter_orthogonal hNq)
    (fun r => ((star ((u : Algebra (matrixVonNeumann (ι := Fin n) M)) ^
      (r.val + 1))).val) ξ)
    ξ (fun r => norm_represented_adjoint_unitary_power
      (matrixVonNeumann (ι := Fin n) M).toStarSubalgebra.subtype u _ ξ)
  simp only [Fintype.card_fin] at hmean
  simp_rw [finiteRMS, recoveryBackwardRow_phase_apply, hmean, Real.sqrt_sq (norm_nonneg ξ)]

end

end KadisonKastler

end OAI
