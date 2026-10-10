import Mathlib

namespace OAI

noncomputable section
namespace PiExponent.DVRBranchExpansion
open PowerSeries

variable {C A : Type*} [Field C] [CommRing A] [Algebra C A]
variable (ρ : A →ₐ[C] C) (π : A) (hπ : π ≠ 0)
variable (hker : RingHom.ker ρ.toRingHom = Ideal.span {π})

include hker in

theorem residue_sub_dvd (a : A) : π ∣ a - algebraMap C A (ρ a) := by
  apply Ideal.mem_span_singleton.mp
  rw [← hker]
  change ρ (a - algebraMap C A (ρ a)) = 0
  simp

def remainder (a : A) : A := Classical.choose (residue_sub_dvd ρ π hker a)

theorem mul_remainder (a : A) : π * remainder ρ π hker a = a - algebraMap C A (ρ a) :=
  (Classical.choose_spec (residue_sub_dvd ρ π hker a)).symm

variable [IsDomain A]

include hπ in
@[simp] theorem remainder_add (a b : A) :
    remainder ρ π hker (a+b) = remainder ρ π hker a + remainder ρ π hker b := by
  apply mul_left_cancel₀ hπ
  rw [mul_add, mul_remainder, mul_remainder, mul_remainder, map_add, map_add]
  ring

include hπ in
@[simp] theorem remainder_smul (c : C) (a : A) :
    remainder ρ π hker (c • a) = c • remainder ρ π hker a := by
  apply mul_left_cancel₀ hπ
  rw [Algebra.smul_def, mul_remainder, map_mul, AlgHom.commutes, map_mul]
  rw [Algebra.smul_def, mul_left_comm, mul_remainder]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  ring

include hπ in
@[simp] theorem remainder_algebraMap (c : C) :
    remainder ρ π hker (algebraMap C A c) = 0 := by
  apply mul_left_cancel₀ hπ
  rw [mul_zero, mul_remainder, AlgHom.commutes]
  simp

include hker in
omit [IsDomain A] in
theorem residue_uniformizer : ρ π = 0 := by
  change π ∈ RingHom.ker ρ.toRingHom
  rw [hker]
  exact Ideal.subset_span (by simp)

include hπ in
@[simp] theorem remainder_uniformizer_mul (a : A) :
    remainder ρ π hker (π*a) = a := by
  apply mul_left_cancel₀ hπ
  rw [mul_remainder, map_mul, residue_uniformizer ρ π hker, zero_mul, map_zero, sub_zero]

def remainderLinear : A →ₗ[C] A where
  toFun := remainder ρ π hker
  map_add' := remainder_add ρ π hπ hker
  map_smul' := remainder_smul ρ π hπ hker

def expansionCoeff (n : ℕ) (a : A) : C := ρ ((remainderLinear ρ π hπ hker ^ n) a)

@[simp] theorem expansionCoeff_zero (a : A) : expansionCoeff ρ π hπ hker 0 a = ρ a := rfl

@[simp] theorem expansionCoeff_succ (n : ℕ) (a : A) :
    expansionCoeff ρ π hπ hker (n+1) a =
      expansionCoeff ρ π hπ hker n (remainder ρ π hker a) := by
  simp only [expansionCoeff, pow_succ, Module.End.mul_apply]
  rfl

@[simp] theorem expansionCoeff_add (n : ℕ) (a b : A) :
    expansionCoeff ρ π hπ hker n (a+b) =
      expansionCoeff ρ π hπ hker n a + expansionCoeff ρ π hπ hker n b := by
  simp [expansionCoeff]

@[simp] theorem expansionCoeff_smul (n : ℕ) (c : C) (a : A) :
    expansionCoeff ρ π hπ hker n (c • a) = c * expansionCoeff ρ π hπ hker n a := by
  simp [expansionCoeff]

def expansion (a : A) : PowerSeries C := PowerSeries.mk (fun n => expansionCoeff ρ π hπ hker n a)

@[simp] theorem coeff_expansion (a : A) (n : ℕ) :
    PowerSeries.coeff n (expansion ρ π hπ hker a) = expansionCoeff ρ π hπ hker n a :=
  PowerSeries.coeff_mk _ _

@[simp] theorem expansion_add (a b : A) :
    expansion ρ π hπ hker (a+b) = expansion ρ π hπ hker a + expansion ρ π hπ hker b := by
  ext n
  simp only [map_add, coeff_expansion, expansionCoeff_add]

@[simp] theorem expansion_smul (c : C) (a : A) :
    expansion ρ π hπ hker (c • a) = c • expansion ρ π hπ hker a := by
  ext n
  simp only [map_smul, coeff_expansion, expansionCoeff_smul, smul_eq_mul]

@[simp] theorem expansion_algebraMap (c : C) :
    expansion ρ π hπ hker (algebraMap C A c) = PowerSeries.C c := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_expansion, expansionCoeff_succ, remainder_algebraMap ρ π hπ hker]
    simp [expansionCoeff]

theorem expansion_rec (a : A) :
    expansion ρ π hπ hker a = PowerSeries.C (ρ a) +
      expansion ρ π hπ hker (remainder ρ π hker a) * PowerSeries.X := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp only [map_add, coeff_expansion, PowerSeries.coeff_succ_C,
      PowerSeries.coeff_succ_mul_X, expansionCoeff_succ, zero_add]

include hπ in

theorem remainder_mul (a b : A) :
    remainder ρ π hker (a*b) = remainder ρ π hker a * b +
      algebraMap C A (ρ a) * remainder ρ π hker b := by
  apply mul_left_cancel₀ hπ
  rw [mul_add, ← mul_assoc, mul_remainder, mul_left_comm π,
    mul_remainder, mul_remainder, map_mul, map_mul]
  ring

theorem expansion_mul (a b : A) :
    expansion ρ π hπ hker (a*b) = expansion ρ π hπ hker a * expansion ρ π hπ hker b := by
  apply PowerSeries.ext
  intro n
  induction n generalizing a b with
  | zero =>
    simp only [coeff_expansion, expansionCoeff_zero, map_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_expansion]
  | succ n ih =>
    calc
      PowerSeries.coeff (n+1) (expansion ρ π hπ hker (a*b)) =
          expansionCoeff ρ π hπ hker n (remainder ρ π hker (a*b)) := by
        rw [coeff_expansion, expansionCoeff_succ]
      _ = expansionCoeff ρ π hπ hker n (remainder ρ π hker a * b) +
          ρ a * expansionCoeff ρ π hπ hker n (remainder ρ π hker b) := by
        rw [remainder_mul ρ π hπ hker, ← Algebra.smul_def, expansionCoeff_add,
          expansionCoeff_smul]
      _ = PowerSeries.coeff n (expansion ρ π hπ hker (remainder ρ π hker a) *
          expansion ρ π hπ hker b) +
          ρ a * PowerSeries.coeff (n+1) (expansion ρ π hπ hker b) := by
        rw [← coeff_expansion, ih]
        rw [coeff_expansion, expansionCoeff_succ]
      _ = PowerSeries.coeff (n+1)
          ((expansion ρ π hπ hker (remainder ρ π hker a) * expansion ρ π hπ hker b) *
            PowerSeries.X + PowerSeries.C (ρ a) * expansion ρ π hπ hker b) := by
        simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C_mul]
      _ = PowerSeries.coeff (n+1) (expansion ρ π hπ hker a * expansion ρ π hπ hker b) := by
        conv_rhs => rw [expansion_rec ρ π hπ hker a]
        congr 1
        ring

def expansionHom : A →ₐ[C] PowerSeries C where
  toFun := expansion ρ π hπ hker
  map_zero' := by ext n; simp [expansionCoeff]
  map_one' := by simpa using expansion_algebraMap ρ π hπ hker (1 : C)
  map_add' := expansion_add ρ π hπ hker
  map_mul' := expansion_mul ρ π hπ hker
  commutes' := expansion_algebraMap ρ π hπ hker

@[simp] theorem constantCoeff_expansionHom (a : A) :
    PowerSeries.constantCoeff (expansionHom ρ π hπ hker a) = ρ a := by
  change PowerSeries.constantCoeff (expansion ρ π hπ hker a) = ρ a
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_expansion, expansionCoeff_zero]

theorem expansionHom_uniformizer : expansionHom ρ π hπ hker π = PowerSeries.X := by
  change expansion ρ π hπ hker π = PowerSeries.X
  rw [expansion_rec, residue_uniformizer ρ π hker, map_zero, zero_add]
  have hr : remainder ρ π hker π = 1 := by
    simpa using remainder_uniformizer_mul ρ π hπ hker (1 : A)
  rw [hr]
  have he : expansion ρ π hπ hker (1 : A) = 1 := by
    simpa using expansion_algebraMap ρ π hπ hker (1 : C)
  rw [he, one_mul]

end PiExponent.DVRBranchExpansion

end

end OAI
