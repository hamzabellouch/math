import OAI.LinearAlgebra.CirculantHadamard.BinaryNorms
import OAI.LinearAlgebra.CirculantHadamard.PrimeCharacterEvaluations

namespace OAI

universe uR

/-!
# Evaluation of the actual binary coefficient construction

The integral `c,d` are mapped coefficientwise into the Gaussian subring, with
their proved convolution norms preserved. All values are taken by the
constructed prime-subset character map into the actual cyclotomic ring `B u`.
The norm equations follow from the original cyclic sign row.
-/

noncomputable section

namespace CirculantHadamard.BinaryEvaluation

open scoped BigOperators
open CyclicRing BinaryCoefficients CyclotomicRings PrimeComponents
open PrimeCharacterEvaluations

/- Select the canonical multiplication action directly. This avoids searching
through the concrete subalgebra's unrelated inherited scalar actions. -/
local instance gaussianSelfScalar : SMulZeroClass GaussianRing GaussianRing where
  smul r x := r * x
  smul_zero := mul_zero

local instance gaussianCoeffScalar (n : ℕ) :
    SMulZeroClass GaussianRing (ZMod n →₀ GaussianRing) := Finsupp.smulZeroClass

/-- The canonical coefficient action, with its group-algebra result type fixed. -/
def gaussianScale {n : ℕ} (r : GaussianRing) (x : Elem GaussianRing n) :
    Elem GaussianRing n :=
  AddMonoidAlgebra.ofCoeff
    (@SMul.smul GaussianRing (ZMod n →₀ GaussianRing)
      (gaussianCoeffScalar n).toSMul r x.coeff)

@[simp] theorem gaussianScale_apply {n : ℕ} (r : GaussianRing)
    (x : Elem GaussianRing n) (a : ZMod n) : (gaussianScale r x).coeff a = r * x.coeff a := rfl

section CoefficientCast

variable {R : Type uR} [CommRing R] {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem castCoeffs_add [NeZero n] (f g : Elem ℤ n) :
    AddMonoidAlgebra.ofCoeff (castCoeffs (R := R) (f + g).coeff) =
      AddMonoidAlgebra.ofCoeff (castCoeffs f.coeff) +
        AddMonoidAlgebra.ofCoeff (castCoeffs g.coeff) := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro x
  change ((f.coeff x + g.coeff x : ℤ) : R) = (f.coeff x : R) + (g.coeff x : R)
  exact Int.cast_add _ _

omit [NeZero n] in
theorem castCoeffs_sub [NeZero n] (f g : Elem ℤ n) :
    AddMonoidAlgebra.ofCoeff (castCoeffs (R := R) (f - g).coeff) =
      AddMonoidAlgebra.ofCoeff (castCoeffs f.coeff) -
        AddMonoidAlgebra.ofCoeff (castCoeffs g.coeff) := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro x
  change ((f.coeff x - g.coeff x : ℤ) : R) = (f.coeff x : R) - (g.coeff x : R)
  exact Int.cast_sub _ _

theorem castCoeffs_mul (f g : Elem ℤ n) :
    AddMonoidAlgebra.ofCoeff (castCoeffs (R := R) (f * g).coeff) =
      Mul.mul (α := Elem R n) (AddMonoidAlgebra.ofCoeff (castCoeffs f.coeff))
        (AddMonoidAlgebra.ofCoeff (castCoeffs g.coeff)) := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro x
  calc
    (((f * g).coeff x : ℤ) : R) = ∑ j, (f.coeff j : R) * (g.coeff (x - j) : R) := by
      rw [CyclicRing.mul_apply]
      simp only [Int.cast_sum, Int.cast_mul]
    _ = _ := (CyclicRing.mul_apply (AddMonoidAlgebra.ofCoeff (castCoeffs (R := R) f.coeff))
      (AddMonoidAlgebra.ofCoeff (castCoeffs g.coeff)) x).symm

theorem castCoeffs_ringStar [StarRing R] (f : Elem ℤ n) :
    AddMonoidAlgebra.ofCoeff (castCoeffs (R := R) (ringStar f).coeff) =
      ringStar (AddMonoidAlgebra.ofCoeff (castCoeffs f.coeff)) := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro x
  simp

omit [NeZero n] in
theorem castCoeffs_scalar [NeZero n] (r : ℤ) :
    AddMonoidAlgebra.ofCoeff (castCoeffs (R := R) (scalar n r).coeff) =
      scalar n (r : R) := by
  classical
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro x
  simp [scalar_apply]

/-- Coefficient maps preserve the norm equation. -/
theorem castCoeffs_norm [StarRing R] (f : Elem ℤ n) (r : ℕ)
    (hf : f * ringStar f = scalar n (r : ℤ)) :
    Mul.mul (α := Elem R n) (AddMonoidAlgebra.ofCoeff (castCoeffs f.coeff))
      (ringStar (AddMonoidAlgebra.ofCoeff (castCoeffs f.coeff))) = scalar n (r : R) := by
  have h := congrArg (fun z : Elem ℤ n =>
    AddMonoidAlgebra.ofCoeff (castCoeffs (R := R) z.coeff)) hf
  simpa only [castCoeffs_mul, castCoeffs_ringStar, castCoeffs_scalar,
    Int.cast_natCast] using h

end CoefficientCast

section GaussianBlocks

variable {n : ℕ} [NeZero n]

def aG (H : Fin 4 → Elem ℤ n) : Elem GaussianRing n :=
  AddMonoidAlgebra.ofCoeff (castCoeffs (a (fun j => (H j).coeff)))
def bG (H : Fin 4 → Elem ℤ n) : Elem GaussianRing n :=
  AddMonoidAlgebra.ofCoeff (castCoeffs (b (fun j => (H j).coeff)))
def cG (H : Fin 4 → Elem ℤ n) : Elem GaussianRing n :=
  AddMonoidAlgebra.ofCoeff (castCoeffs (c (fun j => (H j).coeff)))
def dG (H : Fin 4 → Elem ℤ n) : Elem GaussianRing n :=
  AddMonoidAlgebra.ofCoeff (castCoeffs (d (fun j => (H j).coeff)))
def gG (H : Fin 4 → Elem ℤ n) : Elem GaussianRing n :=
  AddMonoidAlgebra.ofCoeff (gOver gaussianI (fun j => (H j).coeff))
def UG (H : Fin 4 → Elem ℤ n) : Elem GaussianRing n :=
  AddMonoidAlgebra.ofCoeff (UOver gaussianI (fun j => (H j).coeff))
def JG : Elem GaussianRing n := AddMonoidAlgebra.ofCoeff (JOver GaussianRing)

theorem cG_eq (H : Fin 4 → Elem ℤ n) : cG H = aG H + bG H :=
  castCoeffs_add (AddMonoidAlgebra.ofCoeff (a (fun j => (H j).coeff)))
    (AddMonoidAlgebra.ofCoeff (b (fun j => (H j).coeff)))

theorem dG_eq (H : Fin 4 → Elem ℤ n) : dG H = aG H - bG H :=
  castCoeffs_sub (AddMonoidAlgebra.ofCoeff (a (fun j => (H j).coeff)))
    (AddMonoidAlgebra.ofCoeff (b (fun j => (H j).coeff)))

theorem gG_eq {H : Fin 4 → Elem ℤ n} (hH : Signs (fun j => (H j).coeff)) :
    gG H = aG H + gaussianScale gaussianI (bG H) -
      (gaussianScale (1 + gaussianI) JG + gaussianScale 2 (UG H)) := by
  calc
    gG H = aG H + gaussianScale gaussianI (bG H) -
        Add.add (α := Elem GaussianRing n)
          (AddMonoidAlgebra.ofCoeff (castCoeffs (H 2).coeff))
          (gaussianScale gaussianI (AddMonoidAlgebra.ofCoeff (castCoeffs (H 3).coeff))) := by
      apply AddMonoidAlgebra.coeff_injective
      have h := gOver_eq_ab gaussianI hH
      rw [sub_sub] at h
      simp only [gG, aG, bG, gaussianScale, AddMonoidAlgebra.coeff_sub,
        AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_ofCoeff]
      convert h using 1; rfl
    _ = _ := by
      apply congrArg
        (fun z : Elem GaussianRing n => aG H + gaussianScale gaussianI (bG H) - z)
      apply AddMonoidAlgebra.coeff_injective
      have h := binary_identity_over gaussianI hH
      simp only [gaussianScale, JG, UG, AddMonoidAlgebra.coeff_add,
        AddMonoidAlgebra.coeff_ofCoeff]
      convert h using 1; rfl

theorem cG_norm (H : Fin 4 → Elem ℤ n) (r : ℕ)
    (hc : Mul.mul (α := Elem ℤ n)
      (AddMonoidAlgebra.ofCoeff (c (fun j => (H j).coeff)))
      (ringStar (AddMonoidAlgebra.ofCoeff (c (fun j => (H j).coeff)))) =
      scalar n (r : ℤ)) :
    cG H * ringStar (cG H) = scalar n (r : GaussianRing) :=
  castCoeffs_norm (AddMonoidAlgebra.ofCoeff (c (fun j => (H j).coeff))) r hc

theorem dG_norm (H : Fin 4 → Elem ℤ n) (r : ℕ)
    (hd : Mul.mul (α := Elem ℤ n)
      (AddMonoidAlgebra.ofCoeff (d (fun j => (H j).coeff)))
      (ringStar (AddMonoidAlgebra.ofCoeff (d (fun j => (H j).coeff)))) =
      scalar n (r : ℤ)) :
    dG H * ringStar (dG H) = scalar n (r : GaussianRing) :=
  castCoeffs_norm (AddMonoidAlgebra.ofCoeff (d (fun j => (H j).coeff))) r hd

end GaussianBlocks

section Values

variable (u : ℕ) [NeZero u] (hu : 0 < u)

def iB : B u := gaussianToB u gaussianI

def aValue (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) : B u :=
  subsetEvaluation u hu S (aG H)
def bValue (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) : B u :=
  subsetEvaluation u hu S (bG H)
def cValue (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) : B u :=
  subsetEvaluation u hu S (cG H)
def dValue (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) : B u :=
  subsetEvaluation u hu S (dG H)
def gValue (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) : B u :=
  subsetEvaluation u hu S (gG H)
def UValue (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) : B u :=
  subsetEvaluation u hu S (UG H)
def JValue (S : Finset (PrimeIndex u)) : B u := subsetEvaluation u hu S JG

theorem subsetEvaluation_smul (S : Finset (PrimeIndex u)) (r : GaussianRing)
    (x : Elem GaussianRing (u ^ 2)) :
    subsetEvaluation u hu S (gaussianScale r x) =
      gaussianToB u r * subsetEvaluation u hu S x := by
  change evaluate (gaussianToB u).toRingHom (subsetCharacter u hu S) _ =
    gaussianToB u r * evaluate (gaussianToB u).toRingHom (subsetCharacter u hu S) x
  rw [evaluate_apply, evaluate_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change gaussianToB u (r * x.coeff a) * subsetCharacter u hu S (Multiplicative.ofAdd a) =
    gaussianToB u r *
      (gaussianToB u (x.coeff a) * subsetCharacter u hu S (Multiplicative.ofAdd a))
  rw [map_mul, mul_assoc]

theorem cValue_eq (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) :
    cValue u hu H S = aValue u hu H S + bValue u hu H S := by
  exact congrArg (subsetEvaluation u hu S) (cG_eq H) |>.trans (map_add _ _ _)

theorem dValue_eq (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) :
    dValue u hu H S = aValue u hu H S - bValue u hu H S := by
  exact congrArg (subsetEvaluation u hu S) (dG_eq H) |>.trans (map_sub _ _ _)

theorem gValue_eq {H : Fin 4 → Elem ℤ (u ^ 2)} (hH : Signs (fun j => (H j).coeff))
    (S : Finset (PrimeIndex u)) :
    gValue u hu H S = aValue u hu H S + iB u * bValue u hu H S -
      ((1 + iB u) * JValue u hu S + 2 * UValue u hu H S) := by
  have h := congrArg (subsetEvaluation u hu S) (gG_eq hH)
  simpa [map_add, map_sub, map_ofNat, subsetEvaluation_smul, iB, gValue, aValue, bValue,
    JValue, UValue] using h

theorem evaluated_norms (H : Fin 4 → Elem ℤ (u ^ 2))
    (hc : cG H * ringStar (cG H) = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (hd : dG H * ringStar (dG H) = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (hg : gG H * ringStar (gG H) = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (S : Finset (PrimeIndex u)) :
    cValue u hu H S * star (cValue u hu H S) = ((u ^ 2 : ℕ) : B u) ∧
      dValue u hu H S * star (dValue u hu H S) = ((u ^ 2 : ℕ) : B u) ∧
      gValue u hu H S * star (gValue u hu H S) = ((u ^ 2 : ℕ) : B u) :=
  ⟨subsetEvaluation_norm u hu S (cG H) hc,
    subsetEvaluation_norm u hu S (dG H) hd,
    subsetEvaluation_norm u hu S (gG H) hg⟩

end Values

/-- All three Gaussian norm equations come from the original cyclic sign row. -/
theorem gaussian_norms_of_cyclic_norm {u : ℕ} [NeZero u] (hu : Odd u)
    (f : Elem ℤ (4 * u ^ 2)) (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * ringStar f = scalar (4 * u ^ 2) ((4 * u ^ 2 : ℕ) : ℤ)) :
    let H := BinaryBlocks.blocks (BinaryBlocks.crt ℤ u hu f)
    cG H * ringStar (cG H) = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing) ∧
      dG H * ringStar (dG H) = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing) ∧
      gG H * ringStar (gG H) = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing) := by
  obtain ⟨hc, hd, hg⟩ := BinaryNorms.binary_norms_of_cyclic_norm hu f hsign hnorm
  exact ⟨cG_norm _ (u ^ 2) hc, dG_norm _ (u ^ 2) hd, hg⟩

/-- Actual subset evaluations of `c,d,g` all have star norm `u²`,
without independent binary-element norm assumptions. -/
theorem binary_evaluation_of_cyclic_norm {u : ℕ} [NeZero u] (hu : Odd u)
    (f : Elem ℤ (4 * u ^ 2)) (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * ringStar f = scalar (4 * u ^ 2) ((4 * u ^ 2 : ℕ) : ℤ))
    (S : Finset (PrimeIndex u)) :
    let hp : 0 < u := Nat.pos_of_ne_zero (NeZero.ne u)
    let H := BinaryBlocks.blocks (BinaryBlocks.crt ℤ u hu f)
    cValue u hp H S * star (cValue u hp H S) = ((u ^ 2 : ℕ) : B u) ∧
      dValue u hp H S * star (dValue u hp H S) = ((u ^ 2 : ℕ) : B u) ∧
      gValue u hp H S * star (gValue u hp H S) = ((u ^ 2 : ℕ) : B u) := by
  obtain ⟨hc, hd, hg⟩ := gaussian_norms_of_cyclic_norm hu f hsign hnorm
  exact evaluated_norms u (Nat.pos_of_ne_zero (NeZero.ne u)) _ hc hd hg S

end CirculantHadamard.BinaryEvaluation

end

end OAI
