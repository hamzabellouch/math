import OAI.LinearAlgebra.CirculantHadamard.CyclicRing
import OAI.LinearAlgebra.CirculantHadamard.BinaryBlocks
import OAI.LinearAlgebra.CirculantHadamard.BinaryCoefficients
import OAI.LinearAlgebra.CirculantHadamard.CyclotomicRings
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

universe uR uA

/-!
# Cancelling the factor four in the binary norm identities

The coefficient ring may be a domain; the finite cyclic group algebra is not
assumed to be a domain. Cancellation is performed separately at every
coefficient. In particular these statements apply both to complex coefficients
and to the actual Gaussian subring of `ℂ`.

`CyclicRing.ringStar` conjugates coefficients as well as reversing exponents.
The evaluation bridge requires compatibility with this full operation,
including at the fourth root `i`; an inversion-only operation would not suffice.
-/

noncomputable section

namespace CirculantHadamard.BinaryNorms

open CyclicRing

section CoefficientCancellation

variable {R : Type uR} [CommRing R] [IsDomain R] [CharZero R]
variable {n : ℕ}

/-- Cancel four coefficientwise, without any domain assumption on the group
algebra. -/
theorem four_nsmul_cancel {f g : Elem R n}
    (h : (4 : ℕ) • f = (4 : ℕ) • g) : f = g := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro a
  let coeff : Elem R n →+ R :=
    { toFun := fun p => p.coeff a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have ha := congrArg coeff h
  rw [map_nsmul, map_nsmul] at ha
  have hc : (4 : R) * f.coeff a = (4 : R) * g.coeff a := by
    simp only [coeff, nsmul_eq_mul, Nat.cast_ofNat] at ha
    convert ha using 1
  exact mul_left_cancel₀ (by norm_num : (4 : R) ≠ 0) hc

end CoefficientCancellation

section NormCancellation

variable {R : Type uR} [CommRing R] [StarRing R]
variable {n : ℕ} [NeZero n]

/-- Coefficient conjugation fixes natural scalar multiples. -/
theorem ringStar_nsmul (k : ℕ) (x : Elem R n) :
    ringStar (k • x) = k • ringStar x := by
  exact map_nsmul (ringStarRingHom n) k x

/-- The exact factor four before cancellation; this is valid even when the
coefficient ring itself has zero divisors. -/
theorem two_nsmul_norm (x : Elem R n) :
    ((2 : ℕ) • x) * ringStar ((2 : ℕ) • x) =
      (4 : ℕ) • (x * ringStar x) := by
  rw [ringStar_nsmul]
  simp only [nsmul_eq_mul]
  ring

variable [IsDomain R] [CharZero R]

theorem norm_of_two_nsmul (u : ℕ) (x : Elem R n)
    (h : ((2 : ℕ) • x) * ringStar ((2 : ℕ) • x) =
      ((4 * u ^ 2 : ℕ) : Elem R n)) :
    x * ringStar x = scalar n ((u ^ 2 : ℕ) : R) := by
  rw [scalar_natCast]
  apply four_nsmul_cancel
  calc
    (4 : ℕ) • (x * ringStar x) =
        ((2 : ℕ) • x) * ringStar ((2 : ℕ) • x) :=
      (two_nsmul_norm x).symm
    _ = ((4 * u ^ 2 : ℕ) : Elem R n) := h
    _ = (4 : ℕ) • ((u ^ 2 : ℕ) : Elem R n) := by
      simp only [Nat.cast_mul, nsmul_eq_mul, Nat.cast_ofNat]

theorem norm_of_evaluation
    {A : Type uA} [CommRing A] (sigma : A → A)
    (eval : A →+* Elem R n) (u : ℕ) (h : A) (x : Elem R n)
    (hnorm : h * sigma h = ((4 * u ^ 2 : ℕ) : A))
    (hstar : eval (sigma h) = ringStar (eval h))
    (hvalue : eval h = (2 : ℕ) • x) :
    x * ringStar x = scalar n ((u ^ 2 : ℕ) : R) := by
  apply norm_of_two_nsmul u x
  rw [← hvalue, ← hstar, ← map_mul, hnorm, map_natCast]

end NormCancellation

section ActualBinaryElements

open BinaryBlocks BinaryCoefficients

variable {m : ℕ} [NeZero m]

/-- The partial evaluation uses the same literal coefficient cast as the
constructed Gaussian element. -/
theorem mappedBlock_intCast {R : Type uR} [CommRing R]
    (f : ProductElem ℤ m) (j : ZMod 4) :
    mappedBlock m (Int.castRingHom R) f j =
      AddMonoidAlgebra.ofCoeff (castCoeffs (block f j).coeff) := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro a
  rfl

/-- The value at one is twice the actual integral `c`, not a freely chosen
element with a prescribed evaluation. -/
theorem evaluation_one_eq_two_c (f : ProductElem ℤ m)
    (hsign : ∀ a, IsSign (f.coeff a)) :
    partialEval m (RingHom.id ℤ) 1 (by simp) f =
      (2 : ℕ) • AddMonoidAlgebra.ofCoeff (c (fun j => (blocks f j).coeff)) := by
  rw [partialEval_one]
  apply AddMonoidAlgebra.coeff_injective
  have hv := (two_c (H := fun j => (blocks f j).coeff) (blocks_signs f hsign)).symm
  simp only [AddMonoidAlgebra.coeff_add, two_smul, mappedBlock, blocks, block,
    RingHom.id_apply] at hv ⊢
  convert hv using 1

/-- The value at minus one is twice the actual integral `d`. -/
theorem evaluation_neg_one_eq_two_d (f : ProductElem ℤ m)
    (hsign : ∀ a, IsSign (f.coeff a)) :
    partialEval m (RingHom.id ℤ) (-1) (by norm_num) f =
      (2 : ℕ) • AddMonoidAlgebra.ofCoeff (d (fun j => (blocks f j).coeff)) := by
  rw [partialEval_neg_one]
  apply AddMonoidAlgebra.coeff_injective
  have hv := (two_d (H := fun j => (blocks f j).coeff) (blocks_signs f hsign)).symm
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    two_smul, mappedBlock, blocks, block, RingHom.id_apply] at hv ⊢
  convert hv using 1

/-- The fourth-root evaluation is twice the constructed Gaussian pair.
The coefficient ring is arbitrary, including the actual Gaussian ring,
without assuming a group-algebra domain. -/
theorem evaluation_fourthRoot_eq_two_gOver {R : Type uR} [CommRing R]
    (i : R) (hi : i ^ 2 = -1) (f : ProductElem ℤ m)
    (hsign : ∀ a, IsSign (f.coeff a)) :
    partialEval m (Int.castRingHom R) i (fourthRoot_pow_four i hi) f =
      (2 : ℕ) • AddMonoidAlgebra.ofCoeff (gOver i (fun j => (blocks f j).coeff)) := by
  rw [partialEval_fourthRoot m (Int.castRingHom R) i hi f]
  simp only [mappedBlock_intCast]
  apply AddMonoidAlgebra.coeff_injective
  have hv := (two_gOver i (H := fun j => (blocks f j).coeff) (blocks_signs f hsign)).symm
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    AddMonoidAlgebra.coeff_smul, two_smul, blocks] at hv ⊢
  convert hv using 1

theorem c_norm_of_product_norm (u : ℕ) (f : ProductElem ℤ m)
    (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * groupStar f = ((4 * u ^ 2 : ℕ) : ProductElem ℤ m)) :
    Mul.mul (α := Elem ℤ m) (AddMonoidAlgebra.ofCoeff (c (fun j => (blocks f j).coeff))) (ringStar (AddMonoidAlgebra.ofCoeff (c (fun j => (blocks f j).coeff)))) =
      scalar m ((u ^ 2 : ℕ) : ℤ) := by
  exact norm_of_evaluation groupStar
    (partialEval m (RingHom.id ℤ) 1 (by simp)) u f (AddMonoidAlgebra.ofCoeff (c (fun j => (blocks f j).coeff))) hnorm
    (partialEval_groupStar m (RingHom.id ℤ) 1 (by simp)
      (fun _ => by simp) one_character_star f)
    (evaluation_one_eq_two_c f hsign)

/-- The second norm uses the real fourth root `-1` and its genuine star law. -/
theorem d_norm_of_product_norm (u : ℕ) (f : ProductElem ℤ m)
    (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * groupStar f = ((4 * u ^ 2 : ℕ) : ProductElem ℤ m)) :
    Mul.mul (α := Elem ℤ m) (AddMonoidAlgebra.ofCoeff (d (fun j => (blocks f j).coeff))) (ringStar (AddMonoidAlgebra.ofCoeff (d (fun j => (blocks f j).coeff)))) =
      scalar m ((u ^ 2 : ℕ) : ℤ) := by
  exact norm_of_evaluation groupStar
    (partialEval m (RingHom.id ℤ) (-1) (by norm_num)) u f (AddMonoidAlgebra.ofCoeff (d (fun j => (blocks f j).coeff))) hnorm
    (partialEval_groupStar m (RingHom.id ℤ) (-1) (by norm_num)
      (fun _ => by simp) neg_one_character_star f)
    (evaluation_neg_one_eq_two_d f hsign)

/-- The third norm uses conjugation of the fourth root, not exponent reversal
alone. Both the square equation and the conjugation equation are explicit. -/
theorem gOver_norm_of_product_norm {R : Type uR} [CommRing R] [StarRing R]
    [IsDomain R] [CharZero R] (i : R) (hi : i ^ 2 = -1) (hstar : star i = -i)
    (u : ℕ) (f : ProductElem ℤ m) (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * groupStar f = ((4 * u ^ 2 : ℕ) : ProductElem ℤ m)) :
    Mul.mul (α := Elem R m) (AddMonoidAlgebra.ofCoeff (gOver i (fun j => (blocks f j).coeff))) (ringStar (AddMonoidAlgebra.ofCoeff (gOver i (fun j => (blocks f j).coeff)))) =
      scalar m ((u ^ 2 : ℕ) : R) := by
  exact norm_of_evaluation groupStar
    (partialEval m (Int.castRingHom R) i (fourthRoot_pow_four i hi))
    u f (AddMonoidAlgebra.ofCoeff (gOver i (fun j => (blocks f j).coeff))) hnorm
    (partialEval_groupStar m (Int.castRingHom R) i (fourthRoot_pow_four i hi)
      (fun _ => by simp) (fourthRoot_character_star i hi hstar) f)
    (evaluation_fourthRoot_eq_two_gOver i hi f hsign)

/-- The same cancellation is valid in `ℂ[C_m]`, despite that ring having zero
divisors. This specializes the actual coefficient construction `g`. -/
theorem g_norm_of_product_norm (u : ℕ) (f : ProductElem ℤ m)
    (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * groupStar f = ((4 * u ^ 2 : ℕ) : ProductElem ℤ m)) :
    Mul.mul (α := Elem ℂ m) (AddMonoidAlgebra.ofCoeff (g (fun j => (blocks f j).coeff))) (ringStar (AddMonoidAlgebra.ofCoeff (g (fun j => (blocks f j).coeff)))) =
      scalar m ((u ^ 2 : ℕ) : ℂ) :=
  gOver_norm_of_product_norm Complex.I Complex.I_sq (by simp) u f hsign hnorm

/-- Conjugation negates the imaginary unit in the actual Gaussian subring. -/
theorem star_gaussianI : star CyclotomicRings.gaussianI = -CyclotomicRings.gaussianI := by
  apply Subtype.ext
  change star Complex.I = -Complex.I
  simp

/-- The integral Gaussian norm, before any character evaluation or localization. -/
theorem gaussian_g_norm_of_product_norm (u : ℕ) (f : ProductElem ℤ m)
    (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * groupStar f = ((4 * u ^ 2 : ℕ) : ProductElem ℤ m)) :
    Mul.mul (α := Elem CyclotomicRings.GaussianRing m)
        (AddMonoidAlgebra.ofCoeff (gOver CyclotomicRings.gaussianI (fun j => (blocks f j).coeff)))
        (ringStar (AddMonoidAlgebra.ofCoeff (gOver CyclotomicRings.gaussianI (fun j => (blocks f j).coeff)))) =
      scalar m ((u ^ 2 : ℕ) : CyclotomicRings.GaussianRing) :=
  gOver_norm_of_product_norm CyclotomicRings.gaussianI CyclotomicRings.gaussianI_sq
    star_gaussianI u f hsign hnorm

end ActualBinaryElements

/-- The complete binary norm step starts from the original cyclic sign row.
The CRT transport, block signs, doubled evaluation values, full-star
compatibility, and scalar cancellation are all proved in the construction.
No separate norm premise for `c`, `d`, or `g` is accepted. -/
theorem binary_norms_of_cyclic_norm {u : ℕ} [NeZero u] (hu : Odd u)
    (f : Elem ℤ (4 * u ^ 2)) (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * ringStar f = scalar (4 * u ^ 2) ((4 * u ^ 2 : ℕ) : ℤ)) :
    let H := BinaryBlocks.blocks (BinaryBlocks.crt ℤ u hu f)
    Mul.mul (α := Elem ℤ (u ^ 2)) (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.c (fun j => (H j).coeff)))
        (ringStar (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.c (fun j => (H j).coeff)))) =
        scalar (u ^ 2) ((u ^ 2 : ℕ) : ℤ) ∧
      Mul.mul (α := Elem ℤ (u ^ 2)) (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.d (fun j => (H j).coeff)))
          (ringStar (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.d (fun j => (H j).coeff)))) =
        scalar (u ^ 2) ((u ^ 2 : ℕ) : ℤ) ∧
      Mul.mul (α := Elem CyclotomicRings.GaussianRing (u ^ 2))
          (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.gOver CyclotomicRings.gaussianI (fun j => (H j).coeff)))
          (ringStar (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.gOver CyclotomicRings.gaussianI (fun j => (H j).coeff)))) =
        scalar (u ^ 2) ((u ^ 2 : ℕ) : CyclotomicRings.GaussianRing) := by
  let F := BinaryBlocks.crt ℤ u hu f
  have hs : ∀ a, IsSign (F.coeff a) := by
    intro a
    simpa only [F, BinaryBlocks.crt_apply] using
      hsign ((BinaryBlocks.crtIndex u hu).symm a)
  have hn : F * groupStar F = ((4 * u ^ 2 : ℕ) : BinaryBlocks.ProductElem ℤ (u ^ 2)) :=
    BinaryBlocks.crt_norm hu f (4 * u ^ 2) (by simpa only [scalar_natCast] using hnorm)
  exact ⟨c_norm_of_product_norm u F hs hn, d_norm_of_product_norm u F hs hn,
    gaussian_g_norm_of_product_norm u F hs hn⟩

end CirculantHadamard.BinaryNorms

end

end OAI
