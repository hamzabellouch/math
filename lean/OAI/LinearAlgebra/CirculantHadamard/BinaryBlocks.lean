import OAI.LinearAlgebra.CirculantHadamard.Basic
import OAI.LinearAlgebra.CirculantHadamard.CyclicRing
import OAI.LinearAlgebra.CirculantHadamard.CyclicPolynomial
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

universe uR uS

/-!
# The actual four-block decomposition and partial evaluations

The Chinese remainder equivalence transports the actual cyclic group ring,
not just a coefficient count. Coefficients of its four slices are the original
signs. Partial evaluation is a ring homomorphism defined on the product group
algebra and intertwines coefficient conjugation with index reversal.
-/

noncomputable section

namespace CirculantHadamard.BinaryBlocks

open CyclicRing
open scoped BigOperators

abbrev ProductElem (R : Type uR) [Semiring R] (m : ℕ) :=
  AddMonoidAlgebra R (ZMod 4 × ZMod m)

theorem four_coprime_sq {u : ℕ} (hu : Odd u) : Nat.Coprime 4 (u ^ 2) := by
  simpa using (hu.coprime_two_left.pow_left 2).pow_right 2

/-- The concrete CRT map on the exponent group. -/
def crtIndex (u : ℕ) (hu : Odd u) :
    ZMod (4 * u ^ 2) ≃+ ZMod 4 × ZMod (u ^ 2) :=
  (ZMod.chineseRemainder (four_coprime_sq hu)).toAddEquiv

/-- The resulting algebra equivalence preserves the actual convolution. -/
def crt (R : Type uR) [CommRing R] (u : ℕ) (hu : Odd u) :
    Elem R (4 * u ^ 2) ≃ₐ[R] ProductElem R (u ^ 2) :=
  AddMonoidAlgebra.domCongr R R (crtIndex u hu)

@[simp] theorem crt_apply {R : Type uR} [CommRing R] {u : ℕ} (hu : Odd u)
    (f : Elem R (4 * u ^ 2)) (a : ZMod 4 × ZMod (u ^ 2)) :
    (crt R u hu f).coeff a = f.coeff ((crtIndex u hu).symm a) := by
  exact AddMonoidAlgebra.coeff_domCongr (R := R) (A := R) (crtIndex u hu) f a

theorem crt_ringStar {R : Type uR} [CommRing R] [StarRing R]
    {u : ℕ} [NeZero u] (hu : Odd u) (f : Elem R (4 * u ^ 2)) :
    crt R u hu (ringStar f) = groupStar (crt R u hu f) := by
  ext a
  simp only [crt_apply, ringStar_apply, groupStar_apply, map_neg]

theorem crt_norm {R : Type uR} [CommRing R] [StarRing R]
    {u : ℕ} [NeZero u] (hu : Odd u) (f : Elem R (4 * u ^ 2)) (N : ℕ)
    (hnorm : f * ringStar f = (N : Elem R (4 * u ^ 2))) :
    crt R u hu f * groupStar (crt R u hu f) = (N : ProductElem R (u ^ 2)) := by
  rw [← crt_ringStar hu, ← map_mul, hnorm, map_natCast]

def block {R : Type uR} [Semiring R] {m : ℕ} [NeZero m]
    (f : ProductElem R m) (j : ZMod 4) : Elem R m :=
  ofCoeffs fun b => f.coeff (j, b)

@[simp] theorem block_apply {R : Type uR} [Semiring R] {m : ℕ} [NeZero m]
    (f : ProductElem R m) (j : ZMod 4) (b : ZMod m) : (block f j).coeff b = f.coeff (j, b) := rfl

/-- Fin-four indexing agrees with the coefficient arithmetic used by the halves. -/
def blocks {R : Type uR} [Semiring R] {m : ℕ} [NeZero m]
    (f : ProductElem R m) : Fin 4 → Elem R m := fun j => block f j

@[simp] theorem blocks_apply {R : Type uR} [Semiring R] {m : ℕ} [NeZero m]
    (f : ProductElem R m) (j : Fin 4) (b : ZMod m) : (blocks f j).coeff b = f.coeff (j, b) := rfl

theorem blocks_signs {m : ℕ} [NeZero m] (f : ProductElem ℤ m)
    (hf : ∀ a, IsSign (f.coeff a)) : ∀ j b, IsSign ((blocks f j).coeff b) :=
  fun j b => hf (j, b)

theorem crt_blocks_signs {u : ℕ} [NeZero u] (hu : Odd u)
    (f : Elem ℤ (4 * u ^ 2)) (hf : ∀ a, IsSign (f.coeff a)) :
    ∀ j b, IsSign ((blocks (crt ℤ u hu f) j).coeff b) := by
  intro j b
  rw [blocks_apply, crt_apply]
  exact hf ((crtIndex u hu).symm (j, b))

section Evaluation

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] (m : ℕ)

/-- A fourth-root character on the first factor, retaining the second factor. -/
def partialCharacter (z : S) (hz : z ^ 4 = 1) :
    Multiplicative (ZMod 4 × ZMod m) →* Elem S m where
  toFun a := AddMonoidAlgebra.single a.toAdd.2
    (CyclicPolynomial.powerCharacter 4 z hz (Multiplicative.ofAdd a.toAdd.1))
  map_one' := by
    change AddMonoidAlgebra.single 0
      (CyclicPolynomial.powerCharacter 4 z hz 1) = 1
    rw [map_one]
    rfl
  map_mul' a b := by
    change AddMonoidAlgebra.single (a.toAdd.2 + b.toAdd.2)
      (CyclicPolynomial.powerCharacter 4 z hz
        (Multiplicative.ofAdd a.toAdd.1 * Multiplicative.ofAdd b.toAdd.1)) =
      AddMonoidAlgebra.single a.toAdd.2
        (CyclicPolynomial.powerCharacter 4 z hz (Multiplicative.ofAdd a.toAdd.1)) *
      AddMonoidAlgebra.single b.toAdd.2
        (CyclicPolynomial.powerCharacter 4 z hz (Multiplicative.ofAdd b.toAdd.1))
    rw [map_mul, AddMonoidAlgebra.single_mul_single]

/-- Actual partial evaluation, allowing the integer-to-complex coefficient map. -/
def partialEval (φ : R →+* S) (z : S) (hz : z ^ 4 = 1) :
    ProductElem R m →+* Elem S m :=
  AddMonoidAlgebra.liftNCRingHom
    (AddMonoidAlgebra.singleZeroRingHom.comp φ) (partialCharacter m z hz)
    (fun _ _ => Commute.all _ _)

@[simp] theorem partialEval_single (φ : R →+* S) (z : S) (hz : z ^ 4 = 1)
    (a : ZMod 4 × ZMod m) (r : R) :
    partialEval m φ z hz (AddMonoidAlgebra.single a r) =
      AddMonoidAlgebra.single a.2 (φ r * z ^ a.1.val) := by
  simp [partialEval, AddMonoidAlgebra.liftNCRingHom,
    AddMonoidAlgebra.liftNC_single, partialCharacter,
    AddMonoidAlgebra.single_mul_single]

variable [NeZero m]

/-- The four coefficients are summed, with no loss of the second coordinate. -/
theorem partialEval_apply (φ : R →+* S) (z : S) (hz : z ^ 4 = 1)
    (f : ProductElem R m) (b : ZMod m) :
    (partialEval m φ z hz f).coeff b =
      ∑ j : ZMod 4, φ (f.coeff (j, b)) * z ^ j.val := by
  classical
  have hexp : f = ∑ a : ZMod 4 × ZMod m, AddMonoidAlgebra.single a (f.coeff a) := by
    simpa only [AddMonoidAlgebra.sum_coeff_single] using
      (Finsupp.sum_fintype f.coeff AddMonoidAlgebra.single
        (fun a => AddMonoidAlgebra.single_zero a))
  calc
    (partialEval m φ z hz f).coeff b =
        (partialEval m φ z hz (∑ a : ZMod 4 × ZMod m,
          AddMonoidAlgebra.single a (f.coeff a))).coeff b :=
            congrArg (fun g => (partialEval m φ z hz g).coeff b) hexp
    _ = ∑ a : ZMod 4 × ZMod m,
        (AddMonoidAlgebra.single a.2 (φ (f.coeff a) * z ^ a.1.val)).coeff b := by
      rw [map_sum]
      simp only [partialEval_single, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

def mappedBlock (φ : R →+* S) (f : ProductElem R m) (j : ZMod 4) : Elem S m :=
  ofCoeffs fun b => φ (f.coeff (j, b))

@[simp] theorem mappedBlock_apply (φ : R →+* S) (f : ProductElem R m)
    (j : ZMod 4) (b : ZMod m) : (mappedBlock m φ f j).coeff b = φ (f.coeff (j, b)) := rfl

theorem partialEval_four (φ : R →+* S) (z : S) (hz : z ^ 4 = 1)
    (f : ProductElem R m) :
    partialEval m φ z hz f = mappedBlock m φ f 0 + z • mappedBlock m φ f 1 +
      z ^ 2 • mappedBlock m φ f 2 + z ^ 3 • mappedBlock m φ f 3 := by
  ext b
  rw [partialEval_apply]
  change (∑ j : Fin 4, φ (f.coeff (j, b)) * z ^ j.val) =
    φ (f.coeff (0, b)) + z * φ (f.coeff (1, b)) +
      z ^ 2 * φ (f.coeff (2, b)) + z ^ 3 * φ (f.coeff (3, b))
  rw [Fin.sum_univ_four]
  change φ (f.coeff (0, b)) * z ^ 0 + φ (f.coeff (1, b)) * z ^ 1 +
    φ (f.coeff (2, b)) * z ^ 2 + φ (f.coeff (3, b)) * z ^ 3 = _
  simp only [pow_zero, pow_one, one_mul, mul_comm]

theorem partialEval_one (φ : R →+* S) (f : ProductElem R m) :
    partialEval m φ 1 (by simp) f = mappedBlock m φ f 0 + mappedBlock m φ f 1 +
      mappedBlock m φ f 2 + mappedBlock m φ f 3 := by
  simpa using partialEval_four m φ 1 (by simp) f

theorem partialEval_neg_one (φ : R →+* S) (f : ProductElem R m) :
    partialEval m φ (-1) (by norm_num) f = mappedBlock m φ f 0 - mappedBlock m φ f 1 +
      mappedBlock m φ f 2 - mappedBlock m φ f 3 := by
  have hn2 : (-1 : S) ^ 2 = 1 := by norm_num
  have hn3 : (-1 : S) ^ 3 = -1 := by norm_num
  simpa only [hn2, hn3, one_smul, neg_one_smul, sub_eq_add_neg]
    using partialEval_four m φ (-1) (by norm_num) f

theorem fourthRoot_pow_four (i : S) (hi : i ^ 2 = -1) : i ^ 4 = 1 := by
  calc
    i ^ 4 = (i ^ 2) ^ 2 := by ring
    _ = 1 := by rw [hi]; norm_num

/-- The Gaussian coefficient ring can use its actual imaginary unit directly. -/
theorem partialEval_fourthRoot (φ : R →+* S) (i : S) (hi : i ^ 2 = -1)
    (f : ProductElem R m) :
    partialEval m φ i (fourthRoot_pow_four i hi) f =
      mappedBlock m φ f 0 + i • mappedBlock m φ f 1 -
        mappedBlock m φ f 2 - i • mappedBlock m φ f 3 := by
  have hi3 : i ^ 3 = -i := by
    rw [pow_succ, hi]
    ring
  simpa only [hi, hi3, neg_one_smul, neg_smul, one_smul, sub_eq_add_neg]
    using partialEval_four m φ i (fourthRoot_pow_four i hi) f

end Evaluation

theorem partialEval_I {R : Type uR} [CommRing R] (m : ℕ) [NeZero m]
    (φ : R →+* ℂ) (f : ProductElem R m) :
    partialEval m φ Complex.I (by norm_num [pow_succ, Complex.I_sq]) f =
      mappedBlock m φ f 0 + Complex.I • mappedBlock m φ f 1 -
        mappedBlock m φ f 2 - Complex.I • mappedBlock m φ f 3 := by
  exact partialEval_fourthRoot m φ Complex.I Complex.I_sq f

section Star

variable {R : Type uR} {S : Type uS} [CommRing R] [StarRing R] [CommRing S] [StarRing S]
variable (m : ℕ) [NeZero m]

/-- Intertwining is proved on the actual ring maps, with both parts of the star. -/
theorem partialEval_groupStar (φ : R →+* S) (z : S) (hz : z ^ 4 = 1)
    (hφ : ∀ r, φ (star r) = star (φ r))
    (hchar : ∀ a : ZMod 4, z ^ (-a).val = star (z ^ a.val))
    (f : ProductElem R m) :
    partialEval m φ z hz (groupStar f) = ringStar (partialEval m φ z hz f) := by
  have hs (a : ZMod 4 × ZMod m) (r : R) :
      partialEval m φ z hz (groupStar (AddMonoidAlgebra.single a r)) =
        ringStar (partialEval m φ z hz (AddMonoidAlgebra.single a r)) := by
    rw [groupStar_single, partialEval_single, partialEval_single, ringStar_single]
    change AddMonoidAlgebra.single (-a.2) (φ (star r) * z ^ (-a.1).val) =
      AddMonoidAlgebra.single (-a.2) (star (φ r * z ^ a.1.val))
    rw [hφ, hchar, star_mul, mul_comm]
  have he : (partialEval m φ z hz).comp groupStarRingHom =
      (ringStarRingHom m).comp (partialEval m φ z hz) := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro r
      exact hs 0 r
    · intro a
      exact hs a 1
  exact RingHom.congr_fun he f

theorem one_character_star : ∀ a : ZMod 4, (1 : S) ^ (-a).val = star ((1 : S) ^ a.val) := by
  intro a
  simp

theorem neg_one_character_star :
    ∀ a : ZMod 4, (-1 : S) ^ (-a).val = star ((-1 : S) ^ a.val) := by
  intro a
  fin_cases a
  · change (-1 : S) ^ 0 = star ((-1 : S) ^ 0)
    simp
  · change (-1 : S) ^ 3 = star ((-1 : S) ^ 1)
    norm_num
  · change (-1 : S) ^ 2 = star ((-1 : S) ^ 2)
    norm_num
  · change (-1 : S) ^ 1 = star ((-1 : S) ^ 3)
    norm_num

theorem fourthRoot_character_star (i : S) (hi : i ^ 2 = -1) (hstar : star i = -i) :
    ∀ a : ZMod 4, i ^ (-a).val = star (i ^ a.val) := by
  have hi3 : i ^ 3 = -i := by
    rw [pow_succ, hi]
    ring
  intro a
  fin_cases a
  · change i ^ 0 = star (i ^ 0)
    simp
  · change i ^ 3 = star (i ^ 1)
    simp [hi3, hstar]
  · change i ^ 2 = star (i ^ 2)
    rw [hi]
    simp
  · change i ^ 1 = star (i ^ 3)
    simp [hi3, hstar]

end Star

theorem I_character_star :
    ∀ a : ZMod 4, Complex.I ^ (-a).val = star (Complex.I ^ a.val) := by
  exact fourthRoot_character_star Complex.I Complex.I_sq (by simp)

end CirculantHadamard.BinaryBlocks

end

end OAI
