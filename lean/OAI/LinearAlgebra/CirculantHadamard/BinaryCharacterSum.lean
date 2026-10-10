import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Fintype.Powerset
import OAI.LinearAlgebra.CirculantHadamard.AlternatingProducts
import OAI.LinearAlgebra.CirculantHadamard.BinaryCoefficients
import OAI.LinearAlgebra.CirculantHadamard.CyclicEvaluation
import OAI.LinearAlgebra.CirculantHadamard.PrimeCharacterEvaluations

namespace OAI

universe uG uR uA uI uT uK uk uB

/-!
# Finite character sums and the surviving empty subset

Translation of a finite group permutes its elements. Consequently a character
with one value different from `1` has zero total sum in a domain. In a family
indexed by subsets, this removes every nonempty subset once its actual
character has such a witness.

The unit-denominator formulation takes place in the coefficient ring itself,
so it can subsequently be mapped to a residue field of characteristic two.
It does not require a map from a characteristic-zero field to that residue
field. Nontriviality of the actual subset characters is supplied by their
primitive primary components, rather than assumed of all characters.
-/

namespace CirculantHadamard.BinaryCharacterSum

open scoped BigOperators

section CharacterSum

variable {G : Type uG} {R : Type uR} [Group G] [Fintype G] [CommRing R]

/-- A nontrivial value of a character forces its finite sum to vanish.
The proof uses the permutation of `G` given by left translation. -/
theorem character_sum_eq_zero [IsDomain R] (χ : G →* R)
    (hχ : ∃ g : G, χ g ≠ 1) : (∑ g : G, χ g) = 0 := by
  classical
  obtain ⟨g, hg⟩ := hχ
  apply eq_zero_of_mul_eq_self_left hg
  simpa only [Finset.mul_sum, ← map_mul] using
    (Group.mulLeft_bijective g).sum_comp (fun h : G => χ h)

/-- The trivial character sums to the cardinality of the group. -/
theorem character_sum_trivial (χ : G →* R) (hχ : ∀ g : G, χ g = 1) :
    (∑ g : G, χ g) = (Fintype.card G : R) := by
  simp [hχ]

end CharacterSum

section ActualGroupRing

variable {A : Type uA} {R : Type uR} [CommRing A] [CommRing R] {n : ℕ} [NeZero n]

/-- The coefficientwise all-ones element is literally the sum of the basis
elements, with coefficient one at each group element. -/
theorem JOver_eq_sum_single {G : Type uG} [Fintype G] :
    (BinaryCoefficients.JOver A : G →₀ A) = ∑ g : G, Finsupp.single g 1 := by
  classical
  ext g
  simp

/-- Evaluation of the actual all-ones group-ring element is the complete
character sum. `JOver` is not the scalar unit of the group ring. -/
theorem evaluate_J_eq_sum (φ : A →+* R)
    (χ : Multiplicative (ZMod n) →* R) :
    CyclicRing.evaluate φ χ (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n) =
      ∑ g : Multiplicative (ZMod n), χ g := by
  rw [CyclicRing.evaluate_apply]
  simp only [BinaryCoefficients.JOver_apply, map_one, one_mul]
  exact (Multiplicative.ofAdd : ZMod n ≃ Multiplicative (ZMod n)).sum_comp _

/-- A witnessed nontrivial character annihilates the actual group-ring `J`. -/
theorem evaluate_J_eq_zero [IsDomain R] (φ : A →+* R)
    (χ : Multiplicative (ZMod n) →* R)
    (hχ : ∃ g : Multiplicative (ZMod n), χ g ≠ 1) :
    CyclicRing.evaluate φ χ (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n) = 0 := by
  rw [evaluate_J_eq_sum]
  exact character_sum_eq_zero χ hχ

/-- At the trivial character, the actual group-ring `J` evaluates to `n`. -/
theorem evaluate_J_trivial (φ : A →+* R) :
    CyclicRing.evaluate φ (1 : Multiplicative (ZMod n) →* R)
      (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n) = (n : R) := by
  rw [CyclicRing.evaluate_apply]
  simp

end ActualGroupRing

/-- Collapse written directly with evaluations of the actual group-ring `J`.
Only character witnesses for nonempty subsets are used. -/
theorem subset_evaluate_J_mul
    {I : Type uI} {A : Type uA} {R : Type uR} [Fintype I] [DecidableEq I] [CommRing A]
    [CommRing R] [IsDomain R] {n : ℕ} [NeZero n]
    (φ : A →+* R) (χ : Finset I → Multiplicative (ZMod n) →* R)
    (ε d : Finset I → R) (hε : ε ∅ = 1) (htrivial : χ ∅ = 1)
    (hnonempty : ∀ S : Finset I, S.Nonempty →
      ∃ g : Multiplicative (ZMod n), χ S g ≠ 1) :
    (∑ S : Finset I, ε S * CyclicRing.evaluate φ (χ S)
      (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n) * d S) =
      (n : R) * d ∅ := by
  classical
  calc
    (∑ S : Finset I, ε S * CyclicRing.evaluate φ (χ S)
        (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n) * d S) =
        ε ∅ * CyclicRing.evaluate φ (χ ∅)
          (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n) * d ∅ := by
      apply Finset.sum_eq_single ∅
      · intro S _ hS
        rw [evaluate_J_eq_zero φ (χ S)
          (hnonempty S (Finset.nonempty_iff_ne_empty.mpr hS))]
        simp
      · simp
    _ = (n : R) * d ∅ := by
      rw [hε, one_mul, htrivial, evaluate_J_trivial]

/-- First prove the character sum in its domain, then change coefficient
rings. This does not assume nontriviality of the reduced characters and also
allows the coefficients `d S` to lie in a localization of the original ring. -/
theorem subset_map_evaluate_J_mul
    {I : Type uI} {A : Type uA} {R : Type uR} {T : Type uT} [Fintype I] [DecidableEq I] [CommRing A]
    [CommRing R] [IsDomain R] [CommRing T] {n : ℕ} [NeZero n]
    (φ : A →+* R) (ψ : R →+* T)
    (χ : Finset I → Multiplicative (ZMod n) →* R)
    (ε d : Finset I → T) (hε : ε ∅ = 1) (htrivial : χ ∅ = 1)
    (hnonempty : ∀ S : Finset I, S.Nonempty →
      ∃ g : Multiplicative (ZMod n), χ S g ≠ 1) :
    (∑ S : Finset I, ε S * ψ (CyclicRing.evaluate φ (χ S)
      (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n)) * d S) =
      (n : T) * d ∅ := by
  classical
  calc
    (∑ S : Finset I, ε S * ψ (CyclicRing.evaluate φ (χ S)
        (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n)) * d S) =
        ε ∅ * ψ (CyclicRing.evaluate φ (χ ∅)
          (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n)) * d ∅ := by
      apply Finset.sum_eq_single ∅
      · intro S _ hS
        rw [evaluate_J_eq_zero φ (χ S)
          (hnonempty S (Finset.nonempty_iff_ne_empty.mpr hS))]
        simp
      · simp
    _ = (n : T) * d ∅ := by
      rw [hε, one_mul, htrivial, evaluate_J_trivial, map_natCast]

section SubsetSum

variable {I : Type uI} {G : Type uG} {R : Type uR} [Fintype I] [DecidableEq I]
    [Group G] [Fintype G] [CommRing R] [IsDomain R]

omit [DecidableEq I] in
/-- Only the empty subset survives. The coefficients `d S` are arbitrary;
in particular they may be inverses of specified units. -/
theorem subset_character_sum_mul [DecidableEq I]
    (χ : Finset I → G →* R) (ε d : Finset I → R)
    (hε : ε ∅ = 1) (htrivial : ∀ g : G, χ ∅ g = 1)
    (hnonempty : ∀ S : Finset I, S.Nonempty → ∃ g : G, χ S g ≠ 1) :
    (∑ S : Finset I, ε S * (∑ g : G, χ S g) * d S) =
      (Fintype.card G : R) * d ∅ := by
  classical
  calc
    (∑ S : Finset I, ε S * (∑ g : G, χ S g) * d S) =
        ε ∅ * (∑ g : G, χ ∅ g) * d ∅ := by
      apply Finset.sum_eq_single ∅
      · intro S _ hS
        rw [character_sum_eq_zero (χ S)
          (hnonempty S (Finset.nonempty_iff_ne_empty.mpr hS))]
        simp
      · simp
    _ = (Fintype.card G : R) * d ∅ := by
      rw [hε, one_mul, character_sum_trivial (χ ∅) htrivial]

/-- Ring-valued version of the quotient by each specified denominator unit. -/
theorem subset_character_sum_mul_unit_inv
    (χ : Finset I → G →* R) (ε : Finset I → R) (c : Finset I → Rˣ)
    (hε : ε ∅ = 1) (htrivial : ∀ g : G, χ ∅ g = 1)
    (hnonempty : ∀ S : Finset I, S.Nonempty → ∃ g : G, χ S g ≠ 1) :
    (∑ S : Finset I, ε S * (∑ g : G, χ S g) * ↑((c S)⁻¹)) =
      (Fintype.card G : R) * ↑((c ∅)⁻¹) :=
  subset_character_sum_mul χ ε (fun S => ↑((c S)⁻¹)) hε htrivial hnonempty

end SubsetSum

/-- In a field, the same collapse is expressed using division. No
nonvanishing assumption on nonempty-subset denominators is needed. -/
theorem subset_character_sum_div
    {I : Type uI} {G : Type uG} {K : Type uK} [Fintype I] [DecidableEq I] [Group G] [Fintype G] [Field K]
    (χ : Finset I → G →* K) (ε c : Finset I → K)
    (hε : ε ∅ = 1) (htrivial : ∀ g : G, χ ∅ g = 1)
    (hnonempty : ∀ S : Finset I, S.Nonempty → ∃ g : G, χ S g ≠ 1) :
    (∑ S : Finset I, ε S * (∑ g : G, χ S g) / c S) =
      (Fintype.card G : K) / c ∅ := by
  simpa only [div_eq_mul_inv] using
    subset_character_sum_mul χ ε (fun S => (c S)⁻¹) hε htrivial hnonempty

section Residue

variable {R : Type uR} {k : Type uk} [CommRing R] [CommRing k] [Nontrivial k] [CharP k 2]

/-- An odd cardinal times the inverse of a unit stays nonzero in any
nontrivial characteristic-two residue ring. -/
theorem residue_odd_mul_unit_inv_ne_zero (φ : R →+* k) {n : ℕ}
    (hn : Odd n) (c : Rˣ) : φ ((n : R) * ↑(c⁻¹)) ≠ 0 := by
  rw [map_mul, map_natCast,
    natCast_eq_one_of_odd_of_two_eq_zero hn (CharTwo.two_eq_zero (R := k)), one_mul]
  exact (IsUnit.map φ (c⁻¹).isUnit).ne_zero

/-- The weighted sum is nonzero after reduction when the finite group has
odd order and the empty-subset denominator is the specified unit. -/
theorem residue_subset_character_sum_ne_zero
    {I : Type uI} {G : Type uG} [Fintype I] [DecidableEq I] [Group G] [Fintype G] [IsDomain R]
    (φ : R →+* k) (χ : Finset I → G →* R)
    (ε : Finset I → R) (c : Finset I → Rˣ)
    (hε : ε ∅ = 1) (htrivial : ∀ g : G, χ ∅ g = 1)
    (hnonempty : ∀ S : Finset I, S.Nonempty → ∃ g : G, χ S g ≠ 1)
    (hodd : Odd (Fintype.card G)) :
    φ (∑ S : Finset I, ε S * (∑ g : G, χ S g) * ↑((c S)⁻¹)) ≠ 0 := by
  rw [subset_character_sum_mul_unit_inv χ ε c hε htrivial hnonempty]
  exact residue_odd_mul_unit_inv_ne_zero φ hodd (c ∅)

/-- The residue of the actual `J` expression is nonzero. Only the denominator
at the surviving empty subset needs to be a unit; the other coefficients are
arbitrary because their character evaluations vanish. -/
theorem residue_subset_evaluate_J_ne_zero
    {I : Type uI} {A : Type uA} [Fintype I] [DecidableEq I] [CommRing A] [IsDomain R]
    {n : ℕ} [NeZero n] (φ : A →+* R) (residue : R →+* k)
    (χ : Finset I → Multiplicative (ZMod n) →* R)
    (ε d : Finset I → R) (c₀ : Rˣ)
    (hε : ε ∅ = 1) (htrivial : χ ∅ = 1)
    (hnonempty : ∀ S : Finset I, S.Nonempty →
      ∃ g : Multiplicative (ZMod n), χ S g ≠ 1)
    (hd : d ∅ = ↑(c₀⁻¹)) (hodd : Odd n) :
    residue (∑ S : Finset I, ε S * CyclicRing.evaluate φ (χ S)
      (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n) * d S) ≠ 0 := by
  rw [subset_evaluate_J_mul φ χ ε d hε htrivial hnonempty, hd]
  exact residue_odd_mul_unit_inv_ne_zero residue hodd c₀

/-- Localization and residue reduction may follow the domain-valued
character-sum proof. Only the empty-subset coefficient is constrained. -/
theorem residue_subset_map_evaluate_J_ne_zero
    {I : Type uI} {A : Type uA} {B : Type uB} [Fintype I] [DecidableEq I] [CommRing A]
    [CommRing B] [IsDomain B] {n : ℕ} [NeZero n]
    (φ : A →+* B) (ψ : B →+* R) (residue : R →+* k)
    (χ : Finset I → Multiplicative (ZMod n) →* B)
    (ε d : Finset I → R) (c₀ : Rˣ)
    (hε : ε ∅ = 1) (htrivial : χ ∅ = 1)
    (hnonempty : ∀ S : Finset I, S.Nonempty →
      ∃ g : Multiplicative (ZMod n), χ S g ≠ 1)
    (hd : d ∅ = ↑(c₀⁻¹)) (hodd : Odd n) :
    residue (∑ S : Finset I, ε S * ψ (CyclicRing.evaluate φ (χ S)
      (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n)) * d S) ≠ 0 := by
  rw [subset_map_evaluate_J_mul φ ψ χ ε d hε htrivial hnonempty, hd]
  exact residue_odd_mul_unit_inv_ne_zero residue hodd c₀

end Residue

section ActualSubsetCharacters

open CyclotomicRings PrimeComponents PrimeCharacterEvaluations

/-- The witness is the actual CRT generator of a prime in the nonempty
subset. Its value is the corresponding primitive prime root, hence not one. -/
theorem actual_subsetCharacter_nontrivial (u : ℕ) (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (hS : S.Nonempty) :
    ∃ g : Multiplicative (ZMod (u ^ 2)), subsetCharacter u hu S g ≠ 1 := by
  obtain ⟨a, ha⟩ := subsetCharacter_nonempty u hu S hS
  exact ⟨Multiplicative.ofAdd a, ha⟩

variable (u : ℕ) [NeZero (u ^ 2)] (hu : 0 < u)

/-- The actual empty-subset evaluation of `J` is the order `u²`. -/
theorem actual_subsetEvaluation_J_empty :
    subsetEvaluation u hu ∅
      (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing) : CyclicRing.Elem GaussianRing (u ^ 2)) =
      (u ^ 2 : ℕ) := by
  simp only [subsetEvaluation, subsetCharacter_empty, evaluate_J_trivial]

/-- Every actual nonempty-subset evaluation of `J` vanishes. No
nontrivial-character hypothesis is an input to this theorem. -/
theorem actual_subsetEvaluation_J_nonempty
    (S : Finset (PrimeIndex u)) (hS : S.Nonempty) :
    subsetEvaluation u hu S
      (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing) : CyclicRing.Elem GaussianRing (u ^ 2)) = 0 := by
  exact evaluate_J_eq_zero (gaussianToB u).toRingHom (subsetCharacter u hu S)
    (actual_subsetCharacter_nontrivial u hu S hS)

/-- The actual prime-subset sum, with the literal parity signs. The target
may be a localization: its coefficients need not belong to the original `B`. -/
theorem actual_subset_J_sum
    {T : Type uT} [CommRing T] (ψ : B u →+* T)
    (d : Finset (PrimeIndex u) → T) :
    (∑ S : Finset (PrimeIndex u), (subsetSign S : T) *
      ψ (subsetEvaluation u hu S
        (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing) : CyclicRing.Elem GaussianRing (u ^ 2))) *
      d S) = ((u ^ 2 : ℕ) : T) * d ∅ := by
  exact subset_map_evaluate_J_mul (gaussianToB u).toRingHom ψ
    (subsetCharacter u hu) (fun S => (subsetSign S : T)) d (by simp)
    (subsetCharacter_empty u hu) (actual_subsetCharacter_nontrivial u hu)

/-- In a field the concrete sum is exactly `|P| / c_empty`, with
`|P| = u²`. Values at every nonempty subset were proved zero using its
actual primitive primary component. -/
theorem actual_subset_J_sum_div
    {K : Type uK} [Field K] (ψ : B u →+* K)
    (c : Finset (PrimeIndex u) → K) :
    (∑ S : Finset (PrimeIndex u), (subsetSign S : K) *
      ψ (subsetEvaluation u hu S
        (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing) : CyclicRing.Elem GaussianRing (u ^ 2))) /
      c S) = ((u ^ 2 : ℕ) : K) / c ∅ := by
  simpa only [div_eq_mul_inv] using actual_subset_J_sum u hu ψ (fun S => (c S)⁻¹)

/-- The concrete prime-character sum has nonzero characteristic-two residue.
Oddness comes from the actual `u`; only the surviving denominator must be a
unit. There is no assumption on reduced-character nontriviality. -/
theorem actual_subset_J_residue_ne_zero
    {T : Type uT} {k : Type uk} [CommRing T] [CommRing k] [Nontrivial k] [CharP k 2]
    (ψ : B u →+* T) (residue : T →+* k)
    (d : Finset (PrimeIndex u) → T) (c₀ : Tˣ)
    (hd : d ∅ = ↑(c₀⁻¹)) (hodd : Odd u) :
    residue (∑ S : Finset (PrimeIndex u), (subsetSign S : T) *
      ψ (subsetEvaluation u hu S
        (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing) : CyclicRing.Elem GaussianRing (u ^ 2))) *
      d S) ≠ 0 := by
  rw [actual_subset_J_sum u hu ψ d, hd]
  exact residue_odd_mul_unit_inv_ne_zero residue hodd.pow c₀

end ActualSubsetCharacters

end CirculantHadamard.BinaryCharacterSum

end OAI
