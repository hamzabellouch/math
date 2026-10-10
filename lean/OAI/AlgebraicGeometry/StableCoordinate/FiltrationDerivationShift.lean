import OAI.AlgebraicGeometry.StableCoordinate.FiltrationSeparation
import OAI.AlgebraicGeometry.StableCoordinate.IntegerFiltrationDegree
import Mathlib.RingTheory.Derivation.Basic

namespace OAI

/-!
# Bounded derivation shifts for the integer source filtration

This proves the generator-bound step in equation `gr:shift` of the source.
It uses the actual five-variable integer filtration, including negative
indices.  Bounds on derivatives of the five generators imply one common
bound on the derivative of every filtration piece.
-/

namespace StableCoordinate
namespace Filtration

open MvPolynomial

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

/-- The image of each monomial lies in its assigned integer filtration layer. -/
theorem image_monomial_mem (φ : MvPolynomial (Fin 5) K →ₐ[K] A)
    (s : Fin 5 →₀ ℕ) (c : K) :
    φ (monomial s c) ∈ imagePiece φ (monomialWeight s) :=
  ⟨monomial s c, monomial_mem_piece K le_rfl c, rfl⟩

/-- The weight of a pure power is its exponent times the variable weight. -/
theorem monomialWeight_single (i : Fin 5) (n : ℕ) :
    monomialWeight (Finsupp.single i n) =
      n • monomialWeight (Finsupp.single i 1) := by
  fin_cases i <;> simp [monomialWeight]

/-- The product rule propagates a common filtration shift through multiplication. -/
theorem derivation_mul_mem_imagePiece
    (φ : MvPolynomial (Fin 5) K →ₐ[K] A) (D : Derivation K A A)
    {a b : A} {d e m : ℤ}
    (ha : a ∈ imagePiece φ d) (hb : b ∈ imagePiece φ e)
    (hDa : D a ∈ imagePiece φ (d + m))
    (hDb : D b ∈ imagePiece φ (e + m)) :
    D (a * b) ∈ imagePiece φ (d + e + m) := by
  rw [D.leibniz, smul_eq_mul, smul_eq_mul]
  apply (imagePiece φ _).add_mem
  · simpa only [add_assoc] using mul_mem_imagePiece φ ha hDb
  · convert mul_mem_imagePiece φ hb hDa using 1
    congr 1
    omega

/-- The product rule propagates a common filtration shift through every power. -/
theorem derivation_pow_mem_imagePiece
    (φ : MvPolynomial (Fin 5) K →ₐ[K] A) (D : Derivation K A A)
    {a : A} {d m : ℤ}
    (ha : a ∈ imagePiece φ d) (hDa : D a ∈ imagePiece φ (d + m))
    (n : ℕ) : D (a ^ n) ∈ imagePiece φ (n • d + m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    convert derivation_mul_mem_imagePiece φ D (SetLike.pow_mem_graded n ha) ha ih hDa using 1
    congr 1
    simp only [succ_nsmul]

/-- A bound on generator derivatives gives the exact monomial-weight bound. -/
theorem derivation_monomial_mem_imagePiece
    (φ : MvPolynomial (Fin 5) K →ₐ[K] A) (D : Derivation K A A) (m : ℤ)
    (hD : ∀ i : Fin 5, D (φ (X i)) ∈
      imagePiece φ (monomialWeight (Finsupp.single i 1) + m))
    (s : Fin 5 →₀ ℕ) (c : K) :
    D (φ (monomial s c)) ∈ imagePiece φ (monomialWeight s + m) := by
  have hone : ∀ s : Fin 5 →₀ ℕ,
      D (φ (monomial s 1)) ∈ imagePiece φ (monomialWeight s + m) := by
    intro s
    induction s using Finsupp.induction with
    | zero => simp
    | single_add i n s hni hn ih =>
      rw [add_comm (Finsupp.single i n), monomial_add_single, map_mul]
      have hpow := derivation_pow_mem_imagePiece φ D
        (image_monomial_mem φ (Finsupp.single i 1) 1) (hD i) n
      change D (φ (X i) ^ n) ∈ _ at hpow
      have hmul := derivation_mul_mem_imagePiece φ D
        (image_monomial_mem φ s 1)
        (SetLike.pow_mem_graded n (image_monomial_mem φ (Finsupp.single i 1) 1))
        ih hpow
      rw [map_add, monomialWeight_single i n]
      simpa only [map_pow, MvPolynomial.X] using hmul
  have hsmul := (imagePiece φ _).smul_mem c (hone s)
  have hmono : monomial s c = c • (monomial s 1 : MvPolynomial (Fin 5) K) := by
    simp only [smul_monomial, smul_eq_mul, mul_one]
  rw [hmono, map_smul, Derivation.map_smul]
  exact hsmul

/-- Generator bounds extend to every element of a source filtration piece. -/
theorem derivation_source_piece_mem_imagePiece
    (φ : MvPolynomial (Fin 5) K →ₐ[K] A) (D : Derivation K A A) (m : ℤ)
    (hD : ∀ i : Fin 5, D (φ (X i)) ∈
      imagePiece φ (monomialWeight (Finsupp.single i 1) + m))
    {q : MvPolynomial (Fin 5) K} {d : ℤ} (hq : q ∈ piece K d) :
    D (φ q) ∈ imagePiece φ (d + m) := by
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨s, hs, rfl⟩ := hq
    have hsm : monomialWeight s + m ≤ d + m := by omega
    exact imagePiece_mono φ hsm
      (derivation_monomial_mem_imagePiece φ D m hD s 1)
  | zero => simp
  | add q r hq hr ihq ihr =>
    simpa only [map_add] using (imagePiece φ _).add_mem ihq ihr
  | smul c q hq ihq =>
    simpa only [map_smul, Derivation.map_smul] using (imagePiece φ _).smul_mem c ihq

/-- The source's bounded-shift assertion, for every integer filtration degree. -/
theorem derivation_imagePiece_le
    (φ : MvPolynomial (Fin 5) K →ₐ[K] A) (D : Derivation K A A) (m : ℤ)
    (hD : ∀ i : Fin 5, D (φ (X i)) ∈
      imagePiece φ (monomialWeight (Finsupp.single i 1) + m))
    (d : ℤ) :
    imagePiece φ d ≤ (imagePiece φ (d + m)).comap D.toLinearMap := by
  rintro a ⟨q, hq, rfl⟩
  exact derivation_source_piece_mem_imagePiece φ D m hD hq

/-- A derivation vanishing on all presentation generators is zero. -/
theorem derivation_eq_zero_of_generator_values
    (φ : MvPolynomial (Fin 5) K →ₐ[K] A) (hφ : Function.Surjective φ)
    (D : Derivation K A A) (hD : ∀ i : Fin 5, D (φ (X i)) = 0) : D = 0 := by
  ext a
  obtain ⟨q, rfl⟩ := hφ a
  change D (φ q) = 0
  induction q using MvPolynomial.induction_on with
  | C c => simp
  | add q r ihq ihr => simp [ihq, ihr]
  | mul_X q i ihq => simp [D.leibniz, ihq, hD]

/-- A nonzero derivation has a nonzero value on a presentation generator. -/
theorem exists_ne_zero_generator_value
    (φ : MvPolynomial (Fin 5) K →ₐ[K] A) (hφ : Function.Surjective φ)
    (D : Derivation K A A) (hD : D ≠ 0) :
    ∃ i : Fin 5, D (φ (X i)) ≠ 0 := by
  by_contra h
  push Not at h
  exact hD (derivation_eq_zero_of_generator_values φ hφ D h)

/-- Exhaustiveness and the finite set of presentation generators supply a
uniform integer shift for every derivation. -/
theorem exists_derivation_imagePiece_shift
    (φ : MvPolynomial (Fin 5) K →ₐ[K] A) (hφ : Function.Surjective φ)
    (D : Derivation K A A) :
    ∃ m : ℤ, ∀ d : ℤ,
      imagePiece φ d ≤ (imagePiece φ (d + m)).comap D.toLinearMap := by
  classical
  choose degree hdegree using fun i : Fin 5 =>
    exists_mem_imagePiece φ hφ (D (φ (X i)))
  obtain ⟨i, _, himax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin 5 => degree i - monomialWeight (Finsupp.single i 1))
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin 5)).Nonempty)
  refine ⟨degree i - monomialWeight (Finsupp.single i 1), ?_⟩
  apply derivation_imagePiece_le φ D
  intro j
  apply imagePiece_mono φ _ (hdegree j)
  have hj := himax j (Finset.mem_univ j)
  omega

/-- Separation makes the maximal generator shift sharp.  Some nonzero
generator image lands in degree `weight + m`, but not the preceding layer.
This is exactly the nonvanishing criterion for the source's leading derivation. -/
theorem exists_attained_derivation_imagePiece_shift
    (φ : MvPolynomial (Fin 5) K →ₐ[K] A) (hφ : Function.Surjective φ)
    (hsep : (⨅ d : ℤ, imagePiece φ d) = ⊥)
    (D : Derivation K A A) (hD : D ≠ 0) :
    ∃ (m : ℤ) (i : Fin 5),
      D (φ (X i)) ≠ 0 ∧
      D (φ (X i)) ∈ imagePiece φ (monomialWeight (Finsupp.single i 1) + m) ∧
      D (φ (X i)) ∉ imagePiece φ (monomialWeight (Finsupp.single i 1) + m - 1) ∧
      ∀ d : ℤ, imagePiece φ d ≤ (imagePiece φ (d + m)).comap D.toLinearMap := by
  classical
  let F : ℤ → Set A := fun d => (imagePiece φ d : Set A)
  have hmono : Monotone F := fun _ _ h => imagePiece_mono φ h
  have hext : ∀ a : A, ∃ d : ℤ, a ∈ F d := exists_mem_imagePiece φ hφ
  have hseparated : ∀ a : A, (∀ d : ℤ, a ∈ F d) → a = 0 :=
    IntegerFiltration.separated_of_iInf_eq_bot (imagePiece φ) hsep
  let deg : Fin 5 → ℤ := fun i => IntegerFiltration.degree F (D (φ (X i)))
  let S : Finset (Fin 5) := Finset.univ.filter fun i => D (φ (X i)) ≠ 0
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := exists_ne_zero_generator_value φ hφ D hD
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨i, hi, himax⟩ := Finset.exists_max_image S
    (fun i : Fin 5 => deg i - monomialWeight (Finsupp.single i 1)) hS
  have hiD : D (φ (X i)) ≠ 0 := (Finset.mem_filter.mp hi).2
  let m : ℤ := deg i - monomialWeight (Finsupp.single i 1)
  have him : monomialWeight (Finsupp.single i 1) + m = deg i := by
    dsimp [m]
    omega
  have hbounded : ∀ j : Fin 5, D (φ (X j)) ∈
      imagePiece φ (monomialWeight (Finsupp.single j 1) + m) := by
    intro j
    by_cases hjD : D (φ (X j)) = 0
    · rw [hjD]
      exact (imagePiece φ _).zero_mem
    · have hj : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjD⟩
      have hmax := himax j hj
      have hdeg := (IntegerFiltration.degree_spec F hmono hext hseparated hjD).1
      apply imagePiece_mono φ _ hdeg
      change deg j ≤ monomialWeight (Finsupp.single j 1) +
        (deg i - monomialWeight (Finsupp.single i 1))
      omega
  refine ⟨m, i, hiD, hbounded i, ?_, derivation_imagePiece_le φ D m hbounded⟩
  rw [him]
  exact IntegerFiltration.not_mem_degree_sub_one F hmono hext hseparated hiD

/-- For the attained maximal shift, both the source generator and its derivative
have nonzero initial classes.  No separate exact-degree theorem for the source
generators is needed to obtain this conclusion. -/
theorem exists_attained_derivation_shift_with_initial_generator
    (φ : MvPolynomial (Fin 5) K →ₐ[K] A) (hφ : Function.Surjective φ)
    (hsep : (⨅ d : ℤ, imagePiece φ d) = ⊥)
    (D : Derivation K A A) (hD : D ≠ 0) :
    ∃ (m : ℤ) (i : Fin 5),
      φ (X i) ∈ imagePiece φ (monomialWeight (Finsupp.single i 1)) ∧
      φ (X i) ∉ imagePiece φ (monomialWeight (Finsupp.single i 1) - 1) ∧
      D (φ (X i)) ∈ imagePiece φ (monomialWeight (Finsupp.single i 1) + m) ∧
      D (φ (X i)) ∉ imagePiece φ (monomialWeight (Finsupp.single i 1) + m - 1) ∧
      ∀ d : ℤ, imagePiece φ d ≤ (imagePiece φ (d + m)).comap D.toLinearMap := by
  obtain ⟨m, i, _, hDi, hDiprev, hshift⟩ :=
    exists_attained_derivation_imagePiece_shift φ hφ hsep D hD
  refine ⟨m, i, image_monomial_mem φ (Finsupp.single i 1) 1, ?_, hDi, hDiprev, hshift⟩
  intro hiprev
  apply hDiprev
  have hm := hshift (monomialWeight (Finsupp.single i 1) - 1) hiprev
  change D (φ (X i)) ∈ imagePiece φ
    (monomialWeight (Finsupp.single i 1) - 1 + m) at hm
  convert hm using 1
  congr 1
  omega

/-- Specialization of the attained-shift theorem to the noetherian-domain
source setting, where the image of the negative-weight variable is a nonunit. -/
theorem exists_attained_derivation_shift_of_nonunit
    [IsNoetherianRing A] [IsDomain A]
    (φ : MvPolynomial (Fin 5) K →ₐ[K] A) (hφ : Function.Surjective φ)
    (hp : ¬ IsUnit (φ (X 0))) (D : Derivation K A A) (hD : D ≠ 0) :
    ∃ (m : ℤ) (i : Fin 5),
      φ (X i) ∈ imagePiece φ (monomialWeight (Finsupp.single i 1)) ∧
      φ (X i) ∉ imagePiece φ (monomialWeight (Finsupp.single i 1) - 1) ∧
      D (φ (X i)) ∈ imagePiece φ (monomialWeight (Finsupp.single i 1) + m) ∧
      D (φ (X i)) ∉ imagePiece φ (monomialWeight (Finsupp.single i 1) + m - 1) ∧
      ∀ d : ℤ, imagePiece φ d ≤ (imagePiece φ (d + m)).comap D.toLinearMap :=
  exists_attained_derivation_shift_with_initial_generator φ hφ
    (iInf_imagePiece_eq_bot φ hp) D hD

end Filtration
end StableCoordinate

end OAI
