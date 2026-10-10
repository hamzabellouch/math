import OAI.Algebra.AffineCancellation.Model

namespace OAI

noncomputable section

/-! Orbit polynomials and exponentiation of locally nilpotent derivations. -/
namespace ComplexCancellation.LND
open Polynomial

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

/-- Local nilpotence, allowing the bound zero for the zero element. -/
def LocallyNilpotent (D : Derivation k R R) : Prop :=
  ∀ r : R, ∃ n : ℕ, (D : R → R)^[n] r = 0

lemma iterate_zero (D : Derivation k R R) (n : ℕ) : (D : R → R)^[n] 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_zero]

lemma iterate_eq_zero_of_le (D : Derivation k R R) {r : R} {n m : ℕ}
    (h : (D : R → R)^[n] r = 0) (hnm : n ≤ m) : (D : R → R)^[m] r = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [Nat.add_comm, Function.iterate_add_apply, h, iterate_zero]

lemma iterate_add (D : Derivation k R R) (n : ℕ) (r s : R) :
    (D : R → R)^[n] (r + s) = (D : R → R)^[n] r + (D : R → R)^[n] s := by
  simpa only [Module.End.pow_apply, Derivation.coeFn_coe] using
    (D.toLinearMap ^ n).map_add r s

lemma iterate_smul (D : Derivation k R R) (n : ℕ) (c : k) (r : R) :
    (D : R → R)^[n] (c • r) = c • (D : R → R)^[n] r := by
  simpa only [Module.End.pow_apply, Derivation.coeFn_coe] using
    (D.toLinearMap ^ n).map_smul c r

lemma iterate_leibniz (D : Derivation k R R) (n : ℕ) (r s : R) :
    (D : R → R)^[n] (r * s) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        n.choose ij.1 • ((D : R → R)^[ij.1] r * (D : R → R)^[ij.2] s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_sum,
      Finset.sum_antidiagonal_choose_succ_nsmul
        (fun i j => (D : R → R)^[i] r * (D : R → R)^[j] s) n]
    simp only [map_nsmul, Derivation.leibniz, smul_eq_mul, nsmul_add,
      Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro ij hij
      rw [Function.iterate_succ_apply']
    · apply Finset.sum_congr rfl
      rintro ⟨i,j⟩ hij
      have hij' : i + j = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      have hchoose : n.choose i = n.choose j := by
        exact Nat.choose_symm_of_eq_add hij'.symm
      rw [Function.iterate_succ_apply', hchoose, mul_comm]

lemma orbit_support_finite (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) :
    (Function.support (fun n : ℕ => ((n.factorial : k)⁻¹) • (D : R → R)^[n] r)).Finite := by
  obtain ⟨m, hm⟩ := hD r
  apply (Set.finite_Iio m).subset
  intro n hn
  change n < m
  by_contra h
  have he := iterate_eq_zero_of_le D hm (by omega : m ≤ n)
  exact hn (by simp [he])

noncomputable def orbit (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) : R[X] :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff
    (Finsupp.ofSupportFinite (fun n : ℕ => ((n.factorial : k)⁻¹) • (D : R → R)^[n] r)
      (orbit_support_finite D hD r)))

@[simp] lemma orbit_coeff (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) (n : ℕ) :
    (orbit D hD r).coeff n = ((n.factorial : k)⁻¹) • (D : R → R)^[n] r := by
  rfl

@[simp] lemma orbit_coeff_zero (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) :
    (orbit D hD r).coeff 0 = r := by simp

@[simp] lemma orbit_coeff_one (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) :
    (orbit D hD r).coeff 1 = D r := by simp

lemma inv_factorial_choose [CharZero k] {n i j : ℕ} (h : i + j = n) :
    ((n.factorial : k)⁻¹) * (n.choose i : k) =
      ((i.factorial : k)⁻¹) * ((j.factorial : k)⁻¹) := by
  have hi : i ≤ n := by omega
  rw [Nat.cast_choose k hi, show n - i = j by omega]
  have hn : (n.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp

lemma orbit_mul [CharZero k] (D : Derivation k R R) (hD : LocallyNilpotent D) (r s : R) :
    orbit D hD (r * s) = orbit D hD r * orbit D hD s := by
  ext n
  rw [orbit_coeff, Polynomial.coeff_mul, iterate_leibniz, Finset.smul_sum]
  apply Finset.sum_congr rfl
  rintro ⟨i,j⟩ hij
  rw [orbit_coeff, orbit_coeff]
  have hij' : i + j = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_factorial_choose hij',
    smul_mul_smul_comm]

lemma orbit_add (D : Derivation k R R) (hD : LocallyNilpotent D) (r s : R) :
    orbit D hD (r + s) = orbit D hD r + orbit D hD s := by
  ext n
  simp [smul_add]

lemma orbit_algebraMap (D : Derivation k R R) (hD : LocallyNilpotent D) (c : k) :
    orbit D hD (algebraMap k R c) = C (algebraMap k R c) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp [Function.iterate_succ_apply, D.map_algebraMap]

noncomputable def orbitHom [CharZero k] (D : Derivation k R R) (hD : LocallyNilpotent D) : R →ₐ[k] R[X] where
  toFun := orbit D hD
  map_zero' := by ext; simp
  map_one' := by simpa using orbit_algebraMap D hD 1
  map_add' := orbit_add D hD
  map_mul' := orbit_mul D hD
  commutes' := orbit_algebraMap D hD

lemma orbit_injective (D : Derivation k R R) (hD : LocallyNilpotent D) :
    Function.Injective (orbit D hD) := by
  intro r s hes
  simpa using congrArg (fun p : R[X] => p.coeff 0) hes

lemma orbit_degree_le_one (D : Derivation k R R) (hD : LocallyNilpotent D) {r : R}
    (hr : D (D r) = 0) : (orbit D hD r).natDegree ≤ 1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [orbit_coeff, iterate_eq_zero_of_le D (n := 2) hr (by omega), smul_zero]

lemma orbit_constant_iff (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) :
    orbit D hD r = C r ↔ D r = 0 := by
  constructor
  · intro h
    simpa using congrArg (fun p : R[X] => p.coeff 1) h
  · intro h
    ext n
    cases n with
    | zero => simp
    | succ n => simp [Function.iterate_succ_apply, h]

end ComplexCancellation.LND

end

end OAI
