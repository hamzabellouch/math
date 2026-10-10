import Mathlib
import OAI.GroupTheory.FiniteType.RelativeChainsEmptyProjectionQuasiIso

namespace OAI

noncomputable section
namespace FiniteIdempotentDiagrams
section

variable {R T : Type*} [NonUnitalRing R] [AddCommGroup T]

def OrthogonalAdditive (z : R → T) : Prop :=
  ∀ E P, E * E = E → P * P = P → E * P = 0 → P * E = 0 →
    z (E + P) = z E + z P

variable {K m : Type*} [CommRing K] [Fintype m]

open Matrix
open scoped Matrix

abbrev rankOne (u l : m → K) : Matrix m m K := vecMulVec u l

lemma rankOne_idem (u l : m → K) (h : l ⬝ᵥ u = 1) :
    rankOne u l * rankOne u l = rankOne u l := by
  simp only [rankOne, vecMulVec_mul_vecMulVec, h, one_smul]

lemma rankOne_orthogonal (u l v a : m → K) (h : l ⬝ᵥ v = 0) :
    rankOne u l * rankOne v a = 0 := by
  simp only [rankOne, vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero]

lemma rankOne_difference (z : Matrix m m K → T) (hz : OrthogonalAdditive z)
    (u v l a : m → K) (hlu : l ⬝ᵥ u = 1) (hlv : l ⬝ᵥ v = 0)
    (hau : a ⬝ᵥ u = 0) (hav : a ⬝ᵥ v = 1) :
    z (rankOne (u + v) l) - z (rankOne u l) =
      z (rankOne v a) - z (rankOne v (a - l)) := by
  have hl : l ⬝ᵥ (u + v) = 1 := by simp [dotProduct_add, hlu, hlv]
  have ha : (a - l) ⬝ᵥ v = 1 := by simp [sub_dotProduct, hav, hlv]
  have hcross : (a - l) ⬝ᵥ (u + v) = 0 := by
    simp [sub_dotProduct, dotProduct_add, hau, hav, hlu, hlv]
  have h₁ := hz (rankOne u l) (rankOne v a)
    (rankOne_idem _ _ hlu) (rankOne_idem _ _ hav)
    (rankOne_orthogonal _ _ _ _ hlv) (rankOne_orthogonal _ _ _ _ hau)
  have h₂ := hz (rankOne (u + v) l) (rankOne v (a - l))
    (rankOne_idem _ _ hl) (rankOne_idem _ _ ha)
    (rankOne_orthogonal _ _ _ _ hlv) (rankOne_orthogonal _ _ _ _ hcross)
  have heq : rankOne u l + rankOne v a =
      rankOne (u + v) l + rankOne v (a - l) := by
    ext i j
    simp only [rankOne, vecMulVec_apply, Matrix.add_apply, Pi.add_apply, Pi.sub_apply]
    ring
  have he : z (rankOne u l) + z (rankOne v a) =
      z (rankOne (u + v) l) + z (rankOne v (a - l)) := by
    rw [← h₁, ← h₂, heq]
  calc z (rankOne (u + v) l) - z (rankOne u l) =
      (z (rankOne (u + v) l) + z (rankOne v (a - l))) -
      (z (rankOne u l) + z (rankOne v (a - l))) := by abel
    _ = (z (rankOne u l) + z (rankOne v a)) -
      (z (rankOne u l) + z (rankOne v (a - l))) := by rw [← he]
    _ = z (rankOne v a) - z (rankOne v (a - l)) := by abel

lemma variation_constant (z : Matrix m m K → T) (hz : OrthogonalAdditive z)
    (u v w l a b : m → K)
    (hlu : l ⬝ᵥ u = 1) (hlv : l ⬝ᵥ v = 0) (hlw : l ⬝ᵥ w = 0)
    (hau : a ⬝ᵥ u = 0) (hav : a ⬝ᵥ v = 1) (haw : a ⬝ᵥ w = 0)
    (hbu : b ⬝ᵥ u = 0) (hbv : b ⬝ᵥ v = 0) (hbw : b ⬝ᵥ w = 1)
    (k : K) :
    z (rankOne ((u + k • v) + v) l) - z (rankOne (u + k • v) l) =
      z (rankOne ((u + w) + v) l) - z (rankOne (u + w) l) := by
  let a' := a - k • l + k • b
  have ha'v : a' ⬝ᵥ v = 1 := by
    simp [a', add_dotProduct, sub_dotProduct, smul_dotProduct, hav, hlv, hbv]
  have ha'u : a' ⬝ᵥ (u + k • v) = 0 := by
    simp [a', add_dotProduct, sub_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, hlu, hlv, hau, hav, hbu, hbv]
  have ha'w : a' ⬝ᵥ (u + w) = 0 := by
    simp [a', add_dotProduct, sub_dotProduct, dotProduct_add,
      smul_dotProduct, hlu, hlw, hau, haw, hbu, hbw]
  have h₁ := rankOne_difference z hz (u + k • v) v l a'
    (by simp [dotProduct_add, dotProduct_smul, hlu, hlv]) hlv ha'u ha'v
  have h₂ := rankOne_difference z hz (u + w) v l a'
    (by simp [dotProduct_add, hlu, hlw]) hlv ha'w ha'v
  exact h₁.trans h₂.symm

lemma nsmul_variation (p : ℕ) [CharP K p]
    (z : Matrix m m K → T) (hz : OrthogonalAdditive z)
    (u v w l a b : m → K)
    (hlu : l ⬝ᵥ u = 1) (hlv : l ⬝ᵥ v = 0) (hlw : l ⬝ᵥ w = 0)
    (hau : a ⬝ᵥ u = 0) (hav : a ⬝ᵥ v = 1) (haw : a ⬝ᵥ w = 0)
    (hbu : b ⬝ᵥ u = 0) (hbv : b ⬝ᵥ v = 0) (hbw : b ⬝ᵥ w = 1) :
    p • z (rankOne (u + v) l) = p • z (rankOne u l) := by
  let δ := z (rankOne ((u + w) + v) l) - z (rankOne (u + w) l)
  let c (n : ℕ) := z (rankOne (u + (n : K) • v) l)
  have hstep (n : ℕ) : c (n + 1) - c n = δ := by
    have h := variation_constant z hz u v w l a b
      hlu hlv hlw hau hav haw hbu hbv hbw (n : K)
    simpa [c, δ, Nat.cast_add, add_smul, add_assoc] using h
  have hc (n : ℕ) : c n = c 0 + n • δ := by
    induction n with
    | zero => simp
    | succ n ih =>
      have h := hstep n
      rw [sub_eq_iff_eq_add] at h
      rw [h, ih, succ_nsmul]
      abel
  have hclose : c p = c 0 := by simp [c]
  have hzero : p • δ = 0 := by
    have h := hc p
    rw [hclose] at h
    exact (add_left_cancel (h.symm.trans (add_zero (c 0)).symm))
  have h₀ := hstep 0
  simp only [c, Nat.cast_zero, zero_smul, add_zero, zero_add,
    Nat.cast_one, one_smul] at h₀
  apply sub_eq_zero.mp
  rw [← nsmul_sub, h₀]
  exact hzero

lemma OrthogonalAdditive.transpose (z : Matrix m m K → T) (hz : OrthogonalAdditive z) :
    OrthogonalAdditive (fun M : Matrix m m K => z Mᵀ) := by
  intro E P hE hP hEP hPE
  change z (E + P)ᵀ = z Eᵀ + z Pᵀ
  rw [transpose_add]
  apply hz
  · simpa only [transpose_mul] using congrArg Matrix.transpose hE
  · simpa only [transpose_mul] using congrArg Matrix.transpose hP
  · simpa only [transpose_mul, transpose_zero] using congrArg Matrix.transpose hPE
  · simpa only [transpose_mul, transpose_zero] using congrArg Matrix.transpose hEP

variable [DecidableEq m]

abbrev basisVector (i : m) : m → K := Pi.single i 1
abbrev diagonalUnit (i : m) : Matrix m m K :=
  rankOne (basisVector i) (basisVector i)

@[simp] lemma basisVector_pair (i j : m) :
    (basisVector i : m → K) ⬝ᵥ basisVector j = if i = j then 1 else 0 := by
  simp only [basisVector, single_dotProduct, one_mul, Pi.single_apply]

@[simp] lemma diagonalUnit_idem (i : m) :
    (diagonalUnit i : Matrix m m K) * diagonalUnit i = diagonalUnit i :=
  rankOne_idem _ _ (by simp)

lemma diagonalUnit_orthogonal {i j : m} (h : i ≠ j) :
    (diagonalUnit i : Matrix m m K) * diagonalUnit j = 0 :=
  rankOne_orthogonal _ _ _ _ (by simp [h])

lemma nsmul_diagonal_eq (p : ℕ) [CharP K p]
    (z : Matrix m m K → T) (hz : OrthogonalAdditive z)
    (i j k : m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    p • z (diagonalUnit i) = p • z (diagonalUnit j) := by
  have hji := hij.symm
  have hki := hik.symm
  have hkj := hjk.symm
  have h₁ := nsmul_variation p (fun M : Matrix m m K => z Mᵀ) (OrthogonalAdditive.transpose z hz)
    (basisVector i) (basisVector j) (basisVector k)
    (basisVector i) (basisVector j) (basisVector k)
    (by simp) (by simp [hij]) (by simp [hik])
    (by simp [hji]) (by simp) (by simp [hjk])
    (by simp [hki]) (by simp [hkj]) (by simp)
  simp only [rankOne, transpose_vecMulVec] at h₁
  have h₂ := nsmul_variation p z hz
    (basisVector i) (basisVector j - basisVector i) (basisVector k)
    (basisVector i + basisVector j) (basisVector j) (basisVector k)
    (by simp [hji])
    (by simp [dotProduct_sub, hij, hji])
    (by simp [hik, hjk])
    (by simp [hji]) (by simp [dotProduct_sub, hji]) (by simp [hjk])
    (by simp [hki]) (by simp [dotProduct_sub, hkj, hki]) (by simp)
  have hv : (basisVector i : m → K) + (basisVector j - basisVector i) =
      basisVector j := by abel
  rw [hv] at h₂
  have h₃ := nsmul_variation p (fun M : Matrix m m K => z Mᵀ) (OrthogonalAdditive.transpose z hz)
    (basisVector j) (basisVector i) (basisVector k)
    (basisVector j) (basisVector i) (basisVector k)
    (by simp) (by simp [hji]) (by simp [hjk])
    (by simp [hij]) (by simp) (by simp [hik])
    (by simp [hkj]) (by simp [hki]) (by simp)
  simp only [rankOne, transpose_vecMulVec, add_comm (basisVector j) (basisVector i)] at h₃
  exact h₁.symm.trans (h₂.symm.trans h₃)

end

section

open Matrix
open scoped Matrix

variable {K R T : Type*} [CommRing K] [Ring R] [AddCommGroup T]

abbrev Mat3 (K : Type*) := Matrix (Fin 3) (Fin 3) K

lemma orthogonal_sum_idem {A B : R} (hA : A * A = A) (hB : B * B = B)
    (hAB : A * B = 0) (hBA : B * A = 0) : (A + B) * (A + B) = A + B := by
  simp [add_mul, mul_add, hA, hB, hAB, hBA]

lemma three_diagonal_sum :
    (diagonalUnit 0 + diagonalUnit 1 + diagonalUnit 2 : Mat3 K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalUnit, rankOne, basisVector, vecMulVec_apply]

lemma orthogonalAdditive_one (z : Mat3 K → T) (hz : OrthogonalAdditive z) :
    z 1 = z (diagonalUnit 0) + z (diagonalUnit 1) + z (diagonalUnit 2) := by
  have h01 : (diagonalUnit 0 : Mat3 K) * diagonalUnit 1 = 0 :=
    diagonalUnit_orthogonal (by decide)
  have h10 : (diagonalUnit 1 : Mat3 K) * diagonalUnit 0 = 0 :=
    diagonalUnit_orthogonal (by decide)
  have h02 : (diagonalUnit 0 : Mat3 K) * diagonalUnit 2 = 0 :=
    diagonalUnit_orthogonal (by decide)
  have h20 : (diagonalUnit 2 : Mat3 K) * diagonalUnit 0 = 0 :=
    diagonalUnit_orthogonal (by decide)
  have h12 : (diagonalUnit 1 : Mat3 K) * diagonalUnit 2 = 0 :=
    diagonalUnit_orthogonal (by decide)
  have h21 : (diagonalUnit 2 : Mat3 K) * diagonalUnit 1 = 0 :=
    diagonalUnit_orthogonal (by decide)
  have h₁ := hz (diagonalUnit 0) (diagonalUnit 1)
    (diagonalUnit_idem _) (diagonalUnit_idem _) h01 h10
  have h₂ := hz (diagonalUnit 0 + diagonalUnit 1) (diagonalUnit 2)
    (orthogonal_sum_idem (diagonalUnit_idem _) (diagonalUnit_idem _) h01 h10)
    (diagonalUnit_idem _)
    (by simp only [add_mul, h02, h12, add_zero])
    (by simp only [mul_add, h20, h21, add_zero])
  rw [three_diagonal_sum] at h₂
  exact h₂.trans (congrArg (· + z (diagonalUnit 2)) h₁)

structure ThreeCopies (K R : Type*) [CommRing K] [Ring R] where
  copy : Fin 3 → (Mat3 K →ₙ+* R)
  first_one : copy 0 1 = 1
  common_second : ∀ i, copy i (diagonalUnit 1) = copy 0 (diagonalUnit 1)
  common_third : ∀ i, copy i (diagonalUnit 2) = copy 0 (diagonalUnit 2)
  partition : copy 0 (diagonalUnit 0) =
    copy 1 (diagonalUnit 0) + copy 2 (diagonalUnit 0)
  partition_orthogonal : copy 1 (diagonalUnit 0) * copy 2 (diagonalUnit 0) = 0
  partition_orthogonal' : copy 2 (diagonalUnit 0) * copy 1 (diagonalUnit 0) = 0

def ThreeCopies.system (C : ThreeCopies K R) : Set R :=
  {x | x = 1 ∨ ∃ (i : Fin 3) (M : Mat3 K), M * M = M ∧ C.copy i M = x}

lemma ThreeCopies.mem_system (C : ThreeCopies K R) (i : Fin 3) (M : Mat3 K)
    (hM : M * M = M) : C.copy i M ∈ C.system := Or.inr ⟨i, M, hM, rfl⟩

lemma ThreeCopies.diagonal_mem (C : ThreeCopies K R) (i j : Fin 3) :
    C.copy i (diagonalUnit j) ∈ C.system := C.mem_system i _ (diagonalUnit_idem j)

lemma ThreeCopies.system_finite [Finite K] (C : ThreeCopies K R) : C.system.Finite := by
  apply ((Set.finite_range fun x : Fin 3 × Mat3 K => C.copy x.1 x.2).insert 1).subset
  rintro x (rfl | ⟨i, M, _, rfl⟩)
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨(i, M), rfl⟩

def OrthogonalAdditiveOn (S : Set R) (z : R → T) : Prop :=
  ∀ E P, E ∈ S → P ∈ S → E + P ∈ S → E * P = 0 → P * E = 0 →
    z (E + P) = z E + z P

lemma ThreeCopies.additive_copy (C : ThreeCopies K R) (z : R → T)
    (hz : OrthogonalAdditiveOn C.system z) (i : Fin 3) :
    OrthogonalAdditive (fun M => z (C.copy i M)) := by
  intro E P hE hP hEP hPE
  have hsum := C.mem_system i (E + P) (orthogonal_sum_idem hE hP hEP hPE)
  rw [map_add] at hsum
  have h := hz (C.copy i E) (C.copy i P) (C.mem_system i E hE)
    (C.mem_system i P hP) hsum
    (by rw [← map_mul, hEP, map_zero]) (by rw [← map_mul, hPE, map_zero])
  simpa only [map_add] using h

theorem ThreeCopies.annihilates_one (p : ℕ) [CharP K p]
    (C : ThreeCopies K R) (z : R → T) (hz : OrthogonalAdditiveOn C.system z) :
    p • z 1 = 0 := by
  have hcopy (i) := C.additive_copy z hz i
  have hcommon (i : Fin 3) :
      p • z (C.copy i (diagonalUnit 0)) = p • z (C.copy 0 (diagonalUnit 1)) := by
    have h := nsmul_diagonal_eq p (fun M => z (C.copy i M)) (hcopy i)
      0 1 2 (by decide) (by decide) (by decide)
    simpa only [C.common_second] using h
  have hsplit : z (C.copy 0 (diagonalUnit 0)) =
      z (C.copy 1 (diagonalUnit 0)) + z (C.copy 2 (diagonalUnit 0)) := by
    rw [C.partition]
    apply hz _ _ (C.diagonal_mem 1 0) (C.diagonal_mem 2 0)
    · rw [← C.partition]
      exact C.diagonal_mem 0 0
    · exact C.partition_orthogonal
    · exact C.partition_orthogonal'
  have hq : p • z (C.copy 0 (diagonalUnit 1)) =
      p • z (C.copy 0 (diagonalUnit 1)) + p • z (C.copy 0 (diagonalUnit 1)) := by
    calc p • z (C.copy 0 (diagonalUnit 1)) = p • z (C.copy 0 (diagonalUnit 0)) :=
           (hcommon 0).symm
         _ = p • z (C.copy 1 (diagonalUnit 0)) +
           p • z (C.copy 2 (diagonalUnit 0)) := by rw [hsplit, nsmul_add]
         _ = _ := by rw [hcommon, hcommon]
  have hzero : p • z (C.copy 0 (diagonalUnit 1)) = 0 := by
    exact (add_left_cancel ((add_zero _).trans hq)).symm
  have hzero₀ : p • z (C.copy 0 (diagonalUnit 0)) = 0 :=
    (hcommon 0).trans hzero
  have hzero₂ : p • z (C.copy 0 (diagonalUnit 2)) = 0 := by
    have h := nsmul_diagonal_eq p (fun M => z (C.copy 0 M)) (hcopy 0)
      0 2 1 (by decide) (by decide) (by decide)
    exact h.symm.trans hzero₀
  have hsum := orthogonalAdditive_one (fun M => z (C.copy 0 M)) (hcopy 0)
  rw [C.first_one] at hsum
  rw [hsum, nsmul_add, nsmul_add, hzero₀, hzero, hzero₂, add_zero, add_zero]

end

open Matrix
open scoped Matrix

variable {K R : Type*} [CommRing K] [Ring R]

def contraction {n : Type*} [Fintype n] [DecidableEq n]
    (S : Matrix Unit n R) (D : Matrix n Unit R) (h : D * S = 1) :
    Matrix n n R →ₙ+* Matrix Unit Unit R where
  toFun M := S * M * D
  map_zero' := by simp
  map_add' M N := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_mul' M N := by
    calc S * (M * N) * D = (S * M) * (N * D) := by
           simp only [Matrix.mul_assoc]
         _ = (S * M) * ((D * S) * (N * D)) := by rw [h, Matrix.one_mul]
         _ = (S * M * D) * (S * N * D) := by simp only [Matrix.mul_assoc]

def oneByOne : Matrix Unit Unit R →+* R where
  toFun M := M () ()
  map_zero' := rfl
  map_one' := by simp
  map_add' _ _ := rfl
  map_mul' M N := by simp [Matrix.mul_apply]

variable [Algebra K R]

noncomputable def matrixCopy {n : Type*} [Fintype n] [DecidableEq n]
    (s d : n → R) (h : ∀ i j, d i * s j = if i = j then 1 else 0) :
    Matrix n n K →ₙ+* R :=
  oneByOne.toNonUnitalRingHom.comp
    ((contraction (Matrix.of fun _ j => s j) (Matrix.of fun i _ => d i) (by
        ext i j
        change (∑ _k : Unit, d i * s j) = if i = j then 1 else 0
        simpa using h i j)).comp
      (algebraMap K R).mapMatrix.toNonUnitalRingHom)

lemma matrixCopy_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (s d : n → R) (h : ∀ i j, d i * s j = if i = j then 1 else 0) (i : n) :
    matrixCopy (K := K) s d h (diagonalUnit i) = s i * d i := by
  change ((Matrix.of fun (_ : Unit) j => s j) *
    (diagonalUnit i).map (algebraMap K R) * (Matrix.of fun i (_ : Unit) => d i)) () () = _
  simp [diagonalUnit, rankOne, basisVector, Matrix.mul_apply,
    Matrix.vecMulVec_apply, Pi.single_apply, Matrix.map_apply, apply_ite]

end FiniteIdempotentDiagrams

end

end OAI
