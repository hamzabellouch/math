import Mathlib
import OAI.NumberTheory.PiExponent.Polynomials.GradedSerre

namespace OAI

namespace PiExponent.GradedH0
noncomputable section
open scoped BigOperators
open ProjectiveMonomialCech
variable {ι R : Type*} [Fintype ι] [CommRing R]

def PolynomialExponent (n : ℕ) := {b : ι →₀ ℕ // b.degree = n}

def NonnegativeMonomialSet (d : ℤ) : Set (Monomial ι d) :=
  {a | ∀ j, 0 ≤ a.val j}

def encode (n : ℕ) (b : PolynomialExponent (ι := ι) n) : Monomial ι (n : ℤ) :=
  ⟨fun j => (b.val j : ℤ), by
    rw [← Nat.cast_sum, ← Finsupp.degree_eq_sum, b.property]⟩

@[simp] theorem encode_apply (n : ℕ) (b : PolynomialExponent (ι := ι) n) (j : ι) :
    (encode n b).val j = (b.val j : ℤ) := rfl

theorem encode_nonnegative (n : ℕ) (b : PolynomialExponent (ι := ι) n) :
    encode n b ∈ NonnegativeMonomialSet (n : ℤ) := fun _j => Int.natCast_nonneg _

def decode (n : ℕ) (a : NonnegativeMonomialSet (ι := ι) (n : ℤ)) :
    PolynomialExponent (ι := ι) n := by
  let b : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun j => (a.val.val j).toNat)
  refine ⟨b, ?_⟩
  apply Int.natCast_inj.mp
  calc
    (b.degree : ℤ) = ∑ j, ((a.val.val j).toNat : ℤ) := by
      rw [Finsupp.degree_eq_sum, Nat.cast_sum]
      rfl
    _ = ∑ j, a.val.val j := by
      apply Finset.sum_congr rfl
      intro j _
      exact Int.toNat_of_nonneg (a.property j)
    _ = (n : ℤ) := a.val.property

@[simp] theorem decode_apply (n : ℕ) (a : NonnegativeMonomialSet (ι := ι) (n : ℤ))
    (j : ι) : (decode n a).val j = (a.val.val j).toNat := rfl

def exponentEquiv (n : ℕ) :
    PolynomialExponent (ι := ι) n ≃ NonnegativeMonomialSet (ι := ι) (n : ℤ) where
  toFun b := ⟨encode n b, encode_nonnegative n b⟩
  invFun := decode n
  left_inv b := by
    apply Subtype.ext
    ext j
    simp
  right_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    simp only [encode_apply, decode_apply]
    exact Int.toNat_of_nonneg (a.property j)

def homogeneousPolynomialEquiv (n : ℕ) :
    MvPolynomial.homogeneousSubmodule ι R n ≃ₗ[R]
      Finsupp.supported R R (NonnegativeMonomialSet (ι := ι) (n : ℤ)) :=
  (LinearEquiv.ofEq _ _ (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported ι R n)).trans <|
    (AddMonoidAlgebra.supportedEquivFinsupp {b : ι →₀ ℕ | b.degree = n}).trans <|
      (Finsupp.domLCongr (exponentEquiv n)).trans
        (Finsupp.supportedEquivFinsupp (NonnegativeMonomialSet (ι := ι) (n : ℤ))).symm

theorem integer_grading_eq_homogeneous (n : ℕ) :
    MvPolynomial.weightedHomogeneousSubmodule R (1 : ι → ℤ) (n : ℤ) =
      MvPolynomial.homogeneousSubmodule ι R n := by
  rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported,
    MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  have hweight (b : ι →₀ ℕ) : Finsupp.weight (1 : ι → ℤ) b = (b.degree : ℤ) := by
    simp [Finsupp.weight_eq_sum, Finsupp.degree_eq_sum, Nat.cast_sum]
  congr 1
  ext b
  simp only [Set.mem_ofPred_eq, hweight, Int.natCast_inj]

def integerHomogeneousPolynomialEquiv (d : ℤ) (hd : 0 ≤ d) :
    MvPolynomial.weightedHomogeneousSubmodule R (1 : ι → ℤ) d ≃ₗ[R]
      Finsupp.supported R R (NonnegativeMonomialSet (ι := ι) d) := by
  cases d with
  | ofNat n =>
      exact (LinearEquiv.ofEq _ _ (integer_grading_eq_homogeneous n)).trans
        (homogeneousPolynomialEquiv n)
  | negSucc n => omega

def polynomialLaurent (n : ℕ) :
    MvPolynomial.homogeneousSubmodule ι R n →ₗ[R] Laurent ι R (n : ℤ) :=
  (Finsupp.supported R R (NonnegativeMonomialSet (ι := ι) (n : ℤ))).subtype.comp
    (homogeneousPolynomialEquiv n).toLinearMap

theorem mem_supported_iff_regular (d : ℤ) (p : Laurent ι R d) :
    p ∈ Finsupp.supported R R (NonnegativeMonomialSet d) ↔ RegularOn ∅ p := by
  classical
  rw [Finsupp.mem_supported]
  constructor
  · intro hp a ha j hj
    exact False.elim ((not_lt_of_ge (hp (Finsupp.mem_support_iff.mpr ha) j)) hj)
  · intro hp a ha j
    by_contra hneg
    exact hp a (Finsupp.mem_support_iff.mp ha) j (lt_of_not_ge hneg)

theorem polynomialLaurent_injective (n : ℕ) :
    Function.Injective (polynomialLaurent (ι := ι) (R := R) n) :=
  Subtype.val_injective.comp (homogeneousPolynomialEquiv n).injective

theorem polynomialLaurent_regular (n : ℕ)
    (p : MvPolynomial.homogeneousSubmodule ι R n) :
    RegularOn ∅ (polynomialLaurent n p) :=
  (mem_supported_iff_regular _ _).mp (homogeneousPolynomialEquiv n p).property

theorem existsUnique_polynomial_of_regular (n : ℕ) (f : Laurent ι R (n : ℤ))
    (hf : RegularOn ∅ f) :
    ∃! p : MvPolynomial.homogeneousSubmodule ι R n, polynomialLaurent n p = f := by
  let a : Finsupp.supported R R (NonnegativeMonomialSet (ι := ι) (n : ℤ)) :=
    ⟨f, (mem_supported_iff_regular _ _).mpr hf⟩
  refine ⟨(homogeneousPolynomialEquiv n).symm a, ?_, ?_⟩
  · change ((homogeneousPolynomialEquiv n) ((homogeneousPolynomialEquiv n).symm a)).val = f
    rw [LinearEquiv.apply_symm_apply]
  · intro p hp
    apply polynomialLaurent_injective n
    rw [hp]
    change f = ((homogeneousPolynomialEquiv n) ((homogeneousPolynomialEquiv n).symm a)).val
    rw [LinearEquiv.apply_symm_apply]

theorem existsUnique_polynomial_of_compatible_vertices [Nonempty ι] (n : ℕ)
    (c : ι → Laurent ι R (n : ℤ)) (hc : ∀ j, RegularOn {j} (c j))
    (heq : ∀ i j, c i = c j) :
    ∃! p : MvPolynomial.homogeneousSubmodule ι R n,
      ∀ j, polynomialLaurent n p = c j := by
  obtain ⟨f, hf, hcf⟩ := GradedSerre.compatible_vertices_are_polynomial
    (Int.natCast_nonneg n) c hc heq
  obtain ⟨p, hp, huniq⟩ := existsUnique_polynomial_of_regular n f hf
  refine ⟨p, fun j => hp.trans (hcf j).symm, ?_⟩
  intro q hq
  exact huniq q ((hq (Classical.choice inferInstance)).trans (hcf _))

theorem zeroth_cocycle_vertices_eq {d : ℤ}
    (c : ProjectiveMonomialCechHigher.Cochain ι (Laurent ι R d) 0)
    (hc : ProjectiveMonomialCechHigher.differential c = 0) (i j : ι) :
    c (fun _ => i) = c (fun _ => j) := by
  have h := congrFun hc (![i, j] : Fin 2 → ι)
  simp only [ProjectiveMonomialCechHigher.differential, Fin.sum_univ_succ,
    Fin.val_zero, pow_zero, one_zsmul, Fin.val_succ, Fin.sum_univ_zero,
    add_zero, Nat.zero_add, pow_one, neg_one_zsmul, Pi.zero_apply] at h
  have hi : (![i, j] : Fin 2 → ι) ∘ (0 : Fin 2).succAbove = (fun _ => j) := by
    funext k
    fin_cases k
    rfl
  have hj : (![i, j] : Fin 2 → ι) ∘ (Fin.succ (0 : Fin 1)).succAbove = (fun _ => i) := by
    funext k
    fin_cases k
    rfl
  rw [hi, hj] at h
  exact (eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using h)).symm

theorem zeroth_cocycle_unique_homogeneous_polynomial [Nonempty ι] (n : ℕ)
    (c : ProjectiveMonomialCechHigher.Cochain ι (Laurent ι R (n : ℤ)) 0)
    (hreg : ProjectiveMonomialCechHigher.Regular c)
    (hc : ProjectiveMonomialCechHigher.differential c = 0) :
    ∃! p : MvPolynomial.homogeneousSubmodule ι R n,
      ∀ t, polynomialLaurent n p = c t := by
  have hreg' (j : ι) : RegularOn {j} (c (fun _ => j)) := by
    have h := hreg (fun _ => j)
    simpa only [Set.range_const] using h
  obtain ⟨p, hp, hu⟩ := existsUnique_polynomial_of_compatible_vertices n
    (fun j => c (fun _ => j)) hreg' (zeroth_cocycle_vertices_eq c hc)
  refine ⟨p, ?_, ?_⟩
  · intro t
    have ht : t = fun _ => t 0 := by
      funext i
      exact congrArg t (show i = 0 by omega)
    rw [ht]
    exact hp (t 0)
  · intro q hq
    exact hu q (fun j => hq (fun _ => j))

end
end PiExponent.GradedH0

end OAI
