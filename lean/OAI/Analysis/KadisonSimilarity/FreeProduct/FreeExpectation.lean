import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Tactic

namespace OAI

/-!
# The expectation of a free compression

Scalar tracial freeness is expressed by vanishing alternating centered words.
The formula `E(e b e) = τ(e)^2 b` is derived by testing against the second
algebra, rather than included among the free-product input data.
-/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]

/-- An alternating word of centered letters in two specified algebras. -/
inductive AlternatingCenteredWord (τ : R →ₗ[ℂ] ℂ) (P Q : StarSubalgebra ℂ R) :
    Bool → List R → Prop
  | nil (side : Bool) : AlternatingCenteredWord τ P Q side []
  | cons {side : Bool} {x : R} {xs : List R}
      (hmem : x ∈ if side then P else Q) (hzero : τ x = 0)
      (htail : AlternatingCenteredWord τ P Q (!side) xs) :
      AlternatingCenteredWord τ P Q side (x :: xs)

/-- Scalar freeness, in the alternating-centered-word convention of the paper. -/
def ScalarFree (τ : R →ₗ[ℂ] ℂ) (P Q : StarSubalgebra ℂ R) : Prop :=
  ∀ side x xs, AlternatingCenteredWord τ P Q side (x :: xs) → τ ((x :: xs).prod) = 0

namespace ScalarFree

variable {τ : R →ₗ[ℂ] ℂ} {P Q : StarSubalgebra ℂ R} (hf : ScalarFree τ P Q)

include hf in
theorem trace_pair {a b : R} (ha : a ∈ P) (hb : b ∈ Q)
    (ha0 : τ a = 0) (hb0 : τ b = 0) : τ (a * b) = 0 := by
  have h := hf true a [b] (.cons (by simpa) ha0 (.cons (by simpa) hb0 (.nil true)))
  simpa using h

include hf in
theorem trace_triple {a b c : R} (ha : a ∈ Q) (hb : b ∈ P) (hc : c ∈ Q)
    (ha0 : τ a = 0) (hb0 : τ b = 0) (hc0 : τ c = 0) : τ (a * b * c) = 0 := by
  have h := hf false a [b, c]
    (.cons (by simpa) ha0 (.cons (by simpa) hb0 (.cons (by simpa) hc0 (.nil true))))
  simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using h

include hf in
theorem trace_quadruple {a b c d : R} (ha : a ∈ Q) (hb : b ∈ P)
    (hc : c ∈ Q) (hd : d ∈ P)
    (ha0 : τ a = 0) (hb0 : τ b = 0) (hc0 : τ c = 0) (hd0 : τ d = 0) :
    τ (a * b * c * d) = 0 := by
  have h := hf false a [b, c, d]
    (.cons (by simpa) ha0 (.cons (by simpa) hb0
      (.cons (by simpa) hc0 (.cons (by simpa) hd0 (.nil false)))))
  simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using h

end ScalarFree

/-- Centering uses the normalized trace. -/
def traceCentered (τ : R →ₗ[ℂ] ℂ) (a : R) : R := a - τ a • 1

theorem traceCentered_mem (τ : R →ₗ[ℂ] ℂ) (P : StarSubalgebra ℂ R)
    {a : R} (ha : a ∈ P) : traceCentered τ a ∈ P :=
  P.sub_mem ha (P.smul_mem (P.one_mem) _)

omit [StarRing R] [StarModule ℂ R] in
@[simp] theorem traceCentered_trace (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1) (a : R) :
    τ (traceCentered τ a) = 0 := by simp [traceCentered, hτ]

omit [StarRing R] [StarModule ℂ R] in
theorem traceCentered_add (τ : R →ₗ[ℂ] ℂ) (a : R) :
    traceCentered τ a + τ a • 1 = a := sub_add_cancel _ _

/-- A centered letter is orthogonal, for the trace pairing, to the other algebra. -/
theorem trace_centered_mul_of_free
    (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1) {P Q : StarSubalgebra ℂ R}
    (hf : ScalarFree τ P Q) {a b : R} (ha : a ∈ P) (ha0 : τ a = 0) (hb : b ∈ Q) :
    τ (a * b) = 0 := by
  have hpair := hf.trace_pair ha (traceCentered_mem τ Q hb) ha0 (traceCentered_trace τ hτ b)
  calc
    τ (a * b) = τ (a * traceCentered τ b + τ b • a) := by
      apply congrArg τ
      calc
        a * b = a * (traceCentered τ b + τ b • 1) :=
          congrArg (fun z : R => a * z) (traceCentered_add τ b).symm
        _ = _ := by rw [mul_add, mul_smul_comm, mul_one]
    _ = 0 := by rw [map_add, map_smul, hpair, ha0]; simp

/-- Orthogonality against the second algebra removes all three mixed terms
in the free-compression expansion. -/
theorem trace_test_free_compression_errors
    (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1)
    (htr : ∀ a b, τ (a * b) = τ (b * a))
    {P Q : StarSubalgebra ℂ R} (hf : ScalarFree τ P Q)
    {a b c : R} (ha : a ∈ P) (ha0 : τ a = 0)
    (hb : b ∈ Q) (hb0 : τ b = 0) (hc : c ∈ Q) :
    τ (c * (a * b)) = 0 ∧ τ (c * (b * a)) = 0 ∧ τ (c * (a * b * a)) = 0 := by
  have hc0 := traceCentered_trace τ hτ c
  have hcm := traceCentered_mem τ Q hc
  have hab := hf.trace_pair ha hb ha0 hb0
  have hcab := hf.trace_triple hcm ha hb hc0 ha0 hb0
  have hcaba := hf.trace_quadruple hcm ha hb ha hc0 ha0 hb0 ha0
  have hba2 : τ (b * (a * a)) = 0 := by
    rw [htr]
    -- The product a² need not be centered; center it before pairing with b.
    have hp := hf.trace_pair (traceCentered_mem τ P (P.mul_mem ha ha)) hb
      (traceCentered_trace τ hτ _) hb0
    have heq : τ ((a * a) * b) = τ (traceCentered τ (a * a) * b) := by
      rw [traceCentered, sub_mul, smul_mul_assoc, one_mul, map_sub, map_smul, hb0]
      simp
    exact heq.trans hp
  have haba : τ (a * b * a) = 0 := by
    rw [htr (a * b) a]
    have ha2b : τ ((a * a) * b) = 0 := by rw [htr]; exact hba2
    simpa only [mul_assoc] using ha2b
  have hfirst : τ (c * (a * b)) = 0 := by
    rw [← traceCentered_add τ c, add_mul, smul_mul_assoc, one_mul, map_add, map_smul]
    have hcab' : τ (traceCentered τ c * (a * b)) = 0 := by
      simpa only [mul_assoc] using hcab
    rw [hcab', hab, smul_zero, add_zero]
  have hsecond : τ (c * (b * a)) = 0 := by
    rw [← mul_assoc, htr]
    exact trace_centered_mul_of_free τ hτ hf ha ha0 (Q.mul_mem hc hb)
  have hthird : τ (c * (a * b * a)) = 0 := by
    rw [← traceCentered_add τ c, add_mul, smul_mul_assoc, one_mul, map_add, map_smul]
    have hcaba' : τ (traceCentered τ c * (a * b * a)) = 0 := by
      simpa only [mul_assoc] using hcaba
    rw [hcaba', haba, smul_zero, add_zero]
  exact ⟨hfirst, hsecond, hthird⟩

/-- The trace pairing determines the conditional expectation in a faithful
tracial representation. -/
theorem expectation_eq_of_trace_pairings
    (τ : R →ₗ[ℂ] ℂ) (Q : StarSubalgebra ℂ R)
    (hfaithful : ∀ z, τ (star z * z) = 0 → z = 0)
    (E : R →ₗ[ℂ] R) (hE : ∀ x, E x ∈ Q)
    (htrace : ∀ x c, c ∈ Q → τ (c * E x) = τ (c * x))
    (x y : R) (hy : y ∈ Q)
    (hxy : ∀ c, c ∈ Q → τ (c * x) = τ (c * y)) : E x = y := by
  apply sub_eq_zero.mp
  apply hfaithful
  have hc : star (E x - y) ∈ Q := star_mem (Q.sub_mem (hE x) hy)
  rw [mul_sub, map_sub, htrace x _ hc, hxy _ hc, sub_self]

/-- The expectation formula in `lem:free-compression`, proved from scalar
freeness and the defining trace-pairing property of conditional expectation.
The projection condition on `e` is not needed for this algebraic identity. -/
theorem expectation_free_compression
    (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1)
    (htr : ∀ a b, τ (a * b) = τ (b * a))
    (hfaithful : ∀ z, τ (star z * z) = 0 → z = 0)
    {P Q : StarSubalgebra ℂ R} (hf : ScalarFree τ P Q)
    (E : R →ₗ[ℂ] R) (hE : ∀ x, E x ∈ Q)
    (htrace : ∀ x c, c ∈ Q → τ (c * E x) = τ (c * x))
    {e b : R} (he : e ∈ P) (hb : b ∈ Q) (hb0 : τ b = 0) :
    E (e * b * e) = (τ e) ^ 2 • b := by
  let a := traceCentered τ e
  have ha : a ∈ P := traceCentered_mem τ P he
  have ha0 : τ a = 0 := traceCentered_trace τ hτ e
  have hexpand : e * b * e = (τ e) ^ 2 • b +
      τ e • (a * b) + τ e • (b * a) + a * b * a := by
    calc
      _ = (a + τ e • 1) * b * (a + τ e • 1) := by
        dsimp [a]
        rw [traceCentered_add]
      _ = _ := by
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
          one_mul, mul_one, smul_add, smul_smul, pow_two]
        abel
  apply expectation_eq_of_trace_pairings τ Q hfaithful E hE htrace _ _ (Q.smul_mem hb _)
  intro c hc
  obtain ⟨h1, h2, h3⟩ := trace_test_free_compression_errors τ hτ htr hf ha ha0 hb hb0 hc
  rw [hexpand]
  simp only [mul_add, mul_smul_comm, map_add, map_smul, h1, h2, h3,
    smul_zero, add_zero]

end KadisonSimilarity

end

end OAI
