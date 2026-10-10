import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Nat.Factorization.Induction

namespace OAI

/-! # Finite reductions modulo integers from finite reductions modulo primes -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct Pointwise
variable (M : Type) [AddCommGroup M]

def integerMultiples (n : ℕ) : Submodule ℤ M :=
  (Ideal.span {(n : ℤ)} : Ideal ℤ) • (⊤ : Submodule ℤ M)

theorem mem_integerMultiples (n : ℕ) (x : M) :
    x ∈ integerMultiples M n ↔ ∃ y : M, (n : ℤ) • y = x := by
  rw [integerMultiples, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and]

def integerReductionEquiv (n : ℕ) :
    (ZMod n ⊗[ℤ] M) ≃ₗ[ℤ] M ⧸ integerMultiples M n := by
  let e : ZMod n ≃ₗ[ℤ] ℤ ⧸ Ideal.span {(n : ℤ)} :=
    (Int.quotientSpanNatEquivZMod n).symm.toAddEquiv.toIntLinearEquiv
  exact (TensorProduct.congr e (LinearEquiv.refl ℤ M)).trans
    (TensorProduct.quotTensorEquivQuotSMul M (Ideal.span {(n : ℤ)}))

theorem finite_integerReduction_mul (n m : ℕ)
    [Finite (M ⧸ integerMultiples M n)] [Finite (M ⧸ integerMultiples M m)] :
    Finite (M ⧸ integerMultiples M (n * m)) := by
  classical
  let P := integerMultiples M n
  let Q := integerMultiples M m
  let L := integerMultiples M (n * m)
  choose s hs using P.mkQ_surjective
  choose t ht using Q.mkQ_surjective
  let F : (M ⧸ P) × (M ⧸ Q) → M ⧸ L :=
    fun x => L.mkQ (s x.1 + (n : ℤ) • t x.2)
  apply Finite.of_surjective F
  intro c
  obtain ⟨x, rfl⟩ := L.mkQ_surjective c
  have hx : x - s (P.mkQ x) ∈ P := (Submodule.Quotient.eq P).mp (hs (P.mkQ x)).symm
  obtain ⟨y, hy⟩ := (mem_integerMultiples M n _).mp hx
  have hy' : y - t (Q.mkQ y) ∈ Q := (Submodule.Quotient.eq Q).mp (ht (Q.mkQ y)).symm
  obtain ⟨z, hz⟩ := (mem_integerMultiples M m _).mp hy'
  refine ⟨(P.mkQ x, Q.mkQ y), ?_⟩
  apply Eq.symm
  apply (Submodule.Quotient.eq L).mpr
  apply (mem_integerMultiples M (n * m) _).mpr
  refine ⟨z, ?_⟩
  calc
    ((n * m : ℕ) : ℤ) • z = (n : ℤ) • ((m : ℤ) • z) := by rw [Nat.cast_mul, mul_smul]
    _ = (n : ℤ) • (y - t (Q.mkQ y)) := by rw [hz]
    _ = x - (s (P.mkQ x) + (n : ℤ) • t (Q.mkQ y)) := by
      rw [smul_sub, hy]
      abel

theorem finite_integerReduction_of_primes
    (h : ∀ p : ℕ, p.Prime → Finite (M ⧸ integerMultiples M p))
    (n : ℕ) (hn : n ≠ 0) : Finite (M ⧸ integerMultiples M n) := by
  have hall : ∀ a : ℕ, a ≠ 0 → Finite (M ⧸ integerMultiples M a) := by
    apply induction_on_primes
    · intro h0
      exact (h0 rfl).elim
    · intro _
      have he : integerMultiples M 1 = ⊤ := by
        ext x
        simp [mem_integerMultiples]
      rw [he]
      infer_instance
    · intro p a hp ha hpa
      have hane : a ≠ 0 := by intro he; simp [he] at hpa
      let := h p hp
      let := ha hane
      exact finite_integerReduction_mul M p a
  exact hall n hn

end PolycyclicRecognition

end

end OAI
