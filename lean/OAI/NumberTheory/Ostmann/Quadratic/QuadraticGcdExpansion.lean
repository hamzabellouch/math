import OAI.NumberTheory.Ostmann.Quadratic.QuadraticPairKernel
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSieveTranspose

namespace OAI

/-! # Exact common-divisor expansion of the quadratic second moment -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

def quadraticGcdPairs (N d : ℕ) : Finset (ℕ × ℕ) :=
  ((oddSquarefreeRange N).product (oddSquarefreeRange N)).filter
    fun z => z.1.gcd z.2 = d

noncomputable def quadraticGcdKernelSum (N d : ℕ) (b : ℕ → ℂ) (m : ℤ) : ℂ :=
  ∑ z ∈ quadraticGcdPairs N d,
    b z.1 * conj (b z.2) * (jacobiSym m (quadraticPairKernel z.1 z.2) : ℂ)

 theorem quadraticTranspose_norm_sq_expand (N : ℕ) (b : ℕ → ℂ) (m : ℤ) :
    (‖quadraticTransposeSum N b m‖ ^ 2 : ℂ) =
      ∑ z ∈ (oddSquarefreeRange N).product (oddSquarefreeRange N),
        b z.1 * conj (b z.2) * (jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ) := by
  rw [← Complex.mul_conj']
  simp only [quadraticTransposeSum, map_sum, map_mul, map_intCast,
    Finset.sum_mul, Finset.mul_sum]
  symm
  calc
    _ = ∑ n₁ ∈ oddSquarefreeRange N, ∑ n₂ ∈ oddSquarefreeRange N,
        b n₁ * conj (b n₂) * (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) :=
      Finset.sum_product (oddSquarefreeRange N) (oddSquarefreeRange N) _
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n₁ _
      apply Finset.sum_congr rfl
      intro n₂ _
      ring

 theorem quadraticTranspose_norm_sq_gcd (N : ℕ) (b : ℕ → ℂ) (m : ℤ) :
    (‖quadraticTransposeSum N b m‖ ^ 2 : ℂ) =
      ∑ d ∈ Finset.Icc 1 N, (if m.gcd d = 1 then (1 : ℂ) else 0) *
        quadraticGcdKernelSum N d b m := by
  rw [quadraticTranspose_norm_sq_expand]
  have hmaps (z : ℕ × ℕ)
      (hz : z ∈ (oddSquarefreeRange N).product (oddSquarefreeRange N)) :
      z.1.gcd z.2 ∈ Finset.Icc 1 N := by
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hz
    obtain ⟨hr₁, _, _⟩ := Finset.mem_filter.mp h₁
    exact Finset.mem_Icc.mpr
      ⟨Nat.gcd_pos_of_pos_left _ (Finset.mem_Icc.mp hr₁).1,
        (Nat.gcd_le_left _ (Finset.mem_Icc.mp hr₁).1).trans (Finset.mem_Icc.mp hr₁).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro d _
  rw [quadraticGcdKernelSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨hz, he⟩ := Finset.mem_filter.mp hz
  obtain ⟨hz₁, hz₂⟩ := Finset.mem_product.mp hz
  have hs := jacobi_pair_kernel (Finset.mem_filter.mp hz₁).2.2
    (Finset.mem_filter.mp hz₂).2.2 m
  rw [he] at hs
  calc
    _ = b z.1 * conj (b z.2) *
        ((jacobiSym m z.1 * jacobiSym m z.2 : ℤ) : ℂ) := by push_cast; ring
    _ = _ := by rw [hs]; split_ifs <;> simp [mul_assoc]

end Ostmann

end OAI
