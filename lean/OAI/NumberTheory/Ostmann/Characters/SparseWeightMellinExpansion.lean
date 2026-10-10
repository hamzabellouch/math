import OAI.NumberTheory.Ostmann.Characters.SparseCoefficientMajorant
import OAI.NumberTheory.Ostmann.Supply.TruncatedBilinearCube

namespace OAI

/-! # Multiplicative Fourier expansion of the original squared subset weight -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable local instance {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

theorem sparsePatternMellin_inversion {p : ℕ} [Fact p.Prime]
    (E : Finset (ZMod p)) (t : ℝ) (v : Bool × Bool) (x : (ZMod p)ˣ) :
    subsetPairFactor (sparseAdditiveKernel E t x) v =
      ∑ χ : MulChar (ZMod p) ℂ, sparsePatternMellin E t χ v * χ x := by
  rcases v with ⟨v, w⟩
  cases v <;> cases w
  · simp only [subsetPairFactor, sparsePatternMellin, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, MulChar.one_apply_coe]
  · exact (mellin_inversion (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x) x).symm
  · exact (mellin_inversion (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x) x).symm
  · exact (mellin_inversion (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x ^ 2) x).symm

theorem sparseWeight_mellin_expansion {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (E : ∀ i, Finset (ZMod (p i))) (t : ℝ) (K : ℕ)
    (x : ∀ i, (ZMod (p i))ˣ) :
    elementaryTruncation (fun i => sparseAdditiveKernel (E i) t (x i)) K ^ 2 =
      ∑ χ : (∀ i, MulChar (ZMod (p i)) ℂ),
        sparseTruncatedMellinCoefficient p E t K χ * ∏ i, χ i (x i) := by
  rw [elementaryTruncation_square_cube]
  simp_rw [sparsePatternMellin_inversion]
  simp_rw [Fintype.prod_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  unfold sparseTruncatedMellinCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  exact Finset.prod_mul_distrib

end Ostmann

end OAI
