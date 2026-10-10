import OAI.NumberTheory.Ostmann.QuadraticSieveRowInflationDyadic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

theorem exists_quadraticNorm_rowInflation_at_scale :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (M N L : ℕ), 0 < M → 0 < N → M ≤ L →
      C*(M:ℝ)*Real.log (2*(M:ℝ)*N) ≤ L → ∀ S : Finset ℕ,
      S ⊆ oddSquarefreeUpTo N → ∃ M' : ℕ, L ≤ M' ∧ M' ≤ 32*L ∧
      quadraticNorm (dyadicSquarefreeRows M) S ≤
        20*quadraticNorm (dyadicSquarefreeRows M') S := by
  obtain ⟨C,hC,hbound⟩ := exists_quadraticNorm_rowInflation_dyadic
  refine ⟨C,hC,?_⟩
  intro M N L hM hN hML hscale S hS
  let R : ℕ := L/M+1
  have hdiv : L/M*M ≤ L := Nat.div_mul_le_self L M
  have hrem : L%M < M := Nat.mod_lt L hM
  have hdivision : L%M+M*(L/M) = L := Nat.mod_add_div L M
  have hLR : L ≤ R*M := by dsimp [R]; nlinarith
  have hRL : R*M ≤ 2*L := by dsimp [R]; nlinarith
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have hRscale : C*Real.log (2*(M:ℝ)*N) ≤ R := by
    have hh : (L:ℝ) ≤ (R:ℝ)*M := by exact_mod_cast hLR
    have hmul : C*Real.log (2*(M:ℝ)*N)*(M:ℝ) ≤ (R:ℝ)*M := by nlinarith
    exact le_of_mul_le_mul_right hmul hMr
  obtain ⟨j,hj,hjbound⟩ := hbound M N R hM hN hRscale S hS
  refine ⟨2^j*(R*M),?_,?_,hjbound⟩
  · have hp : 1 ≤ 2^j := by
      have hh : 0 < (2:ℕ)^j := by positivity
      omega
    nlinarith
  · have hp : 2^j ≤ 16 := by
      have hh := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:ℕ)) (show j≤4 by omega)
      norm_num at hh
      exact hh
    nlinarith

end Ostmann.QuadraticSieve

end

end OAI
