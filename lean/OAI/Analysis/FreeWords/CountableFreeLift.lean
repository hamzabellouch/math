import Mathlib
import OAI.Analysis.FreeWords.FiniteMatrixFreeApproximation

namespace OAI

noncomputable section

namespace KKFreeLiftFrontier

open KKTraceTransfer Filter Topology

noncomputable section

theorem countable_matrix_free_approximation
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [Nontrivial H] (M : VonNeumannAlgebra H)
    (τ : FaithfulNormalTrace M) (hfac : IsFactor M) (hdiff : IsDiffuse M)
    (n : ℕ) (hn : 0 < n) (T : ℕ → List (ℤ × MatrixAlgebra n M))
    (hT : ∀ i, IsCenteredTest τ (T i)) :
    ∃ d : ℕ → ℕ, (∀ j, 0 < d j) ∧
      ∃ ρ : ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M,
      (∀ j, Function.Injective (ρ j)) ∧ ∃ U : ℕ → unitary (MatrixAlgebra n M),
      (∀ j i k, (U j).val i k ∈ (ρ j).range) ∧
      (∀ k : ℤ, k ≠ 0 → Tendsto (fun j => matrixTrace τ n (U j ^ k).val) atTop (𝓝 0)) ∧
      (∀ i, Tendsto (fun j => mixedMoment τ (U j) (T i)) atTop (𝓝 0)) := by
  classical
  have hε (j : ℕ) : 0 < (1 : ℝ) / (j + 1) := by positivity
  have ex (j : ℕ) := finite_matrix_free_approximation H M τ hfac hdiff n hn
    ((Finset.range (j+1)).image T)
    (by intro w hw; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw; exact hT i)
    (Finset.Icc (-(j:ℤ)) (j:ℤ)) ((1:ℝ)/(j+1)) (hε j)
  choose d hd ρ hρ U hU hH hM using ex
  refine ⟨d,hd,ρ,hρ,U,hU,?_,?_⟩
  · intro k hk
    apply squeeze_zero_norm' _ tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [eventually_ge_atTop k.natAbs] with j hj
    apply (hH j k _ hk).le
    apply Finset.mem_Icc.mpr
    have hc : (k.natAbs:ℤ) ≤ (j:ℤ) := by exact_mod_cast hj
    have hpos : k ≤ (k.natAbs:ℤ) := Int.le_natAbs
    have hneg : -k ≤ (k.natAbs:ℤ) := by simpa using (Int.le_natAbs (a := -k))
    constructor <;> omega
  · intro i
    apply squeeze_zero_norm' _ tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [eventually_ge_atTop i] with j hj
    apply (hM j (T i) _).le
    apply Finset.mem_image.mpr
    exact ⟨i,Finset.mem_range.mpr (by omega),rfl⟩

end

end KKFreeLiftFrontier
end

end OAI
