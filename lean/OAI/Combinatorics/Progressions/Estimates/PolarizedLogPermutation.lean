import OAI.Combinatorics.Progressions.Polynomial.RealPolarizedPolynomialOrbit

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem polarizedLog_eval_permute (p : F.adaptedLieSubalgebra)
    (e : Equiv.Perm ι) (he : ∀ i, π (e i) = π i) (x : ι → ℚ) :
    F.squarefreeBlockPermute π e he (eval x (F.polarizedLog π p)) =
      eval (fun i => x (e.symm i)) (F.polarizedLog π p) := by
  rw [F.polarizedLog_eval, F.polarizedLog_eval]
  simp only [map_sum, map_smul, F.polarizedCoefficient_permute π p e he]
  symm
  calc
    (∑ a : SquarefreeIndex ι, (a.val.prod fun i n => x (e.symm i) ^ n) •
        F.polarizedCoefficient π p a) =
      ∑ a : SquarefreeIndex ι,
        ((SquarefreeIndex.permute e a).val.prod fun i n => x (e.symm i) ^ n) •
        F.polarizedCoefficient π p (SquarefreeIndex.permute e a) :=
      (Equiv.sum_comp (SquarefreeIndex.permute e) _).symm
    _ = _ := by simp only [SquarefreeIndex.permute_weight]

end Erdos3.MultidegreeLieFiltration

end

end OAI
