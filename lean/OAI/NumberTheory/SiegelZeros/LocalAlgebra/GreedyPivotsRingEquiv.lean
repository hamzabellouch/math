import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.AlgebraMapMemSpanImage

namespace OAI

namespace SiegelZeros


namespace WeightedTorusJets

theorem greedyPivots_ringEquiv {K L ι : Type*} [Field K] [Field L] [Fintype ι]
    (e : K ≃+* L) (v : ℕ → ι → K) (T : ℕ) :
    greedyPivots L (fun i => e ∘ v i) T = greedyPivots K v T := by
  let : Algebra K L := e.toRingHom.toAlgebra
  exact greedyPivots_algebraMap (L := L) v T

theorem source_greedy_indices_transport {K L ι α : Type*}
    [Field K] [Field L] [Fintype ι]
    (e : K ≃+* L) (R : α → ι → K) (R' : α → ι → L)
    (hR : ∀ a j, e (R a j) = R' a j) (order : ℕ → α) (T : ℕ) :
    greedyPivots L (R' ∘ order) T = greedyPivots K (R ∘ order) T := by
  have h : R' ∘ order = fun i => e ∘ (R ∘ order) i := by
    funext i j
    exact (hR (order i) j).symm
  rw [h]
  exact greedyPivots_ringEquiv e (R ∘ order) T

end WeightedTorusJets


end SiegelZeros

end OAI
