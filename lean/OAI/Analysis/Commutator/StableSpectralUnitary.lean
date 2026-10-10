import Mathlib
import OAI.Analysis.Commutator.CyclicSpectralUnitary
import OAI.Analysis.Commutator.InfiniteUnitary
import OAI.Analysis.Commutator.L2InfiniteSumCoordinates

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory

open scoped Topology InnerProductSpace

namespace Kadison.CyclicSpectral

open InfiniteAmplification Decomposable

variable {Ω H G : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [CompactSpace Ω]
  [BorelSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

def stableUnitary (W : Space ℕ H ≃ₗᵢ[ℂ] Space ℕ G) (V : Lp ℂ 2 μ ≃ₗᵢ[ℂ] G) :
    Space ℕ H ≃ₗᵢ[ℂ] Lp (Space ℕ ℂ) 2 μ :=
  W.trans ((mapEquiv (ι:=ℕ) V.symm).trans (infiniteSumEquiv (ι:=ℕ) μ))

lemma stableUnitary_intertwines (W : Space ℕ H ≃ₗᵢ[ℂ] Space ℕ G) (V : Lp ℂ 2 μ ≃ₗᵢ[ℂ] G)
    (S : H →L[ℂ] H) (T : G →L[ℂ] G) (f : C(Ω,ℂ))
    (hW : ∀ x,W (map S x)=map T (W x))
    (hV : ∀ x,V (scalarMultiplier μ f x)=T (V x)) (v : Space ℕ H) :
    stableUnitary μ W V (map S v)=scalarVectorMultiplier μ f (stableUnitary μ W V v) := by
  change infiniteSumEquiv μ (mapEquiv V.symm (W (map S v)))=_
  rw [hW]
  have he : ∀ x,V.symm (T x)=scalarMultiplier μ f (V.symm x) := by
    intro x
    apply V.injective
    rw [V.apply_symm_apply,hV,V.apply_symm_apply]
  rw [mapEquiv_intertwines V.symm _ _ he]
  exact infiniteSumEquiv_scalar μ f _

end Kadison.CyclicSpectral

end

end
end

end OAI
