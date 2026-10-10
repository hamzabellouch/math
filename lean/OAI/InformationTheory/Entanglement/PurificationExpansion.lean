import OAI.InformationTheory.Entanglement.PurificationSupport
import OAI.InformationTheory.Entanglement.HilbertEmbeddingOrder

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder
open Matrix ContinuousLinearMap
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {n : Type} [Fintype n] [DecidableEq n]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [DecidableEq n] [CompleteSpace H] in
theorem purification_orthonormal_expansion (x : n→H) :
    ∃ d : ℕ, ∃ v : Fin d→H, ∃ B : Matrix (Fin d) n ℂ,
      Orthonormal ℂ v ∧ (∀ j, ∑ i, B i j • v i=x j) ∧
      (∀ i j, (Bᴴ*B) i j=inner ℂ (x i) (x j)) := by
  obtain ⟨d,V,B,hx,hg⟩ := purification_finite_span x
  let e := EuclideanSpace.basisFun (Fin d) ℂ
  let v := fun i => V (e i)
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show inner ℂ (v i) (v j)=inner ℂ (e i) (e j) from V.inner_map_map _ _]
    exact orthonormal_iff_ite.mp e.orthonormal i j
  refine ⟨d,v,B,hv,?_,hg⟩
  intro j
  calc
    _=V (∑ i, B i j • e i) := by simp only [map_sum,map_smul]; rfl
    _=V (WithLp.toLp 2 (fun i => B i j)) := by
      congr 1
      simpa only [e,EuclideanSpace.basisFun_repr,WithLp.ofLp_toLp] using
        e.sum_repr (WithLp.toLp 2 (fun i => B i j))
    _=x j := hx j

end SecretKey

end

end OAI
