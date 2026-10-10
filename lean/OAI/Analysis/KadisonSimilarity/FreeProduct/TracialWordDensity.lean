import OAI.Analysis.KadisonSimilarity.Representation.CenteredBaseDensity
import OAI.Analysis.KadisonSimilarity.FreeProduct.ReducedWordModel
import OAI.Analysis.KadisonSimilarity.Tensor.TensorPacketDensity

namespace OAI

/-! Equality of bounded word maps can be tested on actual bounded algebra
letters. This bridges the published product formula to completed word actions. -/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

attribute [local irreducible] tensorWordSpace TracialCornerGeometry.baseSpace

variable {P H K : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

local instance baseANormed : NormedAddCommGroup (G.baseSpace A) := inferInstance
local instance baseAInner : InnerProductSpace ℂ (G.baseSpace A) := inferInstance
local instance baseDNormed : NormedAddCommGroup (G.baseSpace D) := inferInstance
local instance baseDInner : InnerProductSpace ℂ (G.baseSpace D) := inferInstance
local instance centeredANormed : NormedAddCommGroup (centeredSubspace (G.baseVector A 1)) :=
  inferInstance
local instance centeredAInner : InnerProductSpace ℂ (centeredSubspace (G.baseVector A 1)) :=
  inferInstance
local instance centeredDNormed : NormedAddCommGroup (centeredSubspace (G.baseVector D 1)) :=
  inferInstance
local instance centeredDInner : InnerProductSpace ℂ (centeredSubspace (G.baseVector D 1)) :=
  inferInstance

/-- Bounded algebra vectors determine every continuous map on a word level. -/
theorem continuousLinearMap_ext_tracialWordTensors (hτ : G.trace 1 = 1) (n : ℕ)
    (f g : HilbertTensor
      (HilbertTensor (CompletedTensorWord (centeredSubspace (G.baseVector A 1)) n)
        (G.baseSpace A))
      (EndpointTensor (G.baseSpace D) (centeredSubspace (G.baseVector D 1)) n) →L[ℂ] K)
    (h : ∀ (d : D) (b : A) (a : Fin n → A) (c : Fin n → D)
      (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0),
      f (tracialWordTensor G A D n d b a c ha hc) =
        g (tracialWordTensor G A D n d b a c ha hc)) : f = g := by
  refine continuousLinearMap_ext_denseTensorPackets
    (X := centeredSubspace (G.baseVector A 1)) (B := G.baseSpace A)
    (E := G.baseSpace D) (F := centeredSubspace (G.baseVector D 1)) (n := n) (K := K)
    (G.centeredBaseAlgebraVector A) (G.baseVector A) (G.baseVector D)
    (G.centeredBaseAlgebraVector D) ?_ ?_ ?_ ?_ _ _ ?_
  · exact G.centeredBaseAlgebraVector_dense A hτ
  · exact G.baseVector_dense A
  · exact G.baseVector_dense D
  · exact G.centeredBaseAlgebraVector_dense D hτ
  · intro a b d c
    exact h d b (fun i => (a i).val) (fun i => (c i).val)
      (fun i => (a i).property) (fun i => (c i).property)

/-- Equality on bounded algebra words determines a continuous map on the
completed word space. -/
theorem function_ext_tracialWordTensors (hτ : G.trace 1 = 1) (n : ℕ)
    (p q : HilbertTensor
      (HilbertTensor (CompletedTensorWord (centeredSubspace (G.baseVector A 1)) n)
        (G.baseSpace A))
      (EndpointTensor (G.baseSpace D) (centeredSubspace (G.baseVector D 1)) n) → K)
    (hp : Continuous p) (hq : Continuous q)
    (hpadd : ∀ x y, p (x + y) = p x + p y) (hqadd : ∀ x y, q (x + y) = q x + q y)
    (hpsmul : ∀ (c : ℂ) x, p (c • x) = c • p x)
    (hqsmul : ∀ (c : ℂ) x, q (c • x) = c • q x)
    (h : ∀ (d : D) (b : A) (a : Fin n → A) (c : Fin n → D)
      (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0),
      p (tracialWordTensor G A D n d b a c ha hc) =
        q (tracialWordTensor G A D n d b a c ha hc)) : p = q := by
  let fp : HilbertTensor
      (HilbertTensor (CompletedTensorWord (centeredSubspace (G.baseVector A 1)) n)
        (G.baseSpace A))
      (EndpointTensor (G.baseSpace D) (centeredSubspace (G.baseVector D 1)) n) →L[ℂ] K :=
    { toFun := p, map_add' := hpadd, map_smul' := hpsmul, cont := hp }
  let fq : HilbertTensor
      (HilbertTensor (CompletedTensorWord (centeredSubspace (G.baseVector A 1)) n)
        (G.baseSpace A))
      (EndpointTensor (G.baseSpace D) (centeredSubspace (G.baseVector D 1)) n) →L[ℂ] K :=
    { toFun := q, map_add' := hqadd, map_smul' := hqsmul, cont := hq }
  exact congrArg DFunLike.coe
    (G.continuousLinearMap_ext_tracialWordTensors A D hτ n fp fq h)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
