import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.EndpointRegrouping

namespace OAI


noncomputable section
namespace JiangSuConstruction
open scoped Kronecker ComplexOrder CStarAlgebra

variable {p q : ℕ}

def zeroReducedEquiv (m : Multiplicities p q) :
    ((Fin p×Fin (m.k-q*m.delta)) ⊕ ((Fin p×Fin q)×Fin m.delta)) ≃ Fin (p*m.k) :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using m.zero_reduced)
def zeroTensorEquiv (m : Multiplicities p q) : (Fin q×Fin m.l) ≃ Fin (q*m.l) :=
  Fintype.equivOfCardEq (by simp)
def oneReducedEquiv (m : Multiplicities p q) :
    ((Fin q×Fin (m.l-p*m.gamma)) ⊕ ((Fin p×Fin q)×Fin m.gamma)) ≃ Fin (q*m.l) :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using m.one_reduced)
def oneTensorEquiv (m : Multiplicities p q) : (Fin p×Fin m.k) ≃ Fin (p*m.k) :=
  Fintype.equivOfCardEq (by simp)

def zeroIndexEquiv (m : Multiplicities p q) :
    ((Fin p×Fin q)×SpectralIndex m) ≃ (Fin (p*m.k)×Fin (q*m.l)) :=
  (Equiv.prodCongr (Equiv.refl _) (zeroBlockEquiv m)).trans
    (endpointLeftEquiv.trans (Equiv.prodCongr (zeroReducedEquiv m) (zeroTensorEquiv m)))
def oneIndexEquiv (m : Multiplicities p q) :
    ((Fin p×Fin q)×SpectralIndex m) ≃ (Fin (p*m.k)×Fin (q*m.l)) :=
  (Equiv.prodCongr (Equiv.refl _) (oneBlockEquiv m)).trans
    (endpointRightEquiv.trans (Equiv.prodCongr (oneTensorEquiv m) (oneReducedEquiv m)))

lemma zeroIndex_endpoint (m : Multiplicities p q) (f : DimensionDrop p q) :
    CStarMatrix.reindexₐ ℂ ℂ (zeroIndexEquiv m)
      (blockDiagonalHom (fun z => (f : C(Interval,TensorMat p q)) (spectralFamily m z leftEndpoint))) ∈
        (leftAmplification (p*m.k) (q*m.l)).range := by
  obtain ⟨a,ha⟩ := f.2.1
  have hfamily : (fun z => (f : C(Interval,TensorMat p q))
      (spectralFamily m ((zeroBlockEquiv m).symm z) leftEndpoint)) =
      (fun z => match z with
        | Sum.inl _ => leftAmplification p q a
        | Sum.inr _ => (f : C(Interval,TensorMat p q)) midpoint) := by
    funext z
    rw [spectralFamily_zero]
    cases z
    · exact ha.symm
    · rfl
  unfold zeroIndexEquiv
  rw [reindex_trans,reindex_blockDiagonal,hfamily,reindex_trans]
  change CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr (zeroReducedEquiv m) (zeroTensorEquiv m))
    (CStarMatrix.reindexₐ ℂ ℂ endpointLeftEquiv (blockDiagonalHom (fun z => match z with
      | Sum.inl _ => CStarMatrix.ofMatrix (CStarMatrix.ofMatrix.symm a ⊗ₖ (1 : Matrix (Fin q) (Fin q) ℂ))
      | Sum.inr _ => (f : C(Interval,TensorMat p q)) midpoint))) ∈ _
  have he := congrArg (CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr (zeroReducedEquiv m) (zeroTensorEquiv m)))
    (endpoint_left_regroup (α := Fin (m.k-q*m.delta)) (β := Fin m.delta)
      (ν := Fin m.l) a ((f : C(Interval,TensorMat p q)) midpoint))
  rw [reindex_left_amplification] at he
  refine ⟨CStarMatrix.reindexₐ ℂ ℂ (zeroReducedEquiv m) (endpointReduced a ((f : C(Interval,TensorMat p q)) midpoint)), ?_⟩
  convert he.symm using 1
  · congr 2
    apply congrArg blockDiagonalHom
    funext index
    cases index <;> rfl

lemma oneIndex_endpoint (m : Multiplicities p q) (f : DimensionDrop p q) :
    CStarMatrix.reindexₐ ℂ ℂ (oneIndexEquiv m)
      (blockDiagonalHom (fun z => (f : C(Interval,TensorMat p q)) (spectralFamily m z rightEndpoint))) ∈
        (rightAmplification (p*m.k) (q*m.l)).range := by
  obtain ⟨a,ha⟩ := f.2.2
  have hfamily : (fun z => (f : C(Interval,TensorMat p q))
      (spectralFamily m ((oneBlockEquiv m).symm z) rightEndpoint)) =
      (fun z => match z with
        | Sum.inl _ => rightAmplification p q a
        | Sum.inr _ => (f : C(Interval,TensorMat p q)) midpoint) := by
    funext z
    rw [spectralFamily_one]
    cases z
    · exact ha.symm
    · rfl
  unfold oneIndexEquiv
  rw [reindex_trans,reindex_blockDiagonal,hfamily,reindex_trans]
  change CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr (oneTensorEquiv m) (oneReducedEquiv m))
    (CStarMatrix.reindexₐ ℂ ℂ endpointRightEquiv (blockDiagonalHom (fun z => match z with
      | Sum.inl _ => CStarMatrix.ofMatrix ((1 : Matrix (Fin p) (Fin p) ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm a)
      | Sum.inr _ => (f : C(Interval,TensorMat p q)) midpoint))) ∈ _
  have he := congrArg (CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr (oneTensorEquiv m) (oneReducedEquiv m)))
    (endpoint_right_regroup (α := Fin (m.l-p*m.gamma)) (β := Fin m.gamma)
      (ν := Fin m.k) a ((f : C(Interval,TensorMat p q)) midpoint))
  rw [reindex_right_amplification] at he
  refine ⟨CStarMatrix.reindexₐ ℂ ℂ (oneReducedEquiv m) (endpointRightReduced a ((f : C(Interval,TensorMat p q)) midpoint)), ?_⟩
  convert he.symm using 1
  · congr 2
    apply congrArg blockDiagonalHom
    funext index
    cases index <;> rfl

def concreteStep (m : Multiplicities p q) :
    DimensionDrop p q →⋆ₐ[ℂ] DimensionDrop (p*m.k) (q*m.l) :=
  connectingMap (spectralFamily m) (zeroIndexEquiv m)
    (permutationUnitary ((zeroIndexEquiv m).symm.trans (zeroIndexEquiv m)))
    (permutationUnitary ((zeroIndexEquiv m).symm.trans (oneIndexEquiv m)))
    (fun f => by rw [permutation_after_reindex]; exact zeroIndex_endpoint m f)
    (fun f => by rw [permutation_after_reindex]; exact oneIndex_endpoint m f)

theorem concreteStep_injective (m : Multiplicities p q) : Function.Injective (concreteStep m) := by
  obtain ⟨z,hz⟩ := spectralFamily_surjective m
  exact connectingMap_injective _ _ _ _ _ _ z hz

end JiangSuConstruction

end

end OAI
