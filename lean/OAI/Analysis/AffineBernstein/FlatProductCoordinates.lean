import Mathlib
import OAI.Analysis.AffineBernstein.Basic

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E F : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

def flatProductCoordinates {n : ℕ} (bS : OrthonormalBasis ι ℝ S)
    (bF : OrthonormalBasis κ ℝ F) (e : Fin n ≃ ι ⊕ κ) : Space n ≃L[ℝ] (S × F) :=
  (((bS.prod bF).reindex e.symm).repr.symm.toContinuousLinearEquiv).trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ S F)

def flatProductFiberBasis (bF : OrthonormalBasis κ ℝ F)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) : OrthonormalBasis (κ ⊕ Unit) ℝ E :=
  (bF.prod (OrthonormalBasis.singleton Unit ℝ)).map f

def flatProductEmbedding (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) : (S × F) →L[ℝ] (S × E) :=
  (ContinuousLinearMap.fst ℝ S F).prod
    (f.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.inl ℝ F ℝ).comp (ContinuousLinearMap.snd ℝ S F))))

@[simp] lemma flatProductEmbedding_apply (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (q : S × F) :
    flatProductEmbedding f q = (q.1, f (WithLp.toLp 2 (q.2,0))) := rfl

@[simp] lemma flatProductFiberBasis_last (bF : OrthonormalBasis κ ℝ F)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) :
    flatProductFiberBasis bF f (Sum.inr ()) = f (WithLp.toLp 2 (0,(1:ℝ))) := by
  simp [flatProductFiberBasis,OrthonormalBasis.map_apply,OrthonormalBasis.prod_apply]

@[simp] lemma flatProductFiberBasis_first (bF : OrthonormalBasis κ ℝ F)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (j : κ) :
    flatProductFiberBasis bF f (Sum.inl j) = f (WithLp.toLp 2 (bF j,0)) := by
  simp [flatProductFiberBasis,OrthonormalBasis.map_apply,OrthonormalBasis.prod_apply]

lemma flatProductEmbedding_injective (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) :
    Function.Injective (flatProductEmbedding (S:=S) f) := by
  intro q r h
  have h₁ := congrArg Prod.fst h
  have h₂ := f.injective (congrArg Prod.snd h)
  exact Prod.ext h₁ (congrArg (fun z : WithLp 2 (F × ℝ) => (WithLp.ofLp z).1) h₂)

lemma flatProductEmbedding_vertical (bF : OrthonormalBasis κ ℝ F)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (q : S × F) :
    inner ℝ (flatProductEmbedding f q).2 (flatProductFiberBasis bF f (Sum.inr ())) = 0 := by
  rw [flatProductEmbedding_apply,flatProductFiberBasis_last,f.inner_map_map]
  simp [WithLp.prod_inner_apply]

lemma flatProductCoordinates_basis {n : ℕ} (bS : OrthonormalBasis ι ℝ S)
    (bF : OrthonormalBasis κ ℝ F) (e : Fin n ≃ ι ⊕ κ) (i : Fin n) :
    flatProductCoordinates bS bF e (coordinateVector n i) =
      Sum.elim (fun j => (bS j,(0:F))) (fun j => ((0:S),bF j)) (e i) := by
  have h := ((bS.prod bF).reindex e.symm).repr_symm_single i
  change (WithLp.ofLp (((bS.prod bF).reindex e.symm).repr.symm (EuclideanSpace.single i 1))) = _
  rw [h,OrthonormalBasis.reindex_apply]
  simp only [Equiv.symm_symm]
  rcases e i with j | j <;> simp [OrthonormalBasis.prod_apply]

lemma flatProductEmbedding_affine (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (q : S × F) :
    ((0:S),f (WithLp.toLp 2 (0,(1:ℝ)))) + flatProductEmbedding f q =
      (q.1,f (WithLp.toLp 2 (q.2,(1:ℝ)))) := by
  rw [flatProductEmbedding_apply]
  apply Prod.ext
  · simp
  · change f (WithLp.toLp 2 (0,(1:ℝ))) + f (WithLp.toLp 2 (q.2,0)) = _
    rw [← map_add]
    congr 1
    change WithLp.toLp 2 ((0:F)+q.2,(1:ℝ)+0) = _
    simp

lemma flatProductCoordinates_measurePreserving [FiniteDimensional ℝ S] [FiniteDimensional ℝ F]
    [MeasurableSpace S] [BorelSpace S] [MeasurableSpace F] [BorelSpace F]
    {n : ℕ} (bS : OrthonormalBasis ι ℝ S) (bF : OrthonormalBasis κ ℝ F)
    (e : Fin n ≃ ι ⊕ κ) : MeasurePreserving (flatProductCoordinates bS bF e) := by
  exact (WithLp.volume_preserving_ofLp S F).comp
    (((bS.prod bF).reindex e.symm).repr.symm.measurePreserving)

end AffineBernstein
end

end OAI
