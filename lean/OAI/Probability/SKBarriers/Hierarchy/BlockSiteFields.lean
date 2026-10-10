import Mathlib
import OAI.Probability.SKBarriers.Interpolation.FinitePressureAlgebra
import OAI.Probability.SKBarriers.Hierarchy.BlockEndpoints
import OAI.Probability.SKBarriers.Scalar.EmbeddedSites
import OAI.Probability.SKBarriers.Hierarchy.BlockSiteEmbedding

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {A S : Type} [Fintype A] [Nonempty A] [Fintype S] [Nonempty S]

def siteBlockObservables {N r k : ℕ} (V : Fin ((k+1)*r) → A → ℝ) :
    Fin (k+1) → Fin (N*r) → (Fin N → A) → ℝ :=
  fun b p s => V (finProdFinEquiv (b,(finProdFinEquiv.symm p).2)) (s (finProdFinEquiv.symm p).1)

omit [Fintype A] [Nonempty A] [Fintype S] [Nonempty S] in
theorem siteBlock_fields_sum {D N r k : ℕ} (V : Fin ((k+1)*r) → A → ℝ)
    (s : Fin N → A) (z : ParameterSpace (blockDimension D (N*r) k)) :
    (∑ b, ∑ p, siteBlockObservables V b p s*
      coordinateProjection (blockDimension D (N*r) k) (fieldIndex D (N*r) k b p) z)=
      (∑ i, embeddedSiteExponent (blockSiteEmbedding D N r k i) V (s i)) z := by
  simp only [sum_apply,embeddedSiteExponent,smul_apply,smul_eq_mul]
  have he (b : Fin (k+1)) : (∑ p, siteBlockObservables V b p s*
      coordinateProjection (blockDimension D (N*r) k) (fieldIndex D (N*r) k b p) z)=
      ∑ i, ∑ u, V (finProdFinEquiv (b,u)) (s i)*
        coordinateProjection (blockDimension D (N*r) k) (fieldIndex D (N*r) k b (finProdFinEquiv (i,u))) z := by
    rw [← finProdFinEquiv.sum_comp (fun p : Fin (N*r) => siteBlockObservables V b p s*
      coordinateProjection (blockDimension D (N*r) k) (fieldIndex D (N*r) k b p) z)]
    simp only [siteBlockObservables,Equiv.symm_apply_apply,Fintype.sum_prod_type]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← finProdFinEquiv.sum_comp (fun j : Fin ((k+1)*r) =>
    V j (s i)*coordinateProjection (blockDimension D (N*r) k) (blockSiteEmbedding D N r k i j) z)]
  simp only [Fintype.sum_prod_type,blockSiteEmbedding_apply]

theorem siteBlock_root_zero_le {D N r k : ℕ} (hN : 0<N)
    (e : S → Fin N → A) (he : Function.Injective e)
    (H : Fin D → S → ℝ) (V : Fin ((k+1)*r) → A → ℝ)
    (c : A → ℝ) (w : Fin (k+1) → ℝ) (hw : ∀ b, 0 ≤ w b) :
    hierarchyPressure (blockDimension D (N*r) k) (weightedBlockMass D (N*r) k w)
      (affineLogPartition (fun s => ∑ i, c (e s i))
        (observableExponent (blockDimension D (N*r) k)
          (blockObservable H (fun b p s => siteBlockObservables V b p (e s)))
          (interpolationCoefficient (blockDimension D (N*r) k) (blockInterpolationChoice D (N*r) k) 0))) 0 ≤
      (N:ℝ)*vectorHierarchy ((k+1)*r) (siteBlockMass r k w) V (siteValueTerminal c) 0 := by
  let L : (Fin N → A) → ParameterSpace (blockDimension D (N*r) k) →L[ℝ] ℝ :=
    fun s => ∑ i, embeddedSiteExponent (blockSiteEmbedding D N r k i) V (s i)
  have hL : observableExponent (blockDimension D (N*r) k)
      (blockObservable H (fun b p s => siteBlockObservables V b p (e s)))
      (interpolationCoefficient (blockDimension D (N*r) k) (blockInterpolationChoice D (N*r) k) 0)=L ∘ e := by
    funext s
    ext z
    rw [blockObservable_endpoint_zero]
    exact siteBlock_fields_sum V (e s) z
  rw [hL]
  have hmon := hierarchyPressure_mono (blockDimension D (N*r) k) (weightedBlockMass D (N*r) k w)
    (fun i => massFromAtoms_nonneg _ _ (weightedBlockAtom_nonneg D (N*r) k w hw) i)
    (affineLogPartition_boundedDerivs (fun s => ∑ i, c (e s i)) (L ∘ e))
    (affineLogPartition_boundedDerivs (fun s : Fin N → A => ∑ i, c (s i)) L)
    (fun z => affineLogPartition_restrict e he (fun s : Fin N → A => ∑ i, c (s i)) L z) 0
  have ht := embeddedSites_tensorizes (fun i => blockSiteEmbedding D N r k i)
    (fun i => blockSiteEmbedding_strictMono D N r k i)
    (blockSiteOwner (D:=D) (r:=r) (k:=k) ⟨0,hN⟩)
    (fun i j => blockSiteOwner_embedding ⟨0,hN⟩ i j)
    (weightedBlockMass D (N*r) k w) (siteBlockMass r k w)
    (fun i j => blockSiteEmbedding_mass D N r k w i j) V c 0
  exact hmon.trans_eq (by simpa only [Fintype.card_fin,L] using ht)
end

end SK.Analytic

end
end

end OAI
