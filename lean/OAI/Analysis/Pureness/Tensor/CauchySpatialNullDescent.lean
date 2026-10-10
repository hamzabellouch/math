import OAI.Analysis.Pureness.Tensor.CauchySpatialRange
import OAI.Analysis.Pureness.Quasitrace.QuasitraceProportionalFunctor
import OAI.Analysis.Pureness.GroupAlgebra.CauchyFreeGroupExactness

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped TensorProduct Topology ENNReal NNReal
variable {D E H L : Type*}
variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E] [Nontrivial E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (T : CuntzPureness.PositiveQuasitrace D) (U : CuntzPureness.PositiveQuasitrace E)
variable (ht : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hu : ∀ x y, U.metricSize (x+y) ≤ U.metricSize x+U.metricSize y)
variable (α : T.cauchySequenceAlgebra ht →⋆ₐ[ℂ] (H →L[ℂ] H))
variable (δ : D →⋆ₐ[ℂ] (L →L[ℂ] L)) (hα : Function.Injective α)
variable (Φ : representedSpatialTensor δ (reducedGroupAlgebra (FreeGroup ℕ)).subtype →⋆ₐ[ℂ] E)
variable (l : D →⋆ₐ[ℂ] E) (r : ReducedFreeGroup →⋆ₐ[ℂ] E)
variable (hΦ : ∀ a b, Φ (spatialCompletionMap δ
  (reducedGroupAlgebra (FreeGroup ℕ)).subtype (a ⊗ₜ[ℂ] b)) = l a*r b)
variable (c : ℝ≥0) (hl : ∀ a, U (Positive.map l.toNonUnitalStarAlgHom a) = (c : ℝ)*T a)

lemma cauchySpatialAmbientSequence_one :
    T.cauchySpatialAmbientSequence U ht hu α δ hα Φ l r hΦ c hl 1 = 1 := by
  apply Subtype.ext
  apply lp.ext
  funext n
  exact (Φ.comp (T.cauchySpatialEval ht α δ hα n)).map_one

def cauchySpatialAmbientSequenceHom :
    representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype →⋆ₐ[ℂ]
      U.cauchySequenceAlgebra hu where
  toFun := T.cauchySpatialAmbientSequence U ht hu α δ hα Φ l r hΦ c hl
  map_zero' := _root_.map_zero (T.cauchySpatialAmbientSequence U ht hu α δ hα Φ l r hΦ c hl)
  map_add' := _root_.map_add (T.cauchySpatialAmbientSequence U ht hu α δ hα Φ l r hΦ c hl)
  map_mul' := _root_.map_mul (T.cauchySpatialAmbientSequence U ht hu α δ hα Φ l r hΦ c hl)
  map_one' := T.cauchySpatialAmbientSequence_one U ht hu α δ hα Φ l r hΦ c hl
  commutes' z := by
    apply Subtype.ext
    apply lp.ext
    funext n
    exact (Φ.comp (T.cauchySpatialEval ht α δ hα n)).commutes z
  map_star' := map_star (T.cauchySpatialAmbientSequence U ht hu α δ hα Φ l r hΦ c hl)

def cauchySpatialAmbientQuotient :
    representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype →⋆ₐ[ℂ]
      U.CauchyQuotient hu :=
  (U.cauchyQuotientStarHom hu).comp
    (T.cauchySpatialAmbientSequenceHom U ht hu α δ hα Φ l r hΦ c hl)

lemma cauchySpatialAmbientQuotient_null_tensor (u : T.cauchySequenceAlgebra ht)
    (hn : T.IsMetricNull (fun n => u.1 n)) (b : ReducedFreeGroup) :
    T.cauchySpatialAmbientQuotient U ht hu α δ hα Φ l r hΦ c hl
      (spatialCompletionMap α (reducedGroupAlgebra (FreeGroup ℕ)).subtype (u ⊗ₜ[ℂ] b)) = 0 := by
  apply (U.cauchyQuotientStarHom_eq_zero_iff hu _).mpr
  change U.IsMetricNull (fun n =>
    T.cauchySpatialAmbientProduct ht α δ hα Φ
      (spatialCompletionMap α (reducedGroupAlgebra (FreeGroup ℕ)).subtype (u ⊗ₜ[ℂ] b)) n)
  rw [show (fun n => T.cauchySpatialAmbientProduct ht α δ hα Φ
    (spatialCompletionMap α (reducedGroupAlgebra (FreeGroup ℕ)).subtype (u ⊗ₜ[ℂ] b)) n) =
      (fun n => l (u.1 n)*r b) from funext
        (T.cauchySpatialAmbientProduct_tensor ht α δ hα Φ l r hΦ u b)]
  exact U.isMetricNull_mul_right
    (T.isMetricNull_map_proportional U l.toNonUnitalStarAlgHom c hl hn)
    ‖r b‖ (norm_nonneg _) (fun _ => le_rfl)

lemma cauchySpatialAmbientQuotient_ideal_zero
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype)
    (hx : x ∈ (spatialTensorKernelIdeal (T.cauchyQuotientStarHom ht) α
      (reducedGroupAlgebra (FreeGroup ℕ)).subtype).ideal) :
    T.cauchySpatialAmbientQuotient U ht hu α δ hα Φ l r hΦ c hl x = 0 := by
  change x ∈ ((spatialTensorKernelIdeal (T.cauchyQuotientStarHom ht) α
    (reducedGroupAlgebra (FreeGroup ℕ)).subtype).ideal : Set _) at hx
  rw [T.cauchyFreeGroupTensorIdeal_coe ht α] at hx
  let F := T.cauchySpatialAmbientQuotient U ht hu α δ hα Φ l r hΦ c hl
  have hc : Continuous F := AddMonoidHomClass.continuous_of_bound F 1
    (by simpa only [one_mul] using! NonUnitalStarAlgHom.nnnorm_apply_le F)
  refine closure_minimal ?_ (isClosed_eq hc continuous_const) hx
  rintro _ ⟨z,rfl⟩
  let k := F.toLinearMap.comp ((spatialCompletionMap α
    (reducedGroupAlgebra (FreeGroup ℕ)).subtype).toLinearMap.comp
      (TensorProduct.map (T.nullSequenceSubmodule ht).subtype
        (LinearMap.id : ReducedFreeGroup →ₗ[ℂ] ReducedFreeGroup)))
  change k z = 0
  induction z using TensorProduct.inductionOn with
  | tmul u b =>
    change F (spatialCompletionMap α (reducedGroupAlgebra (FreeGroup ℕ)).subtype (u.1 ⊗ₜ[ℂ] b)) = 0
    exact T.cauchySpatialAmbientQuotient_null_tensor U ht hu α δ hα Φ l r hΦ c hl
      u.1 ((T.cauchyQuotientStarHom_eq_zero_iff ht u.1).mp u.2) b
  | add z w hz hw =>
    exact (k.map_add z w).trans (by rw [hz,hw,add_zero])
end CuntzPureness.PositiveQuasitrace

end

end OAI
