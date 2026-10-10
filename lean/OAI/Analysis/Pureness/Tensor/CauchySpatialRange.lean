import OAI.Analysis.Pureness.Tensor.CauchySpatialEvaluation
import OAI.Analysis.Pureness.Quasitrace.QuasitraceProportionalMetric

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

def cauchySpatialAmbientProduct :
    representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype →⋆ₙₐ[ℂ]
      lp (fun _ : ℕ => E) ∞ :=
  boundedProductStarHom (fun n => (Φ.comp (T.cauchySpatialEval ht α δ hα n)).toNonUnitalStarAlgHom)

omit [PartialOrder E] [StarOrderedRing E] in
include hΦ in
lemma cauchySpatialAmbientProduct_tensor (u : T.cauchySequenceAlgebra ht)
    (b : ReducedFreeGroup) (n : ℕ) :
    T.cauchySpatialAmbientProduct ht α δ hα Φ
      (spatialCompletionMap α (reducedGroupAlgebra (FreeGroup ℕ)).subtype (u ⊗ₜ[ℂ] b)) n =
        l (u.1 n)*r b := by
  exact (congrArg Φ (T.cauchySpatialEval_tensor ht α δ hα n u b)).trans (hΦ (u.1 n) b)

omit [Nontrivial E] in
include hl in
lemma cauchySpatialAmbient_tmul_cauchy (u : T.cauchySequenceAlgebra ht) (b : ReducedFreeGroup) :
    U.IsMetricCauchy (fun n => l (u.1 n)*r b) := by
  have hc := T.isMetricCauchy_map_proportional U l.toNonUnitalStarAlgHom c hl u.2
  change U.IsMetricCauchy (fun n => l (u.1 n)) at hc
  unfold IsMetricCauchy at hc
  refine squeeze_zero (fun p => U.distance_nonneg _ _) (fun p => ?_)
    (show Tendsto (fun p : ℕ × ℕ => U.distance (l (u.1 p.1)) (l (u.1 p.2))*‖r b‖^(2/3:ℝ))
      atTop (nhds 0) by simpa only [zero_mul] using hc.mul_const (‖r b‖^(2/3:ℝ)))
  change U.metricSize (l (u.1 p.1)*r b-l (u.1 p.2)*r b) ≤ _
  rw [← sub_mul]
  exact U.metricSize_mul_le_right _ _

include hΦ hl in

lemma cauchySpatialAmbientProduct_mem
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype) :
    T.cauchySpatialAmbientProduct ht α δ hα Φ x ∈ U.cauchySequenceAlgebra hu := by
  let F := T.cauchySpatialAmbientProduct ht α δ hα Φ
  have hcont : Continuous F := by
    exact AddMonoidHomClass.continuous_of_bound F 1
      (by simpa only [one_mul] using! NonUnitalStarAlgHom.nnnorm_apply_le F)
  have hc : IsClosed {x | T.cauchySpatialAmbientProduct ht α δ hα Φ x ∈ U.cauchySequenceAlgebra hu} :=
    (U.cauchySequenceAlgebra_isClosed hu).preimage
      hcont
  have hd := representedSpatialTensor_dense α (reducedGroupAlgebra (FreeGroup ℕ)).subtype
  refine hd.induction_on x hc ?_
  intro z
  change T.cauchySpatialAmbientProduct ht α δ hα Φ
    (spatialCompletionMap α (reducedGroupAlgebra (FreeGroup ℕ)).subtype z) ∈ U.cauchySequenceAlgebra hu
  induction z using TensorProduct.inductionOn with
  | tmul u b =>
    change U.IsMetricCauchy (fun n =>
      T.cauchySpatialAmbientProduct ht α δ hα Φ
        (spatialCompletionMap α (reducedGroupAlgebra (FreeGroup ℕ)).subtype (u ⊗ₜ[ℂ] b)) n)
    rw [show (fun n => T.cauchySpatialAmbientProduct ht α δ hα Φ
      (spatialCompletionMap α (reducedGroupAlgebra (FreeGroup ℕ)).subtype (u ⊗ₜ[ℂ] b)) n) =
        (fun n => l (u.1 n)*r b) from funext
          (T.cauchySpatialAmbientProduct_tensor ht α δ hα Φ l r hΦ u b)]
    exact T.cauchySpatialAmbient_tmul_cauchy U ht l r c hl u b
  | add z w hz hw =>
    have he := (congrArg F (_root_.map_add
      (spatialCompletionMap α (reducedGroupAlgebra (FreeGroup ℕ)).subtype) z w)).trans
      (_root_.map_add F _ _)
    exact he.symm ▸ U.isMetricCauchy_add hu hz hw

def cauchySpatialAmbientSequence :
    representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype →⋆ₙₐ[ℂ]
      U.cauchySequenceAlgebra hu :=
  { toFun := fun x => ⟨T.cauchySpatialAmbientProduct ht α δ hα Φ x,
      T.cauchySpatialAmbientProduct_mem U ht hu α δ hα Φ l r hΦ c hl x⟩
    map_zero' := Subtype.ext (_root_.map_zero _)
    map_add' := fun x y => Subtype.ext (map_add _ x y)
    map_mul' := fun x y => Subtype.ext (map_mul _ x y)
    map_smul' := fun z x => Subtype.ext (_root_.map_smul _ z x)
    map_star' := fun x => Subtype.ext (map_star _ x) }
end CuntzPureness.PositiveQuasitrace

end

end OAI
