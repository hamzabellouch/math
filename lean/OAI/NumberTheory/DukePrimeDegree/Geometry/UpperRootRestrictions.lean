import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootCoordinatesMeasure
import OAI.NumberTheory.PrimePackets.LeafNormalization

namespace OAI

/-!
# Compatible restrictions of full upper-root conditionals

Shrinking an actual upper-root quotient box restricts its coordinate
measure. The disintegrated kernels therefore agree projectively on
intersections, with the normalization fixed by a common smaller box.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets
namespace UpperRootBox
variable {n : ℕ} {g : G n}

lemma coordinateMeasure_apply (B : UpperRootBox n g) (μ : Measure (X n))
    {S : Set (UpperRootTransverse n × UpperRootTime n)} (hS : MeasurableSet S) :
    B.coordinateMeasure μ S =
      μ (upperRootQuotientParam n g '' (S ∩ B.domain)) := by
  rw [coordinateMeasure,Measure.map_apply measurable_subtype_coe hS,
    B.embedding.measurableEmbedding.comap_apply]
  congr 1
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z.val,⟨hz,z.prop⟩,rfl⟩
  · rintro ⟨z,⟨hz,hzd⟩,rfl⟩
    exact ⟨⟨z,hzd⟩,hz,rfl⟩



def shrink (B : UpperRootBox n g)
    (U : Set (UpperRootTransverse n)) (V : Set (UpperRootTime n)) (hU : IsOpen U) (hV : IsOpen V)
    (hUB : U ⊆ B.transverse) (hVB : V ⊆ B.time) : UpperRootBox n g :=
  ⟨U,V,hU,hV,B.embedding.comp (Topology.IsOpenEmbedding.inclusion
    (Set.prod_mono hUB hVB) ((hU.prod hV).preimage continuous_subtype_val))⟩



theorem shrink_coordinateMeasure (B : UpperRootBox n g)
    (U : Set (UpperRootTransverse n)) (V : Set (UpperRootTime n)) (hU : IsOpen U) (hV : IsOpen V)
    (hUB : U ⊆ B.transverse) (hVB : V ⊆ B.time) (μ : Measure (X n)) :
    (B.shrink U V hU hV hUB hVB).coordinateMeasure μ =
      (B.coordinateMeasure μ).restrict (U ×ˢ V) := by
  ext S hS
  rw [Measure.restrict_apply hS,coordinateMeasure_apply _ μ hS,
    coordinateMeasure_apply _ μ (hS.inter (hU.measurableSet.prod hV.measurableSet))]
  congr 2
  change S ∩ U ×ˢ V = (S ∩ U ×ˢ V) ∩ B.domain
  exact (Set.inter_eq_left.mpr ((Set.inter_subset_right).trans (Set.prod_mono hUB hVB))).symm



theorem shrink_conditionalKernel (B : UpperRootBox n g)
    (U : Set (UpperRootTransverse n)) (V : Set (UpperRootTime n)) (hU : IsOpen U) (hV : IsOpen V)
    (hUB : U ⊆ B.transverse) (hVB : V ⊆ B.time) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst.restrict U,
      B.conditionalKernel μ s V •
        (B.shrink U V hU hV hUB hVB).conditionalKernel μ s =
          (B.conditionalKernel μ s).restrict V := by
  simp only [conditionalKernel,shrink_coordinateMeasure]
  exact restricted_conditional_kernel _ hU.measurableSet hV.measurableSet



theorem shrink_marginal (B : UpperRootBox n g)
    (U : Set (UpperRootTransverse n)) (V : Set (UpperRootTime n)) (hU : IsOpen U) (hV : IsOpen V)
    (hUB : U ⊆ B.transverse) (hVB : V ⊆ B.time) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ((B.shrink U V hU hV hUB hVB).coordinateMeasure μ).fst =
      ((B.coordinateMeasure μ).fst.restrict U).withDensity
        (fun s => B.conditionalKernel μ s V) := by
  rw [shrink_coordinateMeasure,restricted_conditional_marginal _ hU.measurableSet hV.measurableSet]
  rfl

lemma shrink_marginal_absolutelyContinuous (B : UpperRootBox n g)
    (U : Set (UpperRootTransverse n)) (J : Set (UpperRootTime n)) (hU : IsOpen U) (hJ : IsOpen J)
    (hUB : U ⊆ B.transverse) (hJB : J ⊆ B.time) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ((B.shrink U J hU hJ hUB hJB).coordinateMeasure μ).fst ≪
      (B.coordinateMeasure μ).fst.restrict U := by
  rw [shrink_marginal]
  exact withDensity_absolutelyContinuous _ _

lemma shrink_marginal_ae_anchor_pos (B : UpperRootBox n g)
    (U : Set (UpperRootTransverse n)) (J : Set (UpperRootTime n)) (hU : IsOpen U) (hJ : IsOpen J)
    (hUB : U ⊆ B.transverse) (hJB : J ⊆ B.time) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ∀ᵐ s ∂((B.shrink U J hU hJ hUB hJB).coordinateMeasure μ).fst,
      B.conditionalKernel μ s J ≠ 0 := by
  rw [shrink_marginal]
  exact (ae_withDensity_iff (B.conditionalKernel μ |>.measurable_coe hJ.measurableSet)).mpr
    (ae_of_all _ fun _ h => h)



theorem overlap_anchorNormalize (B C : UpperRootBox n g)
    (U : Set (UpperRootTransverse n)) (J : Set (UpperRootTime n)) (hU : IsOpen U) (hJ : IsOpen J)
    (hUB : U ⊆ B.transverse) (hUC : U ⊆ C.transverse)
    (hJB : J ⊆ B.time) (hJC : J ⊆ C.time)
    (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ∀ᵐ s ∂((B.shrink U J hU hJ hUB hJB).coordinateMeasure μ).fst,
      B.conditionalKernel μ s J ≠ 0 ∧ C.conditionalKernel μ s J ≠ 0 ∧
      (anchorNormalize (B.conditionalKernel μ s) J).restrict (B.time ∩ C.time) =
        (anchorNormalize (C.conditionalKernel μ s) J).restrict (B.time ∩ C.time) := by
  let V := B.time ∩ C.time
  have hV : IsOpen V := B.time_open.inter C.time_open
  let D := B.shrink U V hU hV hUB inter_subset_left
  have hD : D = C.shrink U V hU hV hUC inter_subset_right := rfl
  have hA : B.shrink U J hU hJ hUB hJB = C.shrink U J hU hJ hUC hJC := rfl
  have hB := (B.shrink_marginal_absolutelyContinuous U J hU hJ hUB hJB μ).ae_le
    (B.shrink_conditionalKernel U V hU hV hUB inter_subset_left μ)
  have hC := (C.shrink_marginal_absolutelyContinuous U J hU hJ hUC hJC μ).ae_le
    (C.shrink_conditionalKernel U V hU hV hUC inter_subset_right μ)
  rw [←hA] at hC
  have hpB := B.shrink_marginal_ae_anchor_pos U J hU hJ hUB hJB μ
  have hpC := C.shrink_marginal_ae_anchor_pos U J hU hJ hUC hJC μ
  rw [←hA] at hpC
  filter_upwards [hB,hC,hpB,hpC] with s hsB hsC hpB hpC
  have hJV : J ⊆ V := subset_inter hJB hJC
  have H₁ := (anchorNormalize_restrict _ _ hJ.measurableSet hJV hsB hpB).2
  have H₂ := (anchorNormalize_restrict _ _ hJ.measurableSet hJV hsC hpC).2
  refine ⟨hpB,hpC,?_⟩
  exact H₁.symm.trans H₂


theorem overlap_anchorNormalize_restrict (B C : UpperRootBox n g)
    (U : Set (UpperRootTransverse n)) (J : Set (UpperRootTime n)) (hU : IsOpen U) (hJ : IsOpen J)
    (hUB : U ⊆ B.transverse) (hUC : U ⊆ C.transverse)
    (hJB : J ⊆ B.time) (hJC : J ⊆ C.time)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    {W : Set (UpperRootTime n)} (hW : MeasurableSet W) (hWB : W ⊆ B.time) (hWC : W ⊆ C.time) :
    ∀ᵐ s ∂((B.shrink U J hU hJ hUB hJB).coordinateMeasure μ).fst,
      (anchorNormalize (B.conditionalKernel μ s) J).restrict W =
        (anchorNormalize (C.conditionalKernel μ s) J).restrict W := by
  filter_upwards [overlap_anchorNormalize B C U J hU hJ hUB hUC hJB hJC μ] with s hs
  have H := congrArg (fun ξ : Measure (UpperRootTime n) => ξ.restrict W) hs.2.2
  simpa only [Measure.restrict_restrict hW,inter_eq_left.mpr (subset_inter hWB hWC)] using H

lemma shrink_full_time_marginal (B : UpperRootBox n g)
    (U : Set (UpperRootTransverse n)) (hU : IsOpen U) (hUB : U ⊆ B.transverse)
    (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ((B.shrink U B.time hU B.time_open hUB subset_rfl).coordinateMeasure μ).fst =
      (B.coordinateMeasure μ).fst.restrict U := by
  rw [shrink_marginal]
  calc
    _ = ((B.coordinateMeasure μ).fst.restrict U).withDensity 1 := by
      apply withDensity_congr_ae
      exact ae_restrict_of_ae (B.conditionalKernel_time_mass μ)
    _ = _ := withDensity_one

theorem base_overlap_anchorNormalize (A B C : UpperRootBox n g)
    (hAB : A.time ⊆ B.time) (hAC : A.time ⊆ C.time)
    (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      s ∈ B.transverse → s ∈ C.transverse →
      B.conditionalKernel μ s A.time ≠ 0 ∧ C.conditionalKernel μ s A.time ≠ 0 ∧
      (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (B.time ∩ C.time) =
        (anchorNormalize (C.conditionalKernel μ s) A.time).restrict (B.time ∩ C.time) := by
  let U := A.transverse ∩ B.transverse ∩ C.transverse
  have hU : IsOpen U := (A.transverse_open.inter B.transverse_open).inter C.transverse_open
  have hUA : U ⊆ A.transverse := inter_subset_left.trans inter_subset_left
  have hUB : U ⊆ B.transverse := inter_subset_left.trans inter_subset_right
  have hUC : U ⊆ C.transverse := inter_subset_right
  have H := overlap_anchorNormalize B C U A.time hU A.time_open hUB hUC hAB hAC μ
  have hD : B.shrink U A.time hU A.time_open hUB hAB =
      A.shrink U A.time hU A.time_open hUA subset_rfl := rfl
  rw [hD,A.shrink_full_time_marginal] at H
  have H' := (ae_restrict_iff' hU.measurableSet).mp H
  filter_upwards [H',A.coordinateMeasure_fst_ae_transverse μ] with s hs hsA
  intro hsB hsC
  exact hs ⟨⟨hsA,hsB⟩,hsC⟩



theorem base_anchor_restrict (A B : UpperRootBox n g) (hAB : A.time ⊆ B.time)
    (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ B.transverse →
      B.conditionalKernel μ s A.time ≠ 0 ∧
      (anchorNormalize (B.conditionalKernel μ s) A.time).restrict A.time =
        A.conditionalKernel μ s := by
  filter_upwards [base_overlap_anchorNormalize A A B subset_rfl hAB μ,
    A.coordinateMeasure_fst_ae_transverse μ,A.conditionalKernel_time_mass μ,
    A.conditionalKernel_ae_time μ] with s hs hsA hm ht
  intro hsB
  have H := hs hsA hsB
  refine ⟨H.2.1,?_⟩
  rw [inter_eq_left.mpr hAB] at H
  rw [←H.2.2]
  have hn : anchorNormalize (A.conditionalKernel μ s) A.time = A.conditionalKernel μ s := by
    simp only [anchorNormalize,hm,inv_one,one_smul]
  rw [hn]
  exact Measure.restrict_eq_self_of_ae_mem ht


theorem base_overlap_restrict (A B C : UpperRootBox n g)
    (hAB : A.time ⊆ B.time) (hAC : A.time ⊆ C.time)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    {W : Set (UpperRootTime n)} (hW : MeasurableSet W) (hWB : W ⊆ B.time) (hWC : W ⊆ C.time) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      s ∈ B.transverse → s ∈ C.transverse →
      (anchorNormalize (B.conditionalKernel μ s) A.time).restrict W =
        (anchorNormalize (C.conditionalKernel μ s) A.time).restrict W := by
  filter_upwards [base_overlap_anchorNormalize A B C hAB hAC μ] with s hs
  intro hsB hsC
  have H := congrArg (fun ν : Measure (UpperRootTime n) => ν.restrict W) (hs hsB hsC).2.2
  simpa only [Measure.restrict_restrict hW,inter_eq_left.mpr (subset_inter hWB hWC)] using H

end UpperRootBox
end DukePrimeDegree

end

end OAI
