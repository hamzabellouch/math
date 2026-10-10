import Mathlib
import OAI.Geometry.CAT0Fillings.Slicing.EuclideanSplit

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
noncomputable def prismDomain : Set (Euc (k+1)) :=
  Prism.split k ⁻¹' (Icc (0:ℝ) 1 ×ˢ C.domain)

lemma measurableSet_prismDomain : MeasurableSet C.prismDomain :=
  (measurableSet_Icc.prod C.borel).preimage (Prism.split k).continuous.measurable

lemma bounded_prismDomain : Bornology.IsBounded C.prismDomain := by
  have h := (Prism.split k).symm.lipschitzWith.isBounded_image
    ((isCompact_Icc (a := (0:ℝ)) (b := 1)).isBounded.prod C.bounded)
  change Bornology.IsBounded ((Prism.split k).toEquiv.symm '' (Icc (0:ℝ) 1 ×ˢ C.domain)) at h
  rw [Equiv.image_symm_eq_preimage] at h
  exact h

noncomputable def prismParam (z : C.prismDomain) : ℝ × X :=
  ((Prism.split k z).1, C.param ⟨(Prism.split k z).2,z.2.2⟩)

lemma prismParam_bilipschitz : ∃ L U : ℝ≥0,
    LipschitzWith L C.prismParam ∧ AntilipschitzWith U C.prismParam := by
  obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
  have hs := (Prism.split k).lipschitzWith.comp (LipschitzWith.subtype_val C.prismDomain)
  have ht := LipschitzWith.prod_fst.comp hs
  have hz := (LipschitzWith.prod_snd.comp hs).subtype_mk (fun z : C.prismDomain => z.2.2)
  refine ⟨_, ‖(Prism.split k).symm.toContinuousLinearMap‖₊ * max 1 U,
    ht.prodMk (hL.comp hz), ?_⟩
  apply AntilipschitzWith.of_le_mul_dist
  intro z w
  have hu := hU.le_mul_dist
    ⟨(Prism.split k z).2,z.2.2⟩ ⟨(Prism.split k w).2,w.2.2⟩
  have hs' := (Prism.split k).antilipschitz.le_mul_dist z.val w.val
  change dist z.val w.val ≤ _
  calc
    _ ≤ _ := hs'
    _ ≤ ‖(Prism.split k).symm.toContinuousLinearMap‖₊ *
        ((max 1 U : ℝ≥0) * dist (C.prismParam z) (C.prismParam w)) := by
      apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg _)
      rw [Prod.dist_eq]
      apply max_le
      · calc
          _ ≤ dist (C.prismParam z) (C.prismParam w) := le_max_left _ _
          _ ≤ _ := le_mul_of_one_le_left dist_nonneg (by exact_mod_cast le_max_left 1 U)
      · calc
          _ ≤ (U:ℝ) * dist (C.prismParam z).2 (C.prismParam w).2 := hu
          _ ≤ (U:ℝ) * dist (C.prismParam z) (C.prismParam w) :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) U.coe_nonneg
          _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right 1 U) dist_nonneg
    _ = _ := by simp only [NNReal.coe_mul,mul_assoc]

lemma integrable_prismMultiplicity :
    Integrable (fun z => (C.multiplicity ((Prism.split k z).2) : ℝ))
      (volume.restrict C.prismDomain) := by
  have hi := C.integrable.comp_snd (volume.restrict (Icc (0:ℝ) 1))
  rw [Measure.prod_restrict] at hi
  exact ((Prism.split_measurePreserving k).restrict_preimage
    (measurableSet_Icc.prod C.borel)).integrable_comp_emb
      (Prism.split k).toHomeomorph.measurableEmbedding |>.mpr hi

noncomputable def prism : IntegerChart (ℝ × X) (k+1) where
  domain := C.prismDomain
  borel := C.measurableSet_prismDomain
  bounded := C.bounded_prismDomain
  param := C.prismParam
  bilipschitz := C.prismParam_bilipschitz
  multiplicity z := C.multiplicity ((Prism.split k z).2)
  integrable := C.integrable_prismMultiplicity

lemma prism_image : C.prism.image = Icc (0:ℝ) 1 ×ˢ C.image := by
  ext p
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨z.2.1,⟨⟨(Prism.split k z).2,z.2.2⟩,rfl⟩⟩
  · rintro ⟨ht,⟨z,hz⟩⟩
    let w : C.prismDomain := ⟨(Prism.split k).symm (p.1,z),by
      change Prism.split k ((Prism.split k).symm (p.1,z)) ∈ Icc (0:ℝ) 1 ×ˢ C.domain
      simpa only [ContinuousLinearEquiv.apply_symm_apply,mem_prod] using And.intro ht z.2⟩
    refine ⟨w,?_⟩
    change C.prismParam w = p
    simp only [prismParam,w,ContinuousLinearEquiv.apply_symm_apply]
    exact Prod.ext rfl hz

lemma prism_image_disjoint {D : IntegerChart X k} (h : Disjoint C.image D.image) :
    Disjoint C.prism.image D.prism.image := by
  rw [C.prism_image,D.prism_image]
  exact Set.disjoint_left.mpr fun _ hp hq => Set.disjoint_left.mp h hp.2 hq.2

end CAT0Fillings.IntegerChart

end
end

end OAI
