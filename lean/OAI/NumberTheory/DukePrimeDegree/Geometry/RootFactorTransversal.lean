import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixBoxes

namespace OAI

/-! # Recovering the transverse embedding in an affine root chart -/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma isOpenEmbedding_of_prodMap_real {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {e : A → B} (h : Topology.IsOpenEmbedding (Prod.map e (id : ℝ → ℝ))) :
    Topology.IsOpenEmbedding e := by
  have he : Topology.IsEmbedding e :=
    (isEmbedding_prodMkLeft (0 : ℝ)).of_comp_iff.mp
      (h.isEmbedding.comp (isEmbedding_prodMkLeft (0 : ℝ)))
  apply Topology.IsOpenEmbedding.of_isEmbedding_isOpenMap he
  intro U hU
  have H := isOpenMap_fst _ (h.isOpenMap _ (hU.prod isOpen_univ))
  have hs : Prod.fst '' (Prod.map e (id : ℝ → ℝ) '' (U ×ˢ univ)) = e '' U := by
    ext b
    constructor
    · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩
      exact ⟨z.1,hz.1,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨(e a,0),⟨(a,0),⟨ha,mem_univ _⟩,rfl⟩,rfl⟩
  rwa [hs] at H

theorem root_transversal_isOpenEmbedding {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    {A : Type*} [TopologicalSpace A] (f : A → RootPivot a k) (hf : Continuous f)
    (hchart : Topology.IsOpenEmbedding
      (fun z : A × ℝ => rootPivotTranslate hab (f z.1) z.2)) :
    Topology.IsOpenEmbedding (fun x => rootSliceRepresentative hab (f x)) := by
  let τ : A → ℝ := fun x => -rootParameter a b k (f x).val
  have hτ : Continuous τ := (continuous_rootParameter.comp hf).neg
  let H := (rootPivotHomeomorph hab).isOpenEmbedding.comp
    (hchart.comp (fiberShear (Homeomorph.refl A) τ hτ).isOpenEmbedding)
  have he : Topology.IsOpenEmbedding
      (Prod.map (fun x => rootSliceRepresentative hab (f x)) (id : ℝ → ℝ)) := by
    convert H using 1
    funext z
    rw [Function.comp_apply, Function.comp_apply, rootPivotHomeomorph_translate]
    apply Prod.ext
    · rfl
    · change z.2 = rootParameter a b k (f z.1).val +
        (z.2 + -rootParameter a b k (f z.1).val)
      ring
  exact isOpenEmbedding_of_prodMap_real he

end DukePrimeDegree

end

end OAI
