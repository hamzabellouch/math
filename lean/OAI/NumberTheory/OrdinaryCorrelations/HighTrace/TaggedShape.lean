import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ModifiedWeightSameBand

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

abbrev TaggedShape (w : ClosedLine h ℓ) := Shape w ⊕ Fin ℓ

def taggedShapeCode (w : ClosedLine h ℓ) : TaggedShape w → LocalToken ℓ
  | .inl Q => (true,false,Q.edges.val)
  | .inr e => (true,true,{e})

lemma taggedShapeCode_injective (w : ClosedLine h ℓ) : Function.Injective (taggedShapeCode w) := by
  intro s t he
  rcases s with Q | e <;> rcases t with R | j
  · exact congrArg Sum.inl (Shape.edges_injective w (congrArg (fun t : LocalToken ℓ => t.2.2) he))
  · have := congrArg (fun t : LocalToken ℓ => t.2.1) he; contradiction
  · have := congrArg (fun t : LocalToken ℓ => t.2.1) he; contradiction
  · exact congrArg Sum.inr (singleton_injective (congrArg (fun t : LocalToken ℓ => t.2.2) he))

lemma taggedPieces_shape (w : ClosedLine h ℓ) (hh : 0 < h) (O E : Finset (Fin ℓ))
    (hE : E ⊆ w.treeSteps) (t : LocalToken ℓ) (ht : t ∈ taggedPieces w hh O E) :
    ∃ s : TaggedShape w, taggedShapeCode w s=t := by
  rcases mem_union.mp ht with ht | ht
  · obtain ⟨c,hc,rfl⟩ := mem_image.mp ht
    exact ⟨.inl (shapeFromGrows w _ _ (component_grows w hh hE c hc)
      (componentEdges_nonempty w hh E c hc)),rfl⟩
  · obtain ⟨e,he,rfl⟩ := mem_image.mp ht
    exact ⟨.inr e,rfl⟩

theorem record_tagged_shape (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index)
    (t : LocalToken ℓ) (ht : t ∈ taggedTokens w hh 𝔏 (recordAt w hh 𝔏 a) p) :
    ∃ s : TaggedShape w, taggedShapeCode w s=t := by
  obtain ⟨ht,htag⟩ := mem_filter.mp ht
  by_cases ho : (treeOccurrences w p).Nonempty
  · rw [recordTokens,ite_eq_left ho] at ht
    by_cases hf : S.IsFixed w p
    · rw [ite_eq_left hf] at ht
      by_cases hp : (recordAt w hh 𝔏 a).2 p=true
      · rw [ite_eq_left hp] at ht
        exact taggedPieces_shape w hh _ _ ((recordAt_compatible w hh 𝔏 a p).trans (filter_subset _ _)) t ht
      · rw [ite_eq_right hp] at ht
        have he := mem_singleton.mp ht
        have hfalse : t.1=false := congrArg Prod.fst he
        rw [hfalse] at htag
        contradiction
    · rw [ite_eq_right hf] at ht
      obtain ⟨e,he,rfl⟩ := mem_image.mp ht
      by_cases hp : singletonIsTagged w 𝔏 p e
      · exact ⟨.inr e,by simp only [taggedShapeCode,freePiece,hp,ite_true]⟩
      · simp only [freePiece,hp,ite_false] at htag
        contradiction
  · rw [recordTokens,ite_eq_right ho] at ht
    exact False.elim (Finset.notMem_empty _ ht)

lemma subtree_shape_sum (w : ClosedLine h ℓ) (p : S.Index) :
    (∑ Q : Shape w, subtreeUnionWeight w p Q.edges.val) ≤ bandDefect w (S.beta p) := by
  have hA : 0 ≤ S.amplitude p := by
    unfold amplitude
    split_ifs
    · exact A_pos.le
    · norm_num
  have hne : 1+S.amplitude p ≠ 0 := ne_of_gt (by linarith)
  have hunit : S.beta p*(1+S.amplitude p)=1 := inv_mul_cancel₀ hne
  rw [sum_shapes]
  exact numerical_subtree_sum_le w (S.amplitude p) (S.beta p) hA (beta_nonneg p) hunit

lemma bandDefect_le_vertices (w : ClosedLine h ℓ) (p : S.Index) :
    bandDefect w (S.beta p) ≤ (ℓ:ℝ)+1 := by
  calc
    _ ≤ ∑ _v ∈ treeVertices w, (1:ℝ) := by
      apply sum_le_sum
      intro v hv
      have hn : 0 ≤ (S.beta p)^(w.children v) := pow_nonneg (beta_nonneg p) _
      linarith
    _ = ((treeVertices w).card : ℝ) := by simp
    _ ≤ (ℓ:ℝ)+1 := by
      have hc : (treeVertices w).card ≤ ℓ+1 := by
        simpa only [treeVertices,card_univ,Fintype.card_fin] using card_image_le (s := (univ : Finset (Fin (ℓ+1)))) (f := w.offset)
      exact_mod_cast hc

theorem tagged_shape_sum (w : ClosedLine h ℓ) (p : S.Index) :
    (∑ s : TaggedShape w, localTokenWeight w p (taggedShapeCode w s)) ≤ 3*(ℓ:ℝ)+1 := by
  rw [Fintype.sum_sum_type]
  simp only [taggedShapeCode,localTokenWeight,ite_true,Bool.false_eq_true,ite_false,tokenEdges]
  have h1 := subtree_shape_sum w p
  have h2 := bandDefect_le_vertices w p
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  linarith

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
