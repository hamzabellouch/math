import OAI.Probability.BenjaminiSchramm.FreshSlabCrossing

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def restrictedHit (I : Set E) (x : V) (A : Set V) : Set (Set E) :=
  {ω | ∃ y ∈ A, Conn G (ω ∩ I) x y}

lemma measurableSet_restrictedHit [Countable V] [Countable E]
    (I : Set E) (x : V) (A : Set V) : MeasurableSet (restrictedHit G I x A) := by
  have hm : Measurable (fun ω : Set E => ω ∩ I) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact (Measurable.exists fun y => measurable_const.and
    ((measurableSet_conn G x y).mem.comp hm)).setOf

lemma restrictedHit_dependsOn (I : Set E) (x : V) (A : Set V) :
    DependsOn (fun ω => ω ∈ restrictedHit G I x A) I := by
  intro ω η hωη
  have he : Set.inter ω I = Set.inter η I := by
    ext e
    change (ω e ∧ e ∈ I) ↔ (η e ∧ e ∈ I)
    by_cases hi : e ∈ I
    · simp only [hi,and_true]
      exact Iff.of_eq (hωη e hi)
    · simp only [hi,and_false]
  change (∃ y ∈ A, Conn G (Set.inter ω I) x y) =
    (∃ y ∈ A, Conn G (Set.inter η I) x y)
  rw [he]

theorem restrictedHit_fresh_concatenation [Encodable V] [Countable E]
    (q : E → unitInterval) (I J : Set E) (hIJ : Disjoint I J)
    (x : V) (A B : Set V) (c : ℝ≥0∞)
    (hc : ∀ z ∈ A, c ≤ CriticalPercolation.BernoulliProduct.law q (restrictedHit G J z B)) :
    CriticalPercolation.BernoulliProduct.law q (restrictedHit G I x A) * c ≤
      CriticalPercolation.BernoulliProduct.law q (restrictedHit G (I ∪ J) x B) := by
  let SA : A → Set (Set E) := fun z => firstLayerHitAt G I x A z
  let SB : A → Set (Set E) := fun z => restrictedHit G J z B
  have hdisj : Pairwise (fun z w => Disjoint (SA z) (SA w)) := by
    intro z w hzw
    exact firstLayerHitAt_pairwise G I x A (fun h => hzw (Subtype.ext h))
  have hsub : J ⊆ Iᶜ := Set.disjoint_left.mp hIJ.symm
  have hprob := CriticalPercolation.BernoulliProduct.selected_fresh_continuation_lower
    q I SA SB (fun z => measurableSet_firstLayerHitAt G I x A z)
    (fun z => measurableSet_restrictedHit G J z B)
    (fun z => firstLayerHitAt_dependsOn G I x A z)
    (fun z => DependsOn.mono hsub (restrictedHit_dependsOn G J z B))
    hdisj c (fun z => hc z z.property)
  have hsel : (⋃ z, SA z) = restrictedHit G I x A := by
    ext ω
    constructor
    · intro h
      obtain ⟨z,hz⟩ := Set.mem_iUnion.mp h
      exact ⟨z,z.property,hz.1⟩
    · intro h
      have h' : ω ∈ ⋃ z, firstLayerHitAt G I x A z := by
        rw [iUnion_firstLayerHitAt]
        exact h
      obtain ⟨z,hz⟩ := Set.mem_iUnion.mp h'
      exact Set.mem_iUnion.mpr ⟨⟨z,hz.2.1⟩,hz⟩
  rw [hsel] at hprob
  refine hprob.trans (measure_mono ?_)
  intro ω hω
  obtain ⟨z,hz,hcont⟩ := Set.mem_iUnion.mp hω
  obtain ⟨y,hy,hzy⟩ := hcont
  refine ⟨y,hy,(conn_mono G (Set.inter_subset_inter_right _ Set.subset_union_left) hz.1).trans ?_⟩
  exact conn_mono G (Set.inter_subset_inter_right _ Set.subset_union_right) hzy

theorem slab_crossing_fresh_product [Encodable V] [Countable E]
    (q : E → unitInterval) (f : V → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (x : V) (a b d t : ℝ) (hx : a ≤ f x) (hxb : f x < b) (hbd : b+R ≤ d)
    (κ : ℝ≥0∞)
    (hκ : ∀ z, b ≤ f z → f z ≤ b+R →
      κ ≤ CriticalPercolation.BernoulliProduct.law q
        (restrictedHit G (internalEdges G {v | b ≤ f v ∧ f v ≤ d}) z {v | t ≤ f v})) :
    CriticalPercolation.BernoulliProduct.law q
      (restrictedHit G (internalEdges G {v | a ≤ f v ∧ f v ≤ b+R}) x {v | b ≤ f v}) * κ ≤
      CriticalPercolation.BernoulliProduct.law q
        (restrictedHit G (internalEdges G {v | a ≤ f v ∧ f v ≤ d}) x {v | t ≤ f v}) := by
  let I := lowerCrossingBlock G f a b R
  let J := internalEdges G {v | b ≤ f v ∧ f v ≤ d}
  let A := {v | b ≤ f v ∧ f v ≤ b+R}
  let B := {v | t ≤ f v}
  have hIJ : Disjoint I J := by
    apply (lowerCrossingBlock_disjoint_upper G f a b R).mono_right
    exact internalEdges_mono G (fun _ h => h.1)
  have hstart : restrictedHit G (internalEdges G {v | a ≤ f v ∧ f v ≤ b+R}) x
      {v | b ≤ f v} ⊆ restrictedHit G I x A := by
    intro ω hω
    obtain ⟨y,hy,hxy⟩ := hω
    have hlo : Conn G (ω ∩ internalEdges G {v | a ≤ f v}) x y :=
      conn_mono G (Set.inter_subset_inter_right _ (internalEdges_mono G (fun _ h => h.1))) hxy
    obtain ⟨z,hz,hzR,hzconn⟩ :=
      conn_above_lower_first_crossing G f R hR hjump ω x y a b hx hxb hy hlo
    exact ⟨z,⟨hz,hzR⟩,hzconn⟩
  have hfinish : I ∪ J ⊆ internalEdges G {v | a ≤ f v ∧ f v ≤ d} := by
    intro e he
    rcases he with he | he
    · apply internalEdges_mono G (show {v | a ≤ f v ∧ f v ≤ b+R} ⊆
          {v | a ≤ f v ∧ f v ≤ d} from fun _ h => ⟨h.1,h.2.trans hbd⟩) he.1
    · apply internalEdges_mono G (show {v | b ≤ f v ∧ f v ≤ d} ⊆
          {v | a ≤ f v ∧ f v ≤ d} from fun _ h => ⟨by linarith [h.1],h.2⟩) he
  calc
    _ ≤ CriticalPercolation.BernoulliProduct.law q (restrictedHit G I x A) * κ :=
      mul_le_mul' (measure_mono hstart) le_rfl
    _ ≤ CriticalPercolation.BernoulliProduct.law q (restrictedHit G (I ∪ J) x B) :=
      restrictedHit_fresh_concatenation G q I J hIJ x A B κ
        (fun z hz => hκ z hz.1 hz.2)
    _ ≤ _ := by
      apply measure_mono
      intro ω hω
      obtain ⟨y,hy,hxy⟩ := hω
      exact ⟨y,hy,conn_mono G (Set.inter_subset_inter_right _ hfinish) hxy⟩

end Percolation.BenjaminiSchramm

end

end OAI
