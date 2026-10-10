import Mathlib
import OAI.Geometry.HyperbolicGroups.CoreWordGraph

namespace OAI

noncomputable section

namespace HyperbolicObstruction.LetterPresentation
open IncidenceTemplate CoreGeometry MasterGraph SimpleGraph
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- Exactly the source03 finite presentation: all simple cycles of each
included fan and compatible included top graph, plus the two decorations.
The underlying template graph is not quotiented by its random labels. -/
inductive SimpleWordRelator : List (Alphabet n) → Prop
  | fan (l : Field → Alphabet n) (i : Fin 7)
      (present : w (TableModel.row rowSupport l (.inl i)) = true)
      (v : CoreGeometry.Vertex) (p : (CoreWordGraph.graph (fan i)).Walk v v)
      (simple : p.IsCycle) :
      SimpleWordRelator (GraphWordFilling.word (CoreWordGraph.label (fan i) n l) p)
  | top (l : Field → Alphabet n)
      (present : w (TableModel.row rowSupport l (.inr (.inl ()))) = true)
      (fans : ∀ i : Fin 7, w (TableModel.row rowSupport l (.inl i)) = true)
      (v : CoreGeometry.Vertex) (p : (CoreWordGraph.graph Finset.univ).Walk v v)
      (simple : p.IsCycle) :
      SimpleWordRelator (GraphWordFilling.word (CoreWordGraph.label Finset.univ n l) p)
  | square (l : Field → Alphabet n) (τ : TwoPath)
      (present : w (TableModel.row rowSupport l (.inr (.inr τ))) = true) :
      SimpleWordRelator (literalSquare n l τ)
  | six (x : Fin 6 → Alphabet n) (present : d x = true) : SimpleWordRelator (List.ofFn x)

lemma simpleWordRelator_length {z : List (Alphabet n)} (hz : SimpleWordRelator n w d z) :
    z.length ≤ 18 := by
  cases hz with
  | fan l i present v p hp =>
      rw [GraphWordFilling.word_length]; exact CoreWordGraph.cycle_length _ p hp
  | top l present fans v p hp =>
      rw [GraphWordFilling.word_length]; exact CoreWordGraph.cycle_length _ p hp
  | square => simp [literalSquare]
  | six => simp

/-- Finiteness is proved from literal words, including coinciding labels and
repeated rows, not asserted as an extra presentation hypothesis. -/
theorem simpleWordRelator_finite : Set.Finite {z | SimpleWordRelator n w d z} := by
  let g : (Σ k : Fin 19, Fin k.val → Alphabet n) → List (Alphabet n) := fun x => List.ofFn x.2
  apply (Set.finite_range g).subset
  intro z hz
  refine ⟨⟨⟨z.length,by have hh := simpleWordRelator_length n w d hz; omega⟩,
    fun i => z[i]⟩,?_⟩
  exact List.ofFn_get z

lemma simpleWordRelator_original {z : List (Alphabet n)} (hz : SimpleWordRelator n w d z) :
    WordRelator n w d z := by
  cases hz with
  | fan l i present v p simple =>
    rw [← CoreWordGraph.toMaster_word]
    apply WordRelator.fan l i present (.inl v)
    intro f hf
    have hm := CoreWordGraph.toMaster_fields (fan i) p f (List.mem_toFinset.mp hf)
    obtain ⟨e,rfl,he⟩ := hm
    simpa [rowSupport] using he
  | top l present fans v p simple =>
    rw [← CoreWordGraph.toMaster_word]
    apply WordRelator.top l present fans (.inl v)
    intro f hf
    obtain ⟨e,rfl,he⟩ := CoreWordGraph.toMaster_fields Finset.univ p f hf
    exact ⟨e,rfl⟩
  | square l τ present => exact WordRelator.square l τ present
  | six x present => exact WordRelator.six x present

lemma fan_fields {v z : MasterGraph.Vertex} (i : Fin 7)
    (p : MasterGraph.Path v z) (hp : p.fields.toFinset ⊆ rowSupport (.inl i)) :
    CoreWordGraph.Fields (fan i) p := by
  intro f hf
  have hh := hp (List.mem_toFinset.mpr hf)
  rcases f with e | x
  · exact ⟨e,rfl,by simpa [rowSupport] using hh⟩
  · simp [rowSupport] at hh

lemma top_fields {v z : MasterGraph.Vertex} (p : MasterGraph.Path v z) (hp : p.IsCore) :
    CoreWordGraph.Fields Finset.univ p := by
  intro f hf
  obtain ⟨e,rfl⟩ := hp f hf
  exact ⟨e,rfl,Finset.mem_univ _⟩

/-- Every ORIGINAL relator has a quantitative derivation in the finite
simple-cycle presentation. The bound is its literal length (zero included). -/
theorem relator_simple_filling {z : List (Alphabet n)} (hz : WordRelator n w d z) :
    ∃ a ≤ z.length, WordPictures.Homotopy (SimpleWordRelator n w d) z [] a := by
  cases hz with
  | fan l i present v p fields =>
    have hp := fan_fields i p fields
    obtain ⟨a,ha,hh⟩ := GraphWordFilling.closed_filling (CoreWordGraph.label (fan i) n l)
      (CoreWordGraph.label_rev _ _ _) (SimpleWordRelator n w d)
      (fun v p h => SimpleWordRelator.fan l i present v p h) (CoreWordGraph.path _ p hp)
    rw [CoreWordGraph.path_word] at hh
    rw [CoreWordGraph.path_length] at ha
    exact ⟨a,by simpa only [pathWord_length] using ha,hh⟩
  | top l present fans v p core =>
    have hp := top_fields p core
    obtain ⟨a,ha,hh⟩ := GraphWordFilling.closed_filling (CoreWordGraph.label Finset.univ n l)
      (CoreWordGraph.label_rev _ _ _) (SimpleWordRelator n w d)
      (fun v p h => SimpleWordRelator.top l present fans v p h) (CoreWordGraph.path _ p hp)
    rw [CoreWordGraph.path_word] at hh
    rw [CoreWordGraph.path_length] at ha
    exact ⟨a,by simpa only [pathWord_length] using ha,hh⟩
  | square l τ present =>
    refine ⟨1,by simp [literalSquare],?_⟩
    simpa only [List.nil_append,List.append_nil] using
      (WordPictures.Homotopy.move (WordPictures.Move.face [] [] _
        (SimpleWordRelator.square l τ present)))
  | six x present =>
    refine ⟨1,by simp,?_⟩
    simpa only [List.nil_append,List.append_nil] using
      (WordPictures.Homotopy.move (WordPictures.Move.face [] [] _
        (SimpleWordRelator.six x present)))

/-- Exact normal-closure equality, giving the same original marked group,
not merely a surjection from a conveniently chosen finite presentation. -/
theorem simple_presentation_normalClosure :
    Subgroup.normalClosure (FreeGroup.mk '' SimpleWordRelator n w d) =
    Subgroup.normalClosure (Relator n w d) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_mono
    rintro _ ⟨z,hz,rfl⟩
    rw [← wordRelator_image]
    exact ⟨z,simpleWordRelator_original n w d hz,rfl⟩
  · apply Subgroup.normalClosure_le_normal
    intro g hg
    rw [← wordRelator_image] at hg
    obtain ⟨z,hz,rfl⟩ := hg
    obtain ⟨a,ha,hh⟩ := relator_simple_filling n w d hz
    apply PresentedGroup.mk_eq_one_iff.mp
    have he := WordPictures.sound hh
    exact he

end HyperbolicObstruction.LetterPresentation
end

end OAI
