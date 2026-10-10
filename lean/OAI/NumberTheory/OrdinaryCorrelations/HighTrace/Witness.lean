import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BoundedLists

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.SourceCylinder
open Finset Classical
variable {α ι : Type*} [Fintype α] [Fintype ι] {Ω : ι → Type*} [∀ p, Fintype (Ω p)]

abbrev Witness (V : Finset α) (f : α → Cylinder Ω) (t : ℕ) :=
  {I : Intersection (V.image f) // I ∈ witnesses (V.image f) t}

omit [Fintype α] in
lemma exists_witnessGenerator (V : Finset α) (f : α → Cylinder Ω) (t : ℕ)
    (I : Witness V f t) : ∃ l : List α, l.length ≤ t ∧
      (∀ a ∈ l, a ∈ V) ∧ Cylinder.Generates (l.toFinset.image f) I.val.val := by
  obtain ⟨A,hA,hcard,hgen⟩ := (mem_filter.mp I.property).2.2
  let rep : A → α := fun e => Classical.choose (mem_image.mp (hA e.property))
  have hv (e : A) : rep e ∈ V := (Classical.choose_spec (mem_image.mp (hA e.property))).1
  have hf (e : A) : f (rep e)=e.val := (Classical.choose_spec (mem_image.mp (hA e.property))).2
  let l : List α := A.attach.toList.map rep
  have hlen : l.length = A.card := by simp [l]
  have hmem (a : α) (ha : a ∈ l) : a ∈ V := by
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp ha
    exact hv e
  have he : l.toFinset.image f = A := by
    ext c
    constructor
    · intro hc
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hc
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      rw [hf e]
      exact e.property
    · intro hc
      let e : A := ⟨c,hc⟩
      exact mem_image.mpr ⟨rep e,List.mem_toFinset.mpr
        (List.mem_map.mpr ⟨e,mem_toList.mpr (mem_attach A e),rfl⟩),hf e⟩
  exact ⟨l,hlen ▸ hcard,hmem,he.symm ▸ hgen⟩

noncomputable def witnessGenerator (V : Finset α) (f : α → Cylinder Ω) (t : ℕ)
    (I : Witness V f t) : List α := Classical.choose (exists_witnessGenerator V f t I)

omit [Fintype α] in
lemma witnessGenerator_spec (V : Finset α) (f : α → Cylinder Ω) (t : ℕ)
    (I : Witness V f t) : (witnessGenerator V f t I).length ≤ t ∧
      (∀ a ∈ witnessGenerator V f t I, a ∈ V) ∧
      Cylinder.Generates ((witnessGenerator V f t I).toFinset.image f) I.val.val :=
  Classical.choose_spec (exists_witnessGenerator V f t I)

omit [Fintype α] in
lemma witnessGenerator_injective (V : Finset α) (f : α → Cylinder Ω) (t : ℕ) :
    Function.Injective (witnessGenerator V f t) := by
  intro I J he
  apply Subtype.ext
  apply Subtype.ext
  exact Cylinder.generates_unique (witnessGenerator_spec V f t I).2.2
    (by simpa only [he] using (witnessGenerator_spec V f t J).2.2)

omit [Fintype α] in
lemma witnessGenerator_holds (V : Finset α) (f : α → Cylinder Ω) (t : ℕ)
    (I : Witness V f t) (x : ∀ p, Ω p) (hx : I.val.val.Holds x) :
    ∀ a ∈ witnessGenerator V f t I, a ∈ V ∧ (f a).Holds x := by
  intro a ha
  refine ⟨(witnessGenerator_spec V f t I).2.1 a ha,?_⟩
  apply Cylinder.holds_mono _ hx
  exact (witnessGenerator_spec V f t I).2.2.1 (f a)
    (mem_image.mpr ⟨a,List.mem_toFinset.mpr ha,rfl⟩)

omit [Fintype α] in
lemma witnessCount_eq_sum (V : Finset α) (f : α → Cylinder Ω) (t : ℕ) (x : ∀ p, Ω p) :
    (witnessCount (V.image f) t x : ℝ) =
      ∑ I : Witness V f t, if I.val.val.Holds x then (1:ℝ) else 0 := by
  rw [witnessCount,card_eq_sum_ones,Nat.cast_sum]
  simp only [Nat.cast_one,sum_filter]
  exact sum_subtype (witnesses (V.image f) t) (fun _ => Iff.rfl)
    (fun I : Intersection (V.image f) => if I.val.Holds x then (1:ℝ) else 0)

theorem witnessCount_le_list_sum (V : Finset α) (f : α → Cylinder Ω) (t : ℕ)
    (x : ∀ p, Ω p) (F : List α → ℝ) (hF : ∀ l, 0 ≤ F l)
    (hI : ∀ I : Witness V f t, I.val.val.Holds x → 1 ≤ F (witnessGenerator V f t I)) :
    (witnessCount (V.image f) t x : ℝ) ≤ ∑ l ∈ boundedLists α t, F l := by
  rw [witnessCount_eq_sum V f]
  calc
    _ ≤ ∑ I : Witness V f t, F (witnessGenerator V f t I) := by
      apply sum_le_sum
      intro I hmem
      split_ifs with hx
      · exact hI I hx
      · exact hF _
    _ ≤ _ := by
      rw [← sum_image (fun x _ y _ he => witnessGenerator_injective V f t he)]
      apply sum_le_sum_of_subset_of_nonneg
      · intro l hl
        obtain ⟨I,hI,rfl⟩ := mem_image.mp hl
        exact (mem_boundedLists _ _).mpr (witnessGenerator_spec V f t I).1
      · intro l hl hnot
        exact hF l

end OrdinaryCorrelations.SourceCylinder

end

end OAI
