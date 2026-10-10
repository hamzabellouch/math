import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.MemSupport

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

noncomputable def boundedLists (α : Type*) [Fintype α] (n : ℕ) : Finset (List α) :=
  (range (n+1)).biUnion (fun k => univ.image (fun f : Fin k → α => List.ofFn f))

@[simp] lemma mem_boundedLists (n : ℕ) (l : List α) : l ∈ boundedLists α n ↔ l.length ≤ n := by
  simp only [boundedLists,mem_biUnion,mem_range,mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨k,hk,f,rfl⟩
    simp only [List.length_ofFn]
    omega
  · intro hl
    refine ⟨l.length,by omega,l.get,?_⟩
    simp

omit [Fintype α] in
lemma exists_generatingList (V : Finset α) (f : α → Cylinder Ω)
    (I : Intersection (V.image f)) :
    ∃ l : List α, l.length ≤ Cylinder.rank (V.image f) I.val ∧
      (∀ a ∈ l, a ∈ V) ∧ Cylinder.Generates (l.toFinset.image f) I.val := by
  obtain ⟨A,hA,hcard,hgen⟩ := Cylinder.minimal_generators (V.image f) I.val I.property
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

abbrev LowRank (V : Finset α) (f : α → Cylinder Ω) (t : ℕ) :=
  {I : Intersection (V.image f) // I ∈ retained (V.image f) t}

noncomputable def generatingList (V : Finset α) (f : α → Cylinder Ω) (t : ℕ)
    (I : LowRank V f t) : List α := Classical.choose (exists_generatingList V f I.val)

omit [Fintype α] in
lemma generatingList_spec (V : Finset α) (f : α → Cylinder Ω) (t : ℕ)
    (I : LowRank V f t) :
    (generatingList V f t I).length ≤ t ∧
    (∀ a ∈ generatingList V f t I, a ∈ V) ∧
    Cylinder.Generates ((generatingList V f t I).toFinset.image f) I.val.val := by
  have h := Classical.choose_spec (exists_generatingList V f I.val)
  have hr : Cylinder.rank (V.image f) I.val.val < t := (mem_filter.mp I.property).2
  exact ⟨h.1.trans hr.le,h.2⟩

omit [Fintype α] in
lemma generatingList_injective (V : Finset α) (f : α → Cylinder Ω) (t : ℕ) :
    Function.Injective (generatingList V f t) := by
  intro I J he
  apply Subtype.ext
  apply Subtype.ext
  exact Cylinder.generates_unique (generatingList_spec V f t I).2.2
    (by simpa only [he] using (generatingList_spec V f t J).2.2)

lemma generatingList_sum_le (V : Finset α) (f : α → Cylinder Ω) (t : ℕ)
    (F : List α → ℝ) (hF : ∀ l, 0 ≤ F l) :
    (∑ I : LowRank V f t, F (generatingList V f t I)) ≤ ∑ l ∈ boundedLists α t, F l := by
  rw [← sum_image (fun x _ y _ he => generatingList_injective V f t he)]
  apply sum_le_sum_of_subset_of_nonneg
  · intro l hl
    obtain ⟨I,hI,rfl⟩ := mem_image.mp hl
    exact (mem_boundedLists _ _).mpr (generatingList_spec V f t I).1
  · intro l hl hnot
    exact hF l

noncomputable def labelledIndicator (V : Finset α) (f : α → Cylinder Ω)
    (l : List α) (x : ∀ p, Ω p) : ℝ :=
  if ∀ a ∈ l, a ∈ V ∧ (f a).Holds x then 1 else 0

lemma generatingList_indicator (V : Finset α) (f : α → Cylinder Ω) (t : ℕ)
    (I : LowRank V f t) (x : ∀p, Ω p) :
    labelledIndicator V f (generatingList V f t I) x = if I.val.val.Holds x then 1 else 0 := by
  have hgen := (generatingList_spec V f t I).2.2
  have he : I.val.val.Holds x ↔
      ∀ a ∈ generatingList V f t I, a ∈ V ∧ (f a).Holds x := by
    rw [Cylinder.generates_holds hgen]
    constructor
    · intro hx a ha
      exact ⟨(generatingList_spec V f t I).2.1 a ha,
        hx (f a) (mem_image.mpr ⟨a,List.mem_toFinset.mpr ha,rfl⟩)⟩
    · intro hx c hc
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hc
      exact (hx a (List.mem_toFinset.mp ha)).2
  simp only [labelledIndicator,← he]

end OrdinaryCorrelations.SourceCylinder

end

end OAI
