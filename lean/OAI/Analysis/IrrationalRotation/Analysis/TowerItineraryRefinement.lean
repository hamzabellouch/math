import Mathlib

namespace OAI

namespace Invariant233.TowerItinerary

variable {X ι κ : Type*}

def word (f : X → X) (c : X → κ) (h : ℕ) (x : X) : Fin h → κ :=
  fun k => c (f^[k.val] x)

def refinedBase (f : X → X) (c : X → κ) (B : Set X) (h : ℕ)
    (w : Fin h → κ) : Set X := B ∩ {x | word f c h x = w}

@[simp] theorem mem_refinedBase {f : X → X} {c : X → κ} {B : Set X}
    {h : ℕ} {w : Fin h → κ} {x : X} :
    x ∈ refinedBase f c B h w ↔ x ∈ B ∧ word f c h x = w := Iff.rfl

theorem refinedBase_subset (f : X → X) (c : X → κ) (B : Set X)
    (h : ℕ) (w : Fin h → κ) : refinedBase f c B h w ⊆ B :=
  Set.inter_subset_left

theorem iUnion_refinedBase (f : X → X) (c : X → κ) (B : Set X) (h : ℕ) :
    (⋃ w : Fin h → κ, refinedBase f c B h w) = B := by
  ext x
  simp only [Set.mem_iUnion, mem_refinedBase]
  exact ⟨fun ⟨_, hx, _⟩ => hx, fun hx => ⟨word f c h x, hx, rfl⟩⟩

theorem disjoint_refinedBase (f : X → X) (c : X → κ) (B : Set X)
    (h : ℕ) {v w : Fin h → κ} (hvw : v ≠ w) :
    Disjoint (refinedBase f c B h v) (refinedBase f c B h w) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hvw (hx.2.symm.trans hy.2)

theorem image_refinedBase_subset_color (f : X → X) (c : X → κ)
    (B : Set X) (h : ℕ) (w : Fin h → κ) (k : Fin h) :
    f^[k.val] '' refinedBase f c B h w ⊆ c ⁻¹' {w k} := by
  rintro y ⟨x, hx, rfl⟩
  exact congrFun hx.2 k

theorem iUnion_image_refinedBase (f : X → X) (c : X → κ)
    (B : Set X) (h n : ℕ) :
    (⋃ w : Fin h → κ, f^[n] '' refinedBase f c B h w) = f^[n] '' B := by
  rw [← Set.image_iUnion, iUnion_refinedBase]

section Measurable
variable [MeasurableSpace X] [MeasurableSpace κ] [MeasurableSingletonClass κ]

omit [MeasurableSingletonClass κ] in
theorem measurable_word {f : X → X} {c : X → κ}
    (hf : Measurable f) (hc : Measurable c) (h : ℕ) :
    Measurable (word f c h) := by
  exact Measurable.of_eval (fun k => hc.comp (hf.iterate k.val))

theorem measurableSet_refinedBase {f : X → X} {c : X → κ} {B : Set X}
    (hf : Measurable f) (hc : Measurable c) (hB : MeasurableSet B)
    (h : ℕ) (w : Fin h → κ) : MeasurableSet (refinedBase f c B h w) := by
  exact hB.inter ((measurable_word hf hc h) (measurableSet_singleton w))

end Measurable

def level (f : X → X) (B : ι → Set X) (h : ι → ℕ)
    (a : ι) (k : Fin (h a)) : Set X := f^[k.val] '' B a

abbrev RefinedIndex (h : ι → ℕ) (κ : Type*) := Σ a, Fin (h a) → κ

def refinedHeight (h : ι → ℕ) (a : RefinedIndex h κ) : ℕ := h a.1

def bases (f : X → X) (c : X → κ) (B : ι → Set X) (h : ι → ℕ)
    (a : RefinedIndex h κ) : Set X := refinedBase f c (B a.1) (h a.1) a.2

theorem level_eq_iUnion (f : X → X) (c : X → κ) (B : ι → Set X)
    (h : ι → ℕ) (a : ι) (k : Fin (h a)) :
    level f B h a k = ⋃ w : Fin (h a) → κ,
      level f (bases f c B h) (refinedHeight h) ⟨a, w⟩ k := by
  exact (iUnion_image_refinedBase f c (B a) (h a) k.val).symm

theorem refined_covers (f : X → X) (c : X → κ) (B : ι → Set X)
    (h : ι → ℕ)
    (hcover : ∀ x, ∃ a, ∃ k : Fin (h a), x ∈ level f B h a k) :
    ∀ x, ∃ a : RefinedIndex h κ, ∃ k : Fin (refinedHeight h a),
      x ∈ level f (bases f c B h) (refinedHeight h) a k := by
  intro x
  obtain ⟨a, k, y, hy, rfl⟩ := hcover x
  exact ⟨⟨a, word f c (h a) y⟩, k, y, ⟨hy, rfl⟩, rfl⟩

abbrev LevelIndex (h : ι → ℕ) := Σ a, Fin (h a)

def indexedLevel (f : X → X) (B : ι → Set X) (h : ι → ℕ)
    (a : LevelIndex h) : Set X := level f B h a.1 a.2

theorem pairwiseDisjoint_refinedLevels {f : X → X}
    (hf : Function.Injective f) (c : X → κ) (B : ι → Set X) (h : ι → ℕ)
    (hdisj : Pairwise (fun a b : LevelIndex h =>
      Disjoint (indexedLevel f B h a) (indexedLevel f B h b))) :
    Pairwise (fun a b : LevelIndex (refinedHeight h (κ := κ)) =>
      Disjoint (indexedLevel f (bases f c B h) (refinedHeight h) a)
        (indexedLevel f (bases f c B h) (refinedHeight h) b)) := by
  rintro ⟨⟨i, w⟩, k⟩ ⟨⟨j, v⟩, l⟩ hne
  apply Set.disjoint_left.mpr
  rintro x ⟨y, hy, hxy⟩ ⟨z, hz, hxz⟩
  have hiy : x ∈ indexedLevel f B h ⟨i, k⟩ := ⟨y, hy.1, hxy⟩
  have hjz : x ∈ indexedLevel f B h ⟨j, l⟩ := ⟨z, hz.1, hxz⟩
  by_cases hp : (⟨i, k⟩ : LevelIndex h) = ⟨j, l⟩
  · have hij : i = j := congrArg Sigma.fst hp
    subst j
    have hkl : k = l := eq_of_heq (Sigma.mk.inj hp).2
    subst l
    have hyz : y = z := hf.iterate k.val (hxy.trans hxz.symm)
    subst z
    have hwv : w = v := hy.2.symm.trans hz.2
    subst v
    exact hne rfl
  · exact Set.disjoint_left.mp (hdisj hp) hiy hjz

theorem colorFiber_eq_iUnion (f : X → X) (c : X → κ)
    (B : ι → Set X) (h : ι → ℕ)
    (hcover : ∀ x, ∃ a, ∃ k : Fin (h a), x ∈ level f B h a k) (t : κ) :
    c ⁻¹' {t} = ⋃ a : RefinedIndex h κ,
      ⋃ k : Fin (refinedHeight h a), ⋃ (_ : a.2 k = t),
        level f (bases f c B h) (refinedHeight h) a k := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, k, hax⟩ := refined_covers f c B h hcover x
    have hc : c x = a.2 k := image_refinedBase_subset_color f c
      (B a.1) (h a.1) a.2 k hax
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨k,
      Set.mem_iUnion.mpr ⟨hc.symm.trans hx, hax⟩⟩⟩
  · intro hx
    obtain ⟨a, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨k, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨ht, hax⟩ := Set.mem_iUnion.mp hx
    have hc : c x = a.2 k := image_refinedBase_subset_color f c
      (B a.1) (h a.1) a.2 k hax
    exact hc.trans ht

section MeasurableLevels
variable [MeasurableSpace X] [MeasurableSpace κ] [MeasurableSingletonClass κ]

theorem measurableSet_iterate_image (f : X ≃ᵐ X) {A : Set X}
    (hA : MeasurableSet A) (n : ℕ) : MeasurableSet ((f : X → X)^[n] '' A) := by
  induction n with
  | zero => simpa using hA
  | succ n ih =>
    rw [Function.iterate_succ', Set.image_comp]
    exact f.measurableSet_image.mpr ih

theorem measurableSet_refinedLevel (f : X ≃ᵐ X) {c : X → κ}
    (hc : Measurable c) {B : ι → Set X} (hB : ∀ a, MeasurableSet (B a))
    (h : ι → ℕ) (a : RefinedIndex h κ) (k : Fin (refinedHeight h a)) :
    MeasurableSet (level f (bases f c B h) (refinedHeight h) a k) := by
  exact measurableSet_iterate_image f
    (measurableSet_refinedBase f.measurable hc (hB a.1) (h a.1) a.2) k.val

end MeasurableLevels

noncomputable def partitionColor (P : κ → Set X) (hcover : ∀ x, ∃ a, x ∈ P a)
    (x : X) : κ := Classical.choose (hcover x)

theorem mem_partitionColor (P : κ → Set X) (hcover : ∀ x, ∃ a, x ∈ P a)
    (x : X) : x ∈ P (partitionColor P hcover x) := Classical.choose_spec (hcover x)

theorem partitionColor_fiber (P : κ → Set X)
    (hcover : ∀ x, ∃ a, x ∈ P a)
    (hdisj : Pairwise (fun a b => Disjoint (P a) (P b))) (a : κ) :
    partitionColor P hcover ⁻¹' {a} = P a := by
  ext x
  constructor
  · intro hx
    exact hx ▸ mem_partitionColor P hcover x
  · intro hx
    change partitionColor P hcover x = a
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) (mem_partitionColor P hcover x) hx

theorem measurable_partitionColor [MeasurableSpace X] [MeasurableSpace κ]
    [Countable κ] (P : κ → Set X) (hP : ∀ a, MeasurableSet (P a))
    (hcover : ∀ x, ∃ a, x ∈ P a)
    (hdisj : Pairwise (fun a b => Disjoint (P a) (P b))) :
    Measurable (partitionColor P hcover) := by
  intro s hs
  have heq : partitionColor P hcover ⁻¹' s = ⋃ a ∈ s, P a := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.mpr ⟨partitionColor P hcover x,
        Set.mem_iUnion.mpr ⟨hx, mem_partitionColor P hcover x⟩⟩
    · intro hx
      obtain ⟨a, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨ha, hxa⟩ := Set.mem_iUnion.mp hx
      have hcol : partitionColor P hcover x = a := by
        change x ∈ partitionColor P hcover ⁻¹' {a}
        rw [partitionColor_fiber P hcover hdisj a]
        exact hxa
      change partitionColor P hcover x ∈ s
      rwa [hcol]
  rw [heq]
  exact MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun _ => hP a))

theorem partitionAtom_eq_iUnion (f : X → X) (B : ι → Set X) (h : ι → ℕ)
    (htower : ∀ x, ∃ a, ∃ k : Fin (h a), x ∈ level f B h a k)
    (P : κ → Set X) (hcover : ∀ x, ∃ a, x ∈ P a)
    (hdisj : Pairwise (fun a b => Disjoint (P a) (P b))) (t : κ) :
    P t = ⋃ a : RefinedIndex h κ, ⋃ k : Fin (refinedHeight h a),
      ⋃ (_ : a.2 k = t),
        level f (bases f (partitionColor P hcover) B h) (refinedHeight h) a k := by
  rw [← partitionColor_fiber P hcover hdisj t]
  exact colorFiber_eq_iUnion f (partitionColor P hcover) B h htower t

section Finite
variable [Fintype ι] [Fintype κ]
open scoped BigOperators

theorem card_refinedIndex (h : ι → ℕ) :
    Fintype.card (RefinedIndex h κ) = ∑ a, Fintype.card κ ^ h a := by
  classical
  simp [RefinedIndex]

noncomputable def colorLevels (h : ι → ℕ) (t : κ) :
    Finset (LevelIndex (refinedHeight h (κ := κ))) := by
  classical
  exact Finset.univ.filter (fun a => a.1.2 a.2 = t)

@[simp] theorem mem_colorLevels (h : ι → ℕ) (t : κ)
    (a : LevelIndex (refinedHeight h (κ := κ))) :
    a ∈ colorLevels h t ↔ a.1.2 a.2 = t := by
  classical
  simp [colorLevels]

theorem colorFiber_eq_finset_union (f : X → X) (c : X → κ)
    (B : ι → Set X) (h : ι → ℕ)
    (hcover : ∀ x, ∃ a, ∃ k : Fin (h a), x ∈ level f B h a k) (t : κ) :
    c ⁻¹' {t} = ⋃ a ∈ colorLevels h t,
      indexedLevel f (bases f c B h) (refinedHeight h) a := by
  rw [colorFiber_eq_iUnion f c B h hcover t]
  ext x
  simp only [Set.mem_iUnion, mem_colorLevels]
  constructor
  · rintro ⟨a, k, hc, hx⟩
    exact ⟨⟨a, k⟩, hc, hx⟩
  · rintro ⟨⟨a, k⟩, hc, hx⟩
    exact ⟨a, k, hc, hx⟩

theorem indicator_colorFiber_eq_sum {f : X → X} (hf : Function.Injective f)
    (c : X → κ) (B : ι → Set X) (h : ι → ℕ)
    (hcover : ∀ x, ∃ a, ∃ k : Fin (h a), x ∈ level f B h a k)
    (hdisj : Pairwise (fun a b : LevelIndex h =>
      Disjoint (indexedLevel f B h a) (indexedLevel f B h b)))
    {E : Type*} [AddCommMonoid E] (g : X → E) (t : κ) (x : X) :
    (c ⁻¹' {t}).indicator g x = ∑ a ∈ colorLevels h t,
      (indexedLevel f (bases f c B h) (refinedHeight h) a).indicator g x := by
  classical
  rw [colorFiber_eq_finset_union f c B h hcover t]
  apply Finset.indicator_biUnion_apply
  intro a ha b hb hab
  exact pairwiseDisjoint_refinedLevels hf c B h hdisj hab

end Finite

end Invariant233.TowerItinerary

end OAI
