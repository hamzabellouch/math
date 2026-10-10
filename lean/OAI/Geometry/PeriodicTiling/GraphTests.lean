import OAI.Geometry.PeriodicTiling.CyclicCoordinates
import Mathlib.Tactic.Abel

namespace OAI

universe uH uB uC

namespace PeriodicTilingThree

section RepresentationFibres

variable {H : Type uH} {B : Type uB} {C : Type uC} [AddCommGroup H]

theorem tiles_range_iff_unique_base (s : B → H) (hs : Function.Injective s)
    (F : Finset H) :
    Tiles F (Set.range s) ↔ ∀ y : H, ∃! b : B, y - s b ∈ F := by
  rw [tiles_iff_unique_tile]
  constructor
  · intro h y
    obtain ⟨f, hf, huniq⟩ := h y
    obtain ⟨b, hb⟩ := hf
    have hbf : y - s b = (f : H) := by rw [hb]; simp
    refine ⟨b, ?_, ?_⟩
    · change y - s b ∈ F
      rw [hbf]
      exact f.property
    · intro b' hb'
      let f' : ↥F := ⟨y - s b', hb'⟩
      have hf' : y - (f' : H) ∈ Set.range s := by
        refine ⟨b', ?_⟩
        simp [f']
      have he : (f' : H) = (f : H) := congrArg Subtype.val (huniq f' hf')
      apply hs
      exact sub_right_inj.mp (he.trans hbf.symm)
  · intro h y
    obtain ⟨b, hb, huniq⟩ := h y
    let f : ↥F := ⟨y - s b, hb⟩
    refine ⟨f, ?_, ?_⟩
    · refine ⟨b, ?_⟩
      simp [f]
    · intro f' hf'
      obtain ⟨b', hb'⟩ := hf'
      have hbf : y - s b' = (f' : H) := by rw [hb']; simp
      have hbb : b' = b := huniq b' (by
        change y - s b' ∈ F
        rw [hbf]
        exact f'.property)
      apply Subtype.ext
      change (f' : H) = y - s b
      rw [← hbf, hbb]

variable [AddCommGroup B] [AddCommGroup C]

theorem tiles_kernel_iff_unique_fibre (q : H →+ B)
    (hq : Function.Surjective q) (F : Finset H)
    (hF : ∀ x : H, x ∈ F ↔ q x = 0) (A : Set H) :
    Tiles F A ↔ ∀ b : B, ∃! a : A, q (a : H) = b := by
  constructor
  · intro h b
    obtain ⟨y, hy⟩ := hq b
    obtain ⟨⟨f, a⟩, hfa⟩ := h.2 y
    change (f : H) + (a : H) = y at hfa
    have hqa : q (a : H) = b := by
      have he := congrArg q hfa
      rw [map_add, (hF _).mp f.property, zero_add, hy] at he
      exact he
    refine ⟨a, hqa, ?_⟩
    intro a' ha'
    have hmem : y - (a' : H) ∈ F := by
      apply (hF _).mpr
      rw [map_sub, hy, ha', sub_self]
    let f' : ↥F := ⟨y - (a' : H), hmem⟩
    have he : ((f', a') : ↥F × A) = (f, a) := by
      apply h.1
      change (y - (a' : H)) + (a' : H) = (f : H) + (a : H)
      rw [sub_add_cancel, hfa]
    exact congrArg Prod.snd he
  · intro h
    constructor
    · rintro ⟨f, a⟩ ⟨f', a'⟩ he
      have hqa : q (a : H) = q (a' : H) := by
        have he' := congrArg q he
        simpa only [map_add, (hF _).mp f.property,
          (hF _).mp f'.property, zero_add] using he'
      obtain ⟨a₀, _ha₀, huniq⟩ := h (q (a : H))
      have haa : a = a' := (huniq a rfl).trans (huniq a' hqa.symm).symm
      have hff : f = f' := by
        apply Subtype.ext
        have hv := congrArg Subtype.val haa
        change (f : H) + (a : H) = (f' : H) + (a' : H) at he
        rw [hv] at he
        exact add_right_cancel he
      exact Prod.ext hff haa
    · intro y
      obtain ⟨a, ha, _huniq⟩ := h (q y)
      have hmem : y - (a : H) ∈ F := by
        apply (hF _).mpr
        rw [map_sub, ha, sub_self]
      refine ⟨(⟨y - (a : H), hmem⟩, a), ?_⟩
      exact sub_add_cancel y (a : H)

theorem tiles_invariance_iff (q : H →+ B) (ψ : H →+ C)
    (s : B → H) (hs : ∀ b, q (s b) = b)
    (σ : B) (F : Finset H)
    (hF : ∀ v : H, v ∈ F ↔
      (q v = 0 ∧ ψ v ≠ 0) ∨ (q v = σ ∧ ψ v = 0)) :
    Tiles F (Set.range s) ↔ ∀ b, ψ (s (b - σ)) = ψ (s b) := by
  have hinj : Function.Injective s := fun b b' h => by
    have := congrArg q h
    simpa only [hs] using this
  have hmem (y : H) (b : B) : y - s b ∈ F ↔
      (q y = b ∧ ψ y ≠ ψ (s b)) ∨
      (q y = σ + b ∧ ψ y = ψ (s b)) := by
    simpa only [map_sub, hs, sub_eq_zero, sub_ne_zero,
      sub_eq_iff_eq_add, zero_add] using hF (y - s b)
  rw [tiles_range_iff_unique_base s hinj F]
  constructor
  · intro h b
    obtain ⟨b', hb', _huniq⟩ := h (s b)
    rcases (hmem _ _).mp hb' with ⟨hq, hne⟩ | ⟨hq, he⟩
    · rw [hs] at hq
      exact False.elim (hne (congrArg (fun b => ψ (s b)) hq))
    · rw [hs] at hq
      have hb : b' = b - σ := by rw [hq]; abel
      rw [hb] at he
      exact he.symm
  · intro h y
    by_cases he : ψ y = ψ (s (q y))
    · refine ⟨q y - σ, ?_, ?_⟩
      · apply (hmem _ _).mpr
        exact Or.inr ⟨by abel, he.trans (h (q y)).symm⟩
      · intro b hb
        rcases (hmem _ _).mp hb with ⟨hq, hne⟩ | ⟨hq, _he⟩
        · exact False.elim (hne (hq ▸ he))
        · rw [hq]
          abel
    · refine ⟨q y, (hmem _ _).mpr (Or.inl ⟨rfl, he⟩), ?_⟩
      intro b hb
      rcases (hmem _ _).mp hb with ⟨hq, _hne⟩ | ⟨hq, he'⟩
      · exact hq.symm
      · have hb : b = q y - σ := by rw [hq]; abel
        rw [hb, h (q y)] at he'
        exact False.elim (he he')

end RepresentationFibres

noncomputable section Concrete

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

local instance : DecidableEq (Ambient E) := Classical.decEq _

def usefulCoord (i : Channel p) : Ambient E →+ P E i where
  toFun v := (v.2.2 i).2
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem usefulCoord_apply (i : Channel p) (v : Ambient E) :
    usefulCoord E i v = (v.2.2 i).2 := rfl

@[simp] theorem usefulCoord_point (i : Channel p) (o : GraphOutputs E) (b : Base E) :
    usefulCoord E i (point o b) = o.c b i := rfl

private theorem kernel_horizontal_zero (v : (q0 E).ker) :
    (v : Ambient E).1 = 0 := by
  have hv := congrArg Prod.fst v.property
  exact hv

noncomputable instance kernelFintype : Fintype (q0 E).ker :=
  Fintype.ofInjective (fun v : (q0 E).ker => (v : Ambient E).2) (by
    intro v w h
    apply Subtype.ext
    exact Prod.ext ((kernel_horizontal_zero E v).trans
      (kernel_horizontal_zero E w).symm) h)

def kernelTile : Finset (Ambient E) :=
  (Finset.univ : Finset (q0 E).ker).map ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem mem_kernelTile (v : Ambient E) :
    v ∈ kernelTile E ↔ q0 E v = 0 := by
  constructor
  · intro hv
    obtain ⟨w, _hw, rfl⟩ := Finset.mem_map.mp hv
    exact w.property
  · intro hv
    exact Finset.mem_map.mpr ⟨⟨v, hv⟩, Finset.mem_univ _, rfl⟩

theorem kernelTile_nonempty : (kernelTile E).Nonempty :=
  ⟨0, (mem_kernelTile E 0).mpr (map_zero _)⟩

def baseLift (b : Base E) : Ambient E := point (zeroOutputs E) b

@[simp] theorem q0_baseLift (b : Base E) : q0 E (baseLift E b) = b :=
  q0_point (zeroOutputs E) b

@[simp] theorem usefulCoord_baseLift (i : Channel p) (b : Base E) :
    usefulCoord E i (baseLift E b) = 0 := rfl

theorem kernelTile_iff_unique_fibre (A : Set (Ambient E)) :
    Tiles (kernelTile E) A ↔
      ∀ b : Base E, ∃! a : A, q0 E (a : Ambient E) = b :=
  tiles_kernel_iff_unique_fibre (q0 E) (q0_surjective E) (kernelTile E)
    (mem_kernelTile E) A

theorem kernelTile_graph (o : GraphOutputs E) : Tiles (kernelTile E) (graph o) := by
  apply (tiles_range_iff_unique_base (point o) (point_injective o) (kernelTile E)).mpr
  intro y
  refine ⟨q0 E y, ?_, ?_⟩
  · change y - point o (q0 E y) ∈ kernelTile E
    rw [mem_kernelTile, map_sub, q0_point, sub_self]
  · intro b hb
    rw [mem_kernelTile, map_sub, q0_point, sub_eq_zero] at hb
    exact hb.symm

theorem kernelTile_iff_graph (A : Set (Ambient E)) :
    Tiles (kernelTile E) A ↔ ∃ o : GraphOutputs E, graph o = A := by
  classical
  constructor
  · intro h
    have hf := (kernelTile_iff_unique_fibre E A).mp h
    let a : Base E → A := fun b => Classical.choose (hf b)
    have ha (b : Base E) : q0 E (a b : Ambient E) = b :=
      (Classical.choose_spec (hf b)).1
    let s : Base E → Ambient E := fun b => (a b : Ambient E)
    have hs : ∀ b, q0 E (s b) = b := ha
    refine ⟨outputsOfSection s hs, ?_⟩
    rw [graph_outputsOfSection]
    ext y
    constructor
    · rintro ⟨b, rfl⟩
      exact (a b).property
    · intro hy
      refine ⟨q0 E y, ?_⟩
      have he : (⟨y, hy⟩ : A) = a (q0 E y) :=
        (Classical.choose_spec (hf (q0 E y))).2 ⟨y, hy⟩ rfl
      exact (congrArg Subtype.val he).symm
  · rintro ⟨o, rfl⟩
    exact kernelTile_graph E o

def invarianceZero (i : Channel p) : Finset (Ambient E) :=
  (kernelTile E).filter (fun v => usefulCoord E i v = 0)

def invarianceNonzero (i : Channel p) : Finset (Ambient E) :=
  (kernelTile E).filter (fun v => usefulCoord E i v ≠ 0)

def invarianceTile (i : Channel p) (σ : Base E) : Finset (Ambient E) :=
  invarianceNonzero E i ∪
    (invarianceZero E i).image (fun v => baseLift E σ + v)

theorem mem_invarianceTile (i : Channel p) (σ : Base E) (v : Ambient E) :
    v ∈ invarianceTile E i σ ↔
      (q0 E v = 0 ∧ usefulCoord E i v ≠ 0) ∨
      (q0 E v = σ ∧ usefulCoord E i v = 0) := by
  constructor
  · intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Or.inl (by simpa only [invarianceNonzero, Finset.mem_filter,
        mem_kernelTile] using hv)
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      have hw' : q0 E w = 0 ∧ usefulCoord E i w = 0 := by
        simpa only [invarianceZero, Finset.mem_filter, mem_kernelTile] using hw
      exact Or.inr ⟨by rw [map_add, q0_baseLift, hw'.1, add_zero],
        by rw [map_add, usefulCoord_baseLift, hw'.2, add_zero]⟩
  · rintro (⟨hq, hc⟩ | ⟨hq, hc⟩)
    · apply Finset.mem_union.mpr
      exact Or.inl (by simpa only [invarianceNonzero, Finset.mem_filter,
        mem_kernelTile] using And.intro hq hc)
    · apply Finset.mem_union.mpr
      apply Or.inr
      apply Finset.mem_image.mpr
      refine ⟨v - baseLift E σ, ?_, ?_⟩
      · rw [invarianceZero, Finset.mem_filter, mem_kernelTile]
        constructor
        · rw [map_sub, hq, q0_baseLift, sub_self]
        · rw [map_sub, hc, usefulCoord_baseLift, sub_self]
      · abel

theorem invarianceTile_nonempty (i : Channel p) (σ : Base E) :
    (invarianceTile E i σ).Nonempty := by
  refine ⟨baseLift E σ, (mem_invarianceTile E i σ _).mpr (Or.inr ?_)⟩
  exact ⟨q0_baseLift E σ, usefulCoord_baseLift E i σ⟩

theorem invarianceTile_disjoint (i : Channel p) (σ : Base E) :
    Disjoint (invarianceNonzero E i)
      ((invarianceZero E i).image (fun v => baseLift E σ + v)) := by
  apply Finset.disjoint_left.mpr
  intro v hv hv'
  have hne : usefulCoord E i v ≠ 0 := (Finset.mem_filter.mp hv).2
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv'
  have hw0 : usefulCoord E i w = 0 := (Finset.mem_filter.mp hw).2
  apply hne
  rw [map_add, usefulCoord_baseLift, hw0, add_zero]

theorem invarianceTile_card (i : Channel p) (σ : Base E) :
    (invarianceTile E i σ).card = (kernelTile E).card := by
  rw [invarianceTile, Finset.card_union_of_disjoint (invarianceTile_disjoint E i σ),
    Finset.card_image_of_injective _ (fun _ _ h => add_left_cancel h)]
  have hpart : invarianceNonzero E i ∪ invarianceZero E i = kernelTile E := by
    ext v
    simp only [invarianceNonzero, invarianceZero, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
    · intro hv
      by_cases hc : usefulCoord E i v = 0
      · exact Or.inr ⟨hv, hc⟩
      · exact Or.inl ⟨hv, hc⟩
  have hdisj : Disjoint (invarianceNonzero E i) (invarianceZero E i) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hw).2
  rw [← Finset.card_union_of_disjoint hdisj, hpart]

theorem invarianceTile_iff (i : Channel p) (σ : Base E) (o : GraphOutputs E) :
    Tiles (invarianceTile E i σ) (graph o) ↔
      ∀ b, o.c (b - σ) i = o.c b i := by
  exact tiles_invariance_iff (q0 E) (usefulCoord E i) (point o)
    (q0_point o) σ (invarianceTile E i σ) (mem_invarianceTile E i σ)

end Concrete

end PeriodicTilingThree

end OAI
