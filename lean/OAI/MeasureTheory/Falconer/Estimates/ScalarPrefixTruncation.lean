import OAI.MeasureTheory.Falconer.Estimates.ScalarPathNodes

namespace OAI

/-! Truncation retains all prefix fibers above the truncation depth. -/
namespace Falconer.Regularization

 theorem prefixFiber_image_take (L : Finset (CellPath 1)) {a t : ℕ}
    (hat : a ≤ t) (p : CellPath 1) :
    prefixFiber (L.image (List.take t)) a p = (prefixFiber L a p).image (List.take t) := by
  classical
  ext c
  constructor
  · intro hc
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hc).1
    have hparent := (Finset.mem_filter.mp hc).2
    simp only [List.take_take,min_eq_left hat] at hparent
    exact Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨hu,hparent⟩,rfl⟩
  · intro hc
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_filter.mp hu).1,
      by simpa only [List.take_take,min_eq_left hat] using (Finset.mem_filter.mp hu).2⟩

 theorem prefixChildren_image_take (L : Finset (CellPath 1)) {a b t : ℕ}
    (hat : a ≤ t) (hbt : b ≤ t) (p : CellPath 1) :
    prefixChildren (L.image (List.take t)) a b p = prefixChildren L a b p := by
  classical
  simp only [prefixChildren,prefixFiber_image_take L hat,Finset.image_image,
    Function.comp_def,List.take_take,min_eq_left hbt]

 theorem prefix_image_take_take (L : Finset (CellPath 1)) {a t : ℕ} (hat : a ≤ t) :
    (L.image (List.take t)).image (List.take a) = L.image (List.take a) := by
  classical
  simp only [Finset.image_image,Function.comp_def,List.take_take,min_eq_left hat]

 theorem prefix_image_take_cubePaths {N t : ℕ} {L : Finset (CellPath 1)}
    (hL : L ⊆ cubePaths 1 N) (ht : t ≤ N) :
    L.image (List.take t) ⊆ cubePaths 1 t := by
  classical
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  have hlen := (mem_cubePaths 1 N q).mp (hL hq)
  simp only [mem_cubePaths,List.length_take,hlen,min_eq_left ht]

 theorem prefixChildren_same (L : Finset (CellPath 1)) {a : ℕ} {p : CellPath 1}
    (hp : p ∈ L.image (List.take a)) : prefixChildren L a a p = {p} := by
  classical
  ext c
  constructor
  · intro hc
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
    simpa only [Finset.mem_singleton] using (Finset.mem_filter.mp hq).2
  · intro hc
    have heq := Finset.mem_singleton.mp hc
    subst c
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hq,rfl⟩)

 theorem prefixChildren_card_compose (L : Finset (CellPath 1)) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (p : CellPath 1) :
    (prefixChildren L a c p).card =
      ∑ q ∈ prefixChildren L a b p, (prefixChildren L b c q).card := by
  classical
  have hh := prefixFiber_card_sum (C := L.image (List.take c)) hab p
  rw [prefixFiber_image_take L (hab.trans hbc),
    prefixChildren_image_take L (hab.trans hbc) hbc] at hh
  change (prefixChildren L a c p).card = _ at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro q _
  rw [prefixFiber_image_take L hbc]
  rfl

end Falconer.Regularization

end OAI
