import OAI.MeasureTheory.Falconer.Estimates.PrefixCounting

namespace OAI

/-! Exact planar prefix identities at the endpoint of a profile interval. -/
namespace Falconer.Regularization

theorem planar_prefixFiber_image_take (L : Finset (CellPath 2)) {a t : ℕ}
    (hat : a ≤ t) (p : CellPath 2) :
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

theorem planar_prefixChildren_image_take (L : Finset (CellPath 2)) {a b t : ℕ}
    (hat : a ≤ t) (hbt : b ≤ t) (p : CellPath 2) :
    prefixChildren (L.image (List.take t)) a b p = prefixChildren L a b p := by
  classical
  simp only [prefixChildren,planar_prefixFiber_image_take L hat,Finset.image_image,
    Function.comp_def,List.take_take,min_eq_left hbt]

theorem planar_prefix_image_take_take (L : Finset (CellPath 2)) {a t : ℕ} (hat : a ≤ t) :
    (L.image (List.take t)).image (List.take a) = L.image (List.take a) := by
  classical
  simp only [Finset.image_image,Function.comp_def,List.take_take,min_eq_left hat]

theorem planar_prefix_image_take_cubePaths {N t : ℕ} {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (ht : t ≤ N) : L.image (List.take t) ⊆ cubePaths 2 t := by
  classical
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  have hlen := (mem_cubePaths 2 N q).mp (hL hq)
  simp only [mem_cubePaths,List.length_take,hlen,min_eq_left ht]

end Falconer.Regularization

end OAI
