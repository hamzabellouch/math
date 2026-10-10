import Mathlib
import OAI.Combinatorics.KMedian.Process.CopyListEncoding
import OAI.Combinatorics.KMedian.Geometry.RationalNearestCopies

namespace OAI


                                      
section
namespace MetricKMedian.Preparation.RationalNearest
open Finset
variable {α β : Type} [LinearOrder α] [LinearOrder β]
theorem min_map (e : α ≃o β) (U : Finset α) (hU : U.Nonempty) :
    (U.map e.toEmbedding).min' (hU.map) = e (U.min' hU) := by
  apply le_antisymm
  · exact min'_le _ _ (mem_map.mpr ⟨_,min'_mem U hU,rfl⟩)
  · obtain ⟨a,ha,he⟩ := mem_map.mp (min'_mem (U.map e.toEmbedding) (hU.map))
    rw [← he]
    exact e.monotone (min'_le U a ha)
 theorem least_map (e : α ≃o β) (U : Finset α) (d : α → ℚ) (hU : U.Nonempty) :
    least (U.map e.toEmbedding) (fun b => d (e.symm b)) (hU.map)=e (least U d hU) := by
  have him : (U.map e.toEmbedding).image (fun b => d (e.symm b))=U.image d := by
    ext q
    simp only [mem_image,mem_map]
    constructor
    · rintro ⟨b,⟨a,ha,rfl⟩,h⟩; exact ⟨a,ha,by simpa using h⟩
    · rintro ⟨a,ha,rfl⟩; exact ⟨e a,⟨a,ha,rfl⟩,by simp⟩
  unfold least
  have hf : (U.map e.toEmbedding).filter (fun b => d (e.symm b)=(U.image d).min' (hU.image _))=
      (U.filter (fun a => d a=(U.image d).min' (hU.image _))).map e.toEmbedding := by
    ext b
    simp only [mem_filter,mem_map]
    constructor
    · rintro ⟨⟨a,ha,rfl⟩,hh⟩; exact ⟨a,⟨ha,by simpa using hh⟩,rfl⟩
    · rintro ⟨a,⟨ha,hh⟩,rfl⟩; exact ⟨⟨a,ha,rfl⟩,by simpa using hh⟩
  simp only [him]
  simp only [hf]
  exact min_map e _ _

 theorem takeNearest_map (e : α ≃o β) (d : α → ℚ) (t : ℕ) (U : Finset α) :
    takeNearest (fun b => d (e.symm b)) t (U.map e.toEmbedding)=(takeNearest d t U).map e.toEmbedding := by
  induction t generalizing U with
  | zero => simp only [takeNearest,map_empty]
  | succ t ih =>
    by_cases hU : U.Nonempty
    · rw [takeNearest,takeNearest,dite_eq_left hU,dite_eq_left (hU.map),least_map e U d hU]
      have he : (U.map e.toEmbedding).erase (e (least U d hU))=(U.erase (least U d hU)).map e.toEmbedding := by
        exact (map_erase e.toEmbedding U (least U d hU)).symm
      rw [he,ih,map_insert]
      rfl
    · have he := not_nonempty_iff_eq_empty.mp hU
      subst U
      simp [takeNearest]
end MetricKMedian.Preparation.RationalNearest

namespace MetricKMedian.RationalPhysicalKernel.CopyList
open CopyState
variable {f Δ : ℕ}
local instance : LinearOrder (Copy (F:=Fin f) Δ) := copyOrder

def orderEquiv : @OrderIso (Copy (F:=Fin f) Δ) (Fin (f*Δ)) (copyOrder (F:=Fin f) (Δ:=Δ)).toLE inferInstance where
  toEquiv := finProdFinEquiv
  map_rel_iff' := @StrictMono.le_iff_le _ _ (copyOrder (F:=Fin f) (Δ:=Δ)) _ _ rank_strictMono
end MetricKMedian.RationalPhysicalKernel.CopyList
end

end OAI
