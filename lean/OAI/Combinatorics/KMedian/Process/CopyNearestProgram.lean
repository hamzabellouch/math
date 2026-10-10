import Mathlib
import OAI.Combinatorics.KMedian.Process.CopyGraphProgram
import OAI.Combinatorics.KMedian.Geometry.NearestReindex
import OAI.Combinatorics.KMedian.Programs.NearestMaskProgram
import OAI.Combinatorics.KMedian.Geometry.RationalGridRound
import OAI.Combinatorics.KMedian.Programs.MaximumProgram

namespace OAI


                                          
section
namespace MetricKMedian.FixedBatch.RationalParameters.CopyNearestProgram
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open RationalPhysicalKernel RationalPhysicalKernel.CopyList
open SparseGraph.ListOperation (Row Table setView indices)
variable {τ : ℝ} (q : RationalParameters τ)
local instance {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder

def distances (Δ : ℕ) (x : List ℚ × Row) : List ℚ := (indices x.2).map (fun k => x.1[k/Δ]?.getD 0)
@[fun_prop] theorem distances_poly (Δ : ℕ) : Poly (distances Δ) := by unfold distances; apply list_map <;> fun_prop
 theorem distances_view {f Δ : ℕ} (d : Fin f → ℚ) (A : Finset (CopyState.Copy (F:=Fin f) Δ)) :
    distances Δ (List.ofFn d,view A)=List.ofFn (fun k : Fin (f*Δ) => d (finProdFinEquiv.symm k).1) := by
  simp only [distances,indices,view,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  have hk : k.val/Δ=(finProdFinEquiv.symm k).1.val := by
    simpa only [rank,Equiv.apply_symm_apply] using CopyGraphProgram.rank_owner (finProdFinEquiv.symm k)
  simp only [Function.comp_def,hk,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]

def nearestRaw (Δ : ℕ) (x : List ℚ × Row) : Row :=
  Preparation.RationalNearest.MaskProgram.raw Δ (distances Δ x,x.2)
@[fun_prop] theorem nearestRaw_poly (Δ : ℕ) : Poly (nearestRaw Δ) := by unfold nearestRaw; fun_prop
 theorem nearestRaw_view {f j : ℕ} (d : Fin j → Fin f → ℚ) (A : Finset (CopyState.Copy (F:=Fin f) q.Δ)) (c : Fin j) :
    nearestRaw q.Δ (List.ofFn (d c),view A)=view (q.nearest d A c) := by
  unfold nearestRaw
  rw [distances_view,view,Preparation.RationalNearest.MaskProgram.raw_view]
  exact congrArg setView (Preparation.RationalNearest.takeNearest_map orderEquiv (fun a => d c a.1) q.Δ A)

def radiusRaw (Δ : ℕ) (x : List ℚ × Row) : ℚ :=
  MetricKMedian.MaskProgram.radius (distances Δ x,nearestRaw Δ x)
@[fun_prop] theorem radiusRaw_poly (Δ : ℕ) : Poly (radiusRaw Δ) := by unfold radiusRaw; fun_prop
 theorem radiusRaw_view {f j : ℕ} (d : Fin j → Fin f → ℚ) (A : Finset (CopyState.Copy (F:=Fin f) q.Δ))
    (hA : q.Δ≤A.card) (c : Fin j) : radiusRaw q.Δ (List.ofFn (d c),view A)=q.radius d A hA c := by
  unfold radiusRaw
  rw [distances_view,nearestRaw_view q]
  unfold view
  rw [MetricKMedian.MaskProgram.radius_view _ _ ((q.nearest_nonempty d A hA c).map)]
  have he : ((q.nearest d A c).map finProdFinEquiv.toEmbedding).image
      (fun k => d c (finProdFinEquiv.symm k).1)=(q.nearest d A c).image (fun a => d c a.1) := by
    ext r
    simp only [mem_image,mem_map]
    constructor
    · rintro ⟨b,⟨a,ha,rfl⟩,h⟩; exact ⟨a,ha,by simpa using h⟩
    · rintro ⟨a,ha,rfl⟩; exact ⟨finProdFinEquiv a,⟨a,ha,rfl⟩,by simp⟩
  simp only [he,RationalParameters.radius]
end MetricKMedian.FixedBatch.RationalParameters.CopyNearestProgram
end

end OAI
