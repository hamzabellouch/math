import Mathlib
import OAI.Combinatorics.KMedian.Programs.FinsetMaskProgram

namespace OAI


                                      
section
namespace MetricKMedian.MaskProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
def maximum (xs : List ℚ) : ℚ := xs.foldl max (xs.head?.getD 0)
 theorem maximum_eq_finset (xs : List ℚ) (U : Finset ℚ) (hU : U.Nonempty)
    (hm : ∀ q, q∈xs ↔ q∈U) : maximum xs=U.max' hU := by
  have hne : xs≠[] := by
    intro he
    obtain ⟨q,hq⟩ := hU
    have hx := (hm q).mpr hq
    rw [he] at hx
    cases hx
  have hd : xs.head?.getD 0∈xs := by
    cases xs with
    | nil => contradiction
    | cons a xs => exact List.mem_cons_self
  apply LPBinary.foldl_max_eq
  · exact le_max' U _ ((hm _).mp hd)
  · exact (hm _).mpr (max'_mem U hU)
  · intro q hq
    exact le_max' U q ((hm q).mp hq)
noncomputable def maxFold : PolyProgram (encodePair (encodeList Ratio.encode) Ratio.encode) Ratio.encode
    (fun x : List ℚ × ℚ => x.1.foldl max x.2) :=
  (listChoose ratLT 0).congr _ (fun x => by
    congr 1
    funext a b
    by_cases h : a<b
    · simp [h,max_eq_right h.le]
    · simp [h,max_eq_left (le_of_not_gt h)])
@[fun_prop] theorem maximum_poly : Poly maximum :=
  ⟨(((identity (encodeList Ratio.encode)).fanout (listHead Ratio.encode 0)).comp maxFold).congr _ (fun _ => rfl)⟩
def radius (x : List ℚ × Row) := maximum (selectedValues x)
@[fun_prop] theorem radius_poly : Poly radius := by unfold radius; fun_prop
 theorem radius_view {n : ℕ} (d : Fin n → ℚ) (U : Finset (Fin n)) (hU : U.Nonempty) :
    radius (List.ofFn d,setView U)=(U.image d).max' (hU.image _) :=
  maximum_eq_finset _ _ _ (selectedValues_mem d U)
end MetricKMedian.MaskProgram
end

end OAI
