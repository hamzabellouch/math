import Mathlib
import OAI.Combinatorics.UniformKServer.RawRows
import OAI.Combinatorics.UniformKServer.RawRepresentation

namespace OAI

noncomputable section
                                      
section

namespace UniformKServer.RawCompleteness
open RawArithmetic RawWords RawTable RawTyped RawExpansion RawCertificate RawRows RawRepresentation

theorem config_any {n k : ℕ} (c : Configuration n k) (r : Fin n) :
    (config c).any (fun x=>decide (x=r.val))=true ↔ ∃j,c j=r := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x,hx,he⟩
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hx
    exact ⟨j,Fin.ext (of_decide_eq_true he)⟩
  · rintro ⟨j,hj⟩
    exact ⟨(c j).val,List.mem_ofFn.mpr ⟨j,rfl⟩,by simp [hj]⟩

theorem row_ok {n k b : ℕ} (T : List ℕ) (p : List (Fin n)) (c : Configuration n k)
    (r : Fin n) (N : Fin k→ℕ) (hrep : ∀j,entry T (requests p) (config c) r.val j.val=N j)
    (hN : ∑j,N j=2^b) (hl : ∀j,(∃i,c i=r)→c j≠r→N j=0) :
    rowOK k b T (requests p) (config c) r.val=true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [range_eq_ofFn]
    simpa only [List.map_ofFn,Function.comp_def,hrep,List.sum_ofFn] using hN
  · apply List.all_eq_true.mpr
    intro j hj
    let j' : Fin k := ⟨j,List.mem_range.mp hj⟩
    change (!(config c).any (fun x=>decide (x=r.val)) ||
      decide ((config c).getD j'.val 0=r.val) ||
        decide (entry T (requests p) (config c) r.val j'.val=0))=true
    rw [config_get,hrep]
    by_cases hh : ∃i,c i=r
    · have ha := (config_any c r).mpr hh
      by_cases hjr : c j'=r
      · simp [hjr]
      · have hn : (c j').val≠r.val := fun h=>hjr (Fin.ext h)
        simp [ha,hn,hl j' hh hjr]
    · have ha : (config c).any (fun x=>decide (x=r.val))=false :=
        Bool.eq_false_of_not_eq_true (fun h=>hh ((config_any c r).mp h))
      simp [ha]

theorem rows_ok {n k H b : ℕ} (T : List ℕ)
    (N : State n k→Fin n→Fin k→ℕ)
    (hrep : ∀p c r j,p.length≤H→entry T (requests p) (config c) r.val j.val=N (p,c) r j)
    (hN : ∀s r,∑j,N s r j=2^b)
    (hl : ∀s r j,(∃i,s.2 i=r)→s.2 j≠r→N s r j=0) : rowsOK n k H b T=true := by
  apply List.all_eq_true.mpr
  intro p hp
  obtain ⟨hlen,hp'⟩ := (mem_upto n H p).mp hp
  obtain ⟨p',rfl⟩:=lift_list p hp'
  apply List.all_eq_true.mpr
  intro c hc
  obtain ⟨c',rfl⟩:=lift_config c hc
  apply List.all_eq_true.mpr
  intro r hr
  let r' : Fin n := ⟨r,List.mem_range.mp hr⟩
  exact row_ok T p' c' r' (N (p',c') r')
    (fun j=>hrep p' c' r' j (by simpa [requests] using hlen)) (hN _ _) (hl (p',c') r')

theorem rowCost_eq {n k H b : ℕ} (hk : 0<k) (T : List ℕ)
    (N : State n k→Fin n→Fin k→ℕ)
    (hrep : ∀p c r j,p.length≤H→entry T (requests p) (config c) r.val j.val=N (p,c) r j)
    (d : RationalMetric n) (p : List (Fin n)) (c : Configuration n k) (w : List (Fin n))
    (hw : p.length+w.length≤H) :
    BitSampling.rowCost (b:=b) (complete hk H b T) next (charge d) (p,c) w=
      BitSampling.rowCost (b:=b) N next (charge d) (p,c) w := by
  induction w generalizing p c with
  | nil=>rfl
  | cons r w ih=>
    have hp : p.length≤H := by simp only [List.length_cons] at hw;omega
    simp only [BitSampling.rowCost,complete,ite_eq_left hp,kernel,hrep p c r _ hp,next]
    congr 1
    funext j
    rw [ih]
    simp only [List.length_append,List.length_cons,List.length_nil] at *
    omega

end UniformKServer.RawCompleteness

end


end

end OAI
