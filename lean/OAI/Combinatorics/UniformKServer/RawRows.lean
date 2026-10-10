import Mathlib
import OAI.Combinatorics.UniformKServer.RawCertificate
import OAI.Combinatorics.UniformKServer.RawExpansion

namespace OAI

noncomputable section
                              
section

namespace UniformKServer.RawRows
open RawArithmetic RawWords RawTable RawTyped RawExpansion RawCertificate

theorem selected_row {n k H b : ℕ} {T : List ℕ} (h : rowsOK n k H b T=true)
    (p c : List ℕ) (r : ℕ) (hp : p∈upto n H) (hc : c∈words n k) (hr : r<n) :
    rowOK k b T p c r=true := by
  exact List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h p hp) c hc) r (List.mem_range.mpr hr)

theorem sum_row {n k H b : ℕ} {T : List ℕ} (h : rowsOK n k H b T=true)
    (p : List (Fin n)) (c : Configuration n k) (r : Fin n) (hp : p.length≤H) :
    ∑j,kernel T (p,c) r j=2^b := by
  have hh := selected_row h (requests p) (config c) r.val (requests_mem p H hp) (config_mem c) r.isLt
  have hs := of_decide_eq_true (Bool.and_eq_true_iff.mp hh).1
  simpa only [kernel,range_eq_ofFn,List.map_ofFn,Function.comp_def,List.sum_ofFn] using hs

theorem forbidden_row {n k H b : ℕ} {T : List ℕ} (h : rowsOK n k H b T=true)
    (p : List (Fin n)) (c : Configuration n k) (r : Fin n) (j : Fin k) (hp : p.length≤H)
    (hhit : ∃ i,c i=r) (hbad : c j≠r) : kernel T (p,c) r j=0 := by
  have hh := selected_row h (requests p) (config c) r.val (requests_mem p H hp) (config_mem c) r.isLt
  have hf := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hh).2 j.val (List.mem_range.mpr j.isLt)
  have hx : (config c).any (fun x=>decide (x=r.val))=true := by
    apply List.any_eq_true.mpr
    obtain ⟨i,hi⟩:=hhit
    refine ⟨(c i).val,List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩
    simp [hi]
  have he : (c j).val≠r.val := by intro he;exact hbad (Fin.ext he)
  simpa only [hx,Bool.not_true,Bool.false_or,config_get,decide_eq_false he,Bool.false_or,
    decide_eq_true_eq,kernel] using hf

noncomputable def fallback {n k : ℕ} (hk : 0<k) (c : Configuration n k) (r : Fin n) : Fin k :=
  if h : ∃j,c j=r then Classical.choose h else ⟨0,hk⟩

theorem fallback_hit {n k : ℕ} (hk : 0<k) (c : Configuration n k) (r : Fin n)
    (h : ∃j,c j=r) : c (fallback hk c r)=r := by
  simp only [fallback,dite_eq_left h]
  exact Classical.choose_spec h

noncomputable def complete {n k : ℕ} (hk : 0<k) (H b : ℕ) (T : List ℕ)
    (s : State n k) (r : Fin n) (j : Fin k) : ℕ :=
  if s.1.length≤H then kernel T s r j else if j=fallback hk s.2 r then 2^b else 0

theorem total {n k H b : ℕ} {T : List ℕ} (hk : 0<k) (h : rowsOK n k H b T=true) :
    ∀(s : State n k) r,∑j,complete hk H b T s r j=2^b := by
  intro s r
  by_cases hp : s.1.length≤H
  · simp only [complete,ite_eq_left hp]
    exact sum_row h s.1 s.2 r hp
  · simp [complete,hp]

theorem forbidden {n k H b : ℕ} {T : List ℕ} (hk : 0<k) (h : rowsOK n k H b T=true) :
    ∀(s : State n k) r j,(∃i,s.2 i=r)→s.2 j≠r→complete hk H b T s r j=0 := by
  intro s r j hhit hbad
  by_cases hp : s.1.length≤H
  · simp only [complete,ite_eq_left hp]
    exact forbidden_row h s.1 s.2 r j hp hhit hbad
  · have hj : j≠fallback hk s.2 r := by intro he;exact hbad (he ▸ fallback_hit hk s.2 r hhit)
    simp [complete,hp,hj]

end UniformKServer.RawRows

end


end

end OAI
