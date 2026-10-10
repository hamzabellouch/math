import Mathlib
import OAI.Combinatorics.UniformKServer.Basic
import OAI.Combinatorics.UniformKServer.RawPath

namespace OAI

                               
section

namespace UniformKServer.RawTyped
open RawArithmetic RawWords RawTable RawPath

def requests {n : ℕ} (w : List (Fin n)) : List ℕ := w.map Fin.val
def config {n k : ℕ} (c : Configuration n k) : List ℕ := List.ofFn fun j=> (c j).val
def events {n k : ℕ} (h : History n k) : List (ℕ×ℕ) := h.map fun x=>(x.1.val,x.2.val)

theorem config_get {n k : ℕ} (c : Configuration n k) (j : Fin k) :
    (config c).getD j.val 0=(c j).val := by
  rw [List.getD_eq_getElem _ _ (by simp [config])]
  simp [config]

theorem config_set {n k : ℕ} (c : Configuration n k) (r : Fin n) (j : Fin k) :
    (config c).set j.val r.val=config (serve c r j) := by
  apply List.ext_getElem
  · simp [config]
  · intro i hi hj
    simp only [List.length_set,List.length_ofFn,config] at hi hj ⊢
    rw [List.getElem_set]
    simp only [List.getElem_ofFn,serve,Function.update_apply]
    by_cases h : j.val=i
    · have he : (⟨i,hj⟩:Fin k)=j := Fin.ext h.symm
      simp [h,he]
    · have he : (⟨i,hj⟩:Fin k)≠j := by intro he;exact h (congrArg Fin.val he).symm
      simp [h,he]

theorem history_zip {n k : ℕ} (w : List (Fin n)) (g : List (Fin k)) (h : w.length=g.length) :
    history (requests w) (requests g)=events (w.zip g) := by
  induction w generalizing g with
  | nil=>simp [requests,history,events]
  | cons r w ih=>
    cases g with
    | nil=>simp at h
    | cons j g=>
      have h' : w.length=g.length := by simpa using h
      simpa only [requests,List.map_cons,history_cons,List.zip_cons_cons,events] using
        congrArg ((r.val,j.val)::·) (ih g h')

theorem config_mem {n k : ℕ} (c : Configuration n k) : config c∈words n k := by
  apply (mem_words n k _).mpr
  refine ⟨by simp [config],?_⟩
  intro r hr
  rcases List.mem_ofFn.mp hr with ⟨j,rfl⟩
  exact (c j).isLt

theorem requests_mem {n : ℕ} (w : List (Fin n)) (H : ℕ) (hw : w.length≤H) :
    requests w∈upto n H := by
  apply (mem_upto n H _).mpr
  refine ⟨by simpa [requests] using hw,?_⟩
  intro r hr
  rcases List.mem_map.mp hr with ⟨x,hx,rfl⟩
  exact x.isLt

end UniformKServer.RawTyped

end



end OAI
