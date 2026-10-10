import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalTaper
import OAI.Combinatorics.KMedian.Binary.BinaryAutoExtras

namespace OAI


                                        
section
namespace MetricKMedian.Taper.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly Finset
abbrev Row := List ℚ
abbrev Raw := (ℚ × ℚ) × Row

def upper (ds : Row) : ℚ := 1+(ds.map (fun q => 1/q)).sum
def breaks (x : ℚ × Row) : Row := 0::upper x.2::((x.2.map (fun q => (1-x.1)/q))++x.2.map (fun q => 1/q))
def aSum (x : (ℚ × Row) × ℚ) : ℚ := (x.1.2.map (fun q => aCoef x.1.1 q x.2)).sum
def bSum (x : (ℚ × Row) × ℚ) : ℚ := (x.1.2.map (fun q => bCoef x.1.1 q x.2)).sum
def candidateList (x : Raw) : Row :=
  let bs := breaks (x.1.2,x.2)
  bs++bs.flatMap (fun a => bs.map (fun b => (aSum ((x.1.2,x.2),(a+b)/2)-1/x.1.1)/bSum ((x.1.2,x.2),(a+b)/2)))
def mass (x : Raw × ℚ) : ℚ := (x.1.2.map (fun d => x.1.1.1*rationalMarginal x.1.1.2 d x.2)).sum
def roots (x : Raw) : Row := (candidateList x).filter (fun q => decide (0<q) && decide (mass (x,q)=1))
def radius (x : Raw) : ℚ := (roots x).foldl max 0

@[fun_prop] theorem upper_poly : Poly upper := by
  unfold upper
  have h : Poly (fun ds : Row => ds.map (fun q => 1/q)) := by apply list_map <;> fun_prop
  fun_prop
@[fun_prop] theorem breaks_poly : Poly breaks := by
  unfold breaks
  have h : Poly (fun x : ℚ × Row => x.2.map (fun q => (1-x.1)/q)) := by apply list_map <;> fun_prop
  have h' : Poly (fun x : ℚ × Row => x.2.map (fun q => 1/q)) := by apply list_map <;> fun_prop
  fun_prop
@[fun_prop] theorem aSum_poly : Poly aSum := by
  unfold aSum
  apply comp rat_sum
  apply list_map
  · unfold aCoef; fun_prop
  · fun_prop
@[fun_prop] theorem bSum_poly : Poly bSum := by
  unfold bSum
  apply comp rat_sum
  apply list_map
  · unfold bCoef; fun_prop
  · fun_prop
@[fun_prop] theorem candidateList_poly : Poly candidateList := by
  unfold candidateList
  dsimp only
  apply comp (f:=fun x : Row × Row => x.1++x.2) (g:=fun x : Raw => (breaks (x.1.2,x.2), (breaks (x.1.2,x.2)).flatMap (fun a => (breaks (x.1.2,x.2)).map (fun b => (aSum ((x.1.2,x.2),(a+b)/2)-1/x.1.1)/bSum ((x.1.2,x.2),(a+b)/2))))) list_append
  apply pair
  · fun_prop
  · apply list_flatMap
    · apply list_map <;> fun_prop
    · fun_prop
@[fun_prop] theorem mass_poly : Poly mass := by
  unfold mass
  apply comp rat_sum
  apply list_map
  · unfold rationalMarginal; fun_prop
  · fun_prop
@[fun_prop] theorem roots_poly : Poly roots := by
  unfold roots
  apply list_filter <;> fun_prop
@[fun_prop] theorem radius_poly : Poly radius := by
  exact comp (f:=fun x : Row × ℚ => x.1.foldl max x.2) (g:=fun x : Raw => (roots x,0))
    (of_program LPBinary.Program.maxFold) (pair roots_poly (const 0))

 theorem upper_list {n : ℕ} (d : Fin n → ℚ) : upper (List.ofFn d)=Taper.upper d := by
  simp only [upper,Taper.upper,List.map_ofFn,List.sum_ofFn,one_div,Function.comp_def]
 theorem mem_breaks {n : ℕ} (P : ℚ) (d : Fin n → ℚ) (q : ℚ) :
    q∈breaks (P,List.ofFn d) ↔ q∈Taper.breakpoints P d := by
  simp only [breaks,upper_list,List.mem_cons,List.mem_append,List.mem_map,List.mem_ofFn,
    Taper.breakpoints,mem_insert,mem_union,mem_image,mem_univ,true_and]
  aesop
 theorem aSum_list {n : ℕ} (P t : ℚ) (d : Fin n → ℚ) :
    aSum ((P,List.ofFn d),t)=Taper.A P d t := by
  simp only [aSum,List.map_ofFn,List.sum_ofFn,Taper.A,Function.comp_def]
 theorem bSum_list {n : ℕ} (P t : ℚ) (d : Fin n → ℚ) :
    bSum ((P,List.ofFn d),t)=Taper.B P d t := by
  simp only [bSum,List.map_ofFn,List.sum_ofFn,Taper.B,Function.comp_def]
 theorem mem_candidates {n : ℕ} (g P : ℚ) (d : Fin n → ℚ) (q : ℚ) :
    q∈candidateList ((g,P),List.ofFn d) ↔ q∈Taper.candidates g P d := by
  simp only [candidateList,List.mem_append,List.mem_flatMap,List.mem_map,mem_breaks,
    aSum_list,bSum_list,Taper.candidates,mem_union,mem_image,mem_product,Prod.exists]
  aesop
 theorem mass_list {n : ℕ} (g P r : ℚ) (d : Fin n → ℚ) :
    mass (((g,P),List.ofFn d),r)=rationalMass g P d r := by
  simp only [mass,List.map_ofFn,List.sum_ofFn,rationalMass,Function.comp_def]
 theorem mem_roots {n : ℕ} (g P : ℚ) (d : Fin n → ℚ) (q : ℚ) :
    q∈roots ((g,P),List.ofFn d) ↔ q∈rootCandidates g P d := by
  simp only [roots,List.mem_filter,mem_candidates,Bool.and_eq_true,decide_eq_true_eq,mass_list,
    rootCandidates,mem_filter]
 theorem radius_list {n : ℕ} (g P : ℚ) (d : Fin n → ℚ) :
    radius ((g,P),List.ofFn d)=inverseRadius g P d := by
  unfold inverseRadius
  split_ifs with h
  · apply LPBinary.foldl_max_eq
    · exact (mem_filter.mp (max'_mem (rootCandidates g P d) h)).2.1.le
    · exact (mem_roots _ _ _ _).mpr (max'_mem _ h)
    · intro q hq
      exact le_max' _ _ ((mem_roots _ _ _ _).mp hq)
  · have he : roots ((g,P),List.ofFn d)=[] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro q hq
      exact h ⟨q,(mem_roots _ _ _ _).mp hq⟩
    simp only [radius,he,List.foldl_nil]
end MetricKMedian.Taper.ListOperation
end

end OAI
