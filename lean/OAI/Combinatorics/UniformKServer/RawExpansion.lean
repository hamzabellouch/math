import Mathlib
import OAI.Combinatorics.UniformKServer.RawTyped
import OAI.Combinatorics.UniformKServer.PathExpansion

namespace OAI

                                   
section

namespace UniformKServer.RawExpansion
open RawArithmetic RawWords RawTable RawPath RawTyped
abbrev State (n k : ℕ) := List (Fin n) × Configuration n k

def kernel {n k : ℕ} (T : List ℕ) (s : State n k) (r : Fin n) (j : Fin k) :=
  entry T (requests s.1) (config s.2) r.val j.val

def next {n k : ℕ} (s : State n k) (r : Fin n) (j : Fin k) : State n k :=
  (s.1++[r],serve s.2 r j)

def charge {n k : ℕ} (d : RationalMetric n) (s : State n k) (r : Fin n) (j : Fin k) : ℝ :=
  d.distance (s.2 j) r

theorem weight_eq {n k : ℕ} (T : List ℕ) (p : List (Fin n)) (c : Configuration n k) (h : History n k) :
    RawPath.weight T (requests p) (config c) (events h)=
      PathExpansion.weight (kernel T) next (p,c) h := by
  induction h generalizing p c with
  | nil=>rfl
  | cons rj h ih=>
    obtain ⟨r,j⟩:=rj
    simp only [events,List.map_cons,RawPath.weight,PathExpansion.weight,kernel,next,config_set]
    rw [←ih]
    simp [requests,events]

theorem movement_eq {n k : ℕ} (d : RationalMetric n) (draw : List Q)
    (hd : ∀x y : Fin n,value (dist n draw x.val y.val)=d.distance x y)
    (c : Configuration n k) (h : History n k) :
    (RawPath.movement n draw (config c) (events h):ℝ)=costAlong d c h := by
  induction h generalizing c with
  | nil=>simp [RawPath.movement,events,costAlong]
  | cons rj h ih=>
    obtain ⟨r,j⟩:=rj
    change ((value (dist n draw ((config c).getD j.val 0) r.val)+
      RawPath.movement n draw ((config c).set j.val r.val) (events h):ℚ):ℝ)=_
    push_cast
    rw [config_get,config_set,hd,ih]
    rfl

theorem path_movement_eq {n k : ℕ} (d : RationalMetric n) (p : List (Fin n))
    (c : Configuration n k) (h : History n k) :
    PathExpansion.movement next (charge d) (p,c) h=costAlong d c h := by
  induction h generalizing p c with
  | nil=>rfl
  | cons rj h ih=>
    obtain ⟨r,j⟩:=rj
    simp only [PathExpansion.movement,next,charge,costAlong,ih]

theorem range_eq_ofFn (k : ℕ) : List.range k=List.ofFn (fun j : Fin k=>j.val) := by
  apply List.ext_getElem <;> simp

theorem histories_eq {n : ℕ} (k : ℕ) (w : List (Fin n)) :
    ((words k w.length).map fun g=>history (requests w) g)=
      (PathExpansion.traces k w).map events := by
  induction w with
  | nil=>simp [words,PathExpansion.traces,requests,history,events]
  | cons r w ih=>
    simp only [List.length_cons,words,requests,List.map_cons,PathExpansion.traces,
      List.map_flatMap,List.map_map,Function.comp_def,history_cons,List.map_flatten,List.map_ofFn]
    rw [range_eq_ofFn]
    rw [List.flatMap_def]
    simp only [List.map_ofFn]
    congr 1
    apply congrArg List.ofFn
    funext j
    have he:=congrArg (List.map ((r.val,j.val)::·)) ih
    simpa only [List.map_map,Function.comp_def,events,List.map_cons,requests] using he

theorem total_eq {n k : ℕ} (d : RationalMetric n) (draw : List Q)
    (hd : ∀x y : Fin n,value (dist n draw x.val y.val)=d.distance x y)
    (T : List ℕ) (p : List (Fin n)) (c : Configuration n k) (w : List (Fin n)) :
    (value (total n k draw T (requests p) (config c) (requests w)):ℝ)=
      ((PathExpansion.traces k w).map fun h=>
        (PathExpansion.weight (kernel T) next (p,c) h:ℝ)*
          PathExpansion.movement next (charge d) (p,c) h).sum := by
  rw [total_value]
  have he:=congrArg (List.map (fun h=>(RawPath.weight T (requests p) (config c) h:ℚ)*
    RawPath.movement n draw (config c) h)) (histories_eq k w)
  simp only [List.map_map,Function.comp_def] at he
  have hl : (requests w).length=w.length := by simp [requests]
  rw [hl,he]
  have hsum (xs : List ℚ) : (xs.sum:ℝ)=(xs.map fun q : ℚ =>(q:ℝ)).sum :=
    map_list_sum (Rat.castHom ℝ) xs
  rw [hsum]
  congr 1
  simp only [List.map_map,Function.comp_def,Rat.cast_mul,Rat.cast_natCast,
    weight_eq,movement_eq d draw hd,←path_movement_eq d p c]

theorem expected_eq {n k b : ℕ} (d : RationalMetric n) (draw : List Q)
    (hd : ∀x y : Fin n,value (dist n draw x.val y.val)=d.distance x y)
    (T : List ℕ) (hN : ∀s r,∑j,kernel (n:=n) (k:=k) T s r j=2^b)
    (p : List (Fin n)) (c : Configuration n k) (w : List (Fin n)) :
    (value (expected n k b draw T (requests p) (config c) (requests w)):ℝ)=
      BitSampling.rowCost (b:=b) (kernel T) next (charge d) (p,c) w := by
  rw [expected_value]
  push_cast
  rw [total_eq d draw hd,PathExpansion.sum_weight_cost _ hN]
  simp only [requests,List.length_map,pow_mul]
  have hb : ((2:ℝ)^b)^w.length≠0 := by positivity
  exact mul_div_cancel_left₀ _ hb

end UniformKServer.RawExpansion

end



end OAI
