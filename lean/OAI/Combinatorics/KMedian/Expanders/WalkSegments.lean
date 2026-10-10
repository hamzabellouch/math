import Mathlib
import OAI.Combinatorics.KMedian.Expanders.PortWalk

namespace OAI

section Inline_PCPWalkSegments

namespace MetricKMedian.PCP.PortGraph
open Finset
open scoped BigOperators

variable {V D : Type} {G : PortGraph V D}
namespace Walk
variable {n m : ℕ}

def segment (p : G.Walk n) (a l : ℕ) (h : a+l ≤ n) : G.Walk l where
  vertex i := p.vertex ⟨a+i.val, by omega⟩
  port i := p.port ⟨a+i.val, by omega⟩
  chain i := p.chain ⟨a+i.val, by omega⟩

@[simp] theorem segment_vertex (p : G.Walk n) (a l : ℕ) (h : a+l ≤ n) (i : Fin (l+1)) :
    (p.segment a l h).vertex i = p.vertex ⟨a+i.val, by omega⟩ := rfl
@[simp] theorem segment_port (p : G.Walk n) (a l : ℕ) (h : a+l ≤ n) (i : Fin l) :
    (p.segment a l h).port i = p.port ⟨a+i.val, by omega⟩ := rfl

def catVertex (p : G.Walk n) (q : G.Walk m) (i : Fin (n+m+1)) : V :=
  if h : i.val ≤ n then p.vertex ⟨i.val,by omega⟩
  else q.vertex ⟨i.val-n,by omega⟩
def catPort (p : G.Walk n) (q : G.Walk m) (i : Fin (n+m)) : D :=
  if h : i.val < n then p.port ⟨i.val,h⟩
  else q.port ⟨i.val-n,by omega⟩

def concat (p : G.Walk n) (q : G.Walk m) (h : p.vertex (Fin.last n) = q.vertex 0) : G.Walk (n+m) where
  vertex := catVertex p q
  port := catPort p q
  chain i := by
    by_cases hi : i.val < n
    · dsimp only [catVertex,catPort,Fin.val_castSucc,Fin.val_succ]
      simp only [dite_eq_left hi, dite_eq_left (by omega : i.val ≤ n), dite_eq_left (by omega : i.val+1 ≤ n)]
      exact p.chain ⟨i.val,hi⟩
    · by_cases he : i.val = n
      · dsimp only [catVertex,catPort,Fin.val_castSucc,Fin.val_succ]
        simp only [dite_eq_right hi, dite_eq_left (by omega : i.val ≤ n), dite_eq_right (by omega : ¬ i.val+1 ≤ n)]
        have hn : 0 < m := by omega
        have hl : p.vertex ⟨i.val,by omega⟩ = q.vertex 0 := by
          convert h using 1; congr 1; exact Fin.ext he
        rw [hl]
        convert q.chain ⟨0,hn⟩ using 1 <;> congr 2 <;> first | exact Fin.ext (by dsimp; omega) | (dsimp; omega)
      · dsimp only [catVertex,catPort,Fin.val_castSucc,Fin.val_succ]
        simp only [dite_eq_right hi, dite_eq_right (by omega : ¬ i.val ≤ n), dite_eq_right (by omega : ¬ i.val+1 ≤ n)]
        convert q.chain ⟨i.val-n,by omega⟩ using 1 <;> congr 1
        apply Fin.ext
        simp
        omega

@[simp] theorem concat_start (p : G.Walk n) (q : G.Walk m) (h) :
    (p.concat q h).vertex 0 = p.vertex 0 := by simp [concat,catVertex]

@[simp] theorem concat_end (p : G.Walk n) (q : G.Walk m) (h) :
    (p.concat q h).vertex (Fin.last (n+m)) = q.vertex (Fin.last m) := by
  by_cases hm : m=0
  · subst m
    simpa [concat,catVertex,Fin.last] using h
  · simp [concat,catVertex,Fin.last,show ¬ n+m ≤ n by omega]

@[simp] theorem segment_concat_left (p : G.Walk n) (q : G.Walk m) (h) :
    (p.concat q h).segment 0 n (by omega) = p := by
  apply Walk.ext
  · funext i
    simp [segment,concat,catVertex,show i.val ≤ n by omega]
  · funext i
    simp [segment,concat,catPort]

@[simp] theorem segment_concat_right (p : G.Walk n) (q : G.Walk m) (h) :
    (p.concat q h).segment n m (by omega) = q := by
  apply Walk.ext
  · funext i
    by_cases hi : i.val=0
    · have hei : i=0 := Fin.ext hi
      subst i
      simpa [segment,concat,catVertex,Fin.last] using h
    · dsimp only [segment,concat,catVertex]
      rw [dite_eq_right (by omega : ¬ n+i.val ≤ n)]
      congr 1
      exact Fin.ext (by simp)
  · funext i
    simp [segment,concat,catPort]

theorem concat_segments (p : G.Walk (n+m)) :
    (p.segment 0 n (by omega)).concat (p.segment n m (by omega)) (by simp [segment]) = p := by
  apply Walk.ext
  · funext i
    dsimp [concat,catVertex,segment]
    split_ifs with hi
    · congr 1; apply Fin.ext; simp
    · congr 1; apply Fin.ext; simp; omega
  · funext i
    dsimp [concat,catPort,segment]
    split_ifs with hi
    · congr 1; apply Fin.ext; simp
    · congr 1; apply Fin.ext; simp; omega

def splitEquiv (n m : ℕ) : G.Walk (n+m) ≃ G.Walk n × (Fin m → D) where
  toFun p := (p.segment 0 n (by omega), (p.segment n m (by omega)).port)
  invFun z := z.1.concat (ofWord (z.1.vertex (Fin.last n)) z.2) (by simp [ofWord])
  left_inv p := by
    have hq : ofWord ((p.segment 0 n (by omega)).vertex (Fin.last n))
        (p.segment n m (by omega)).port = p.segment n m (by omega) := by
      apply Walk.ext
      · have hb : (p.segment 0 n (by omega)).vertex (Fin.last n) =
            (p.segment n m (by omega)).vertex 0 := by simp [segment]
        change G.trace m ((p.segment 0 n (by omega)).vertex (Fin.last n)) _ = _
        rw [hb]
        exact (vertex_eq_trace (p.segment n m (by omega))).symm
      · rfl
    simp only [hq,concat_segments]
  right_inv z := by simp [ofWord]

end Walk
end MetricKMedian.PCP.PortGraph

end Inline_PCPWalkSegments

end OAI
