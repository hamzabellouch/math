import OAI.Computability.RandomMean.ControlCorrectness

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp

namespace Word
end Word
namespace Array
end Array
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace Array
end Array
namespace RawBudget
end RawBudget
namespace RawBox
end RawBox
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace RawBasic
 theorem fold_digits {g : Arena} {b : RawBox.Data} {E M : ℕ} (hg : ArenaBounded g E)
    (ha : Array.Bounded b.2.1 M) (hb : Array.Bounded b.2.2 M) (xs : List W) (cs : Count)
    (hx : Array.Bounded xs M) : Array.Bounded (Fold.fold advance.eval ((g,b),xs) cs).2 (M+cs.length*(E+1)) := by
  induction cs generalizing M xs with
  | nil => simpa only [Fold.fold,List.foldl_nil,List.length_nil,Nat.zero_mul,Nat.add_zero] using hx
  | cons u cs ih =>
    have hn : Array.Bounded (next ((g,b),xs)) (M+(E+1)) :=
      clip_bound (ha.mono (by omega)) (hb.mono (by omega)) (by change Array.Bounded (graph (xs,g)) (M+(E+1)); simpa only [Nat.add_assoc] using graph_bound hx hg)
    have h := ih (ha.mono (by omega : M≤M+(E+1))) (hb.mono (by omega : M≤M+(E+1))) (next ((g,b),xs)) hn
    change Array.Bounded (Fold.fold advance.eval ((g,b),next ((g,b),xs)) cs).2 _
    convert h using 1 ; simp only [List.length_cons,Nat.add_mul,Nat.one_mul] ; omega
 theorem solve_small {g : Arena} {b : RawBox.Data} {n E M : ℕ} (hg : ArenaBounded g E)
    (hb : RawBox.Small n M b) (cs : Count) : Array.Small n (M+cs.length*(E+1)) (solve ((g,b),cs)) := by
  refine ⟨?_,fold_digits hg hb.lower.digits hb.upper.digits b.2.1 cs hb.lower.digits⟩
  change (Fold.fold advance.eval ((g,b),b.2.1) cs).2.length≤n
  rw [(fold_layout (g,b) b.2.1 cs).2]
  split <;> first | exact hb.lower.length | exact hb.upper.length
end RawBasic
namespace Array
 theorem Small.foldMin {n M : ℕ} {xs : List W} {xss : List (List W)} (hx : Small n M xs) (hs : ∀ ys∈xss, Small n M ys) :
    Small n M (foldMin (xs,xss)) :=
  ⟨(fold_select_bound Word.min EdgeScan.low_mem hx.digits (fun ys hy => (hs ys hy).digits)).2.le.trans hx.length,
    (fold_select_bound Word.min EdgeScan.low_mem hx.digits (fun ys hy => (hs ys hy).digits)).1⟩
 theorem Small.foldMax {n M : ℕ} {xs : List W} {xss : List (List W)} (hx : Small n M xs) (hs : ∀ ys∈xss, Small n M ys) :
    Small n M (foldMax (xs,xss)) :=
  ⟨(fold_select_bound Word.max EdgeScan.high_mem hx.digits (fun ys hy => (hs ys hy).digits)).2.le.trans hx.length,
    (fold_select_bound Word.max EdgeScan.high_mem hx.digits (fun ys hy => (hs ys hy).digits)).1⟩
end Array
namespace RawBox
 theorem Small.smallVector {n M : ℕ} {b : Data} (hb : Small n M b) {p : RawBudget.Data} (hp : RawBudget.Small n M p) :
    Array.Small n M (smallVector (p,b)) := by
  apply Array.choose_small hb.upper hb.lower
  change (Zip.zip _ _ _ _).length≤n
  rw [Array.zip_length]
  change (p.2.2.2.map _).length≤n
  simpa only [List.length_map] using hp.beta.length
end RawBox
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace Array
 theorem Bounded.nth {M : ℕ} {xs : List W} (h : Bounded xs M) (i : ℕ) : (xs.getD i zero).digits.length≤M := by
  induction xs generalizing i with
  | nil => exact Nat.zero_le _
  | cons x xs ih => cases i with
    | zero => exact h x (by simp)
    | succ i => exact ih (fun y hy => h y (by simp [hy])) i
end Array
namespace RawMedian
 theorem scalar_bound {M : ℕ} {xs : List W} (h : Array.Bounded xs M) : (scalar xs).digits.length≤M := by
  apply Array.Bounded.headD
  intro w hw
  exact h w ((Sort.sort_perm xs).mem_iff.mp (List.mem_of_mem_drop hw))
 theorem column_bound {M : ℕ} {xs : List (List W)} (h : ∀ ys∈xs, Array.Bounded ys M) (c : Count) :
    (column (xs,c)).digits.length≤M := by
  apply scalar_bound
  intro w hw
  obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hw
  change (Code.nth Array.zero (ys,c)).digits.length≤M
  rw [Code.nth_eval]
  exact (h ys hy).nth _
 theorem coordinates_small {M n : ℕ} {xs : List (List W)} (h : ∀ ys∈xs, Array.Bounded ys M) (c : Count) (hc : c.length≤n) :
    Array.Small n M (coordinates (c,xs)) := by
  refine ⟨?_,?_⟩
  · change ((Counter.enum c).map _).length≤n
    rw [List.length_map,Counter.enum_eq,List.length_map,List.length_range]
    exact hc
  · intro w hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    exact column_bound h i
 theorem boxed_small {n M : ℕ} {b : RawBox.Data} (hb : RawBox.Small n M b) {xs : List (List W)} (h : ∀ ys∈xs, Array.Small n M ys) :
    Array.Small n M (boxed (b,xs)) := by
  simp only [boxed,branch_eval,comp_eval,pair_eval,fst_eval,snd_eval,empty_eval]
  split
  · exact hb.lower
  · apply coordinates_small (fun ys hy => (h ys hy).digits)
    change (b.2.1.map (fun _ => ())).length≤n
    simpa only [List.length_map] using hb.lower.length
end RawMedian
namespace RawOrientation
 def Small (n : ℕ) (o : Data) : Prop := ∀ hs∈o.2, hs.length≤n
 theorem positives_length (b : RawBox.Data) (s : W) (xs : List W) : (positives (b,s,xs)).length=xs.length := by
  change ((_ : List W).map _).length=xs.length
  rw [List.length_map]
  change ((_ : List W).map _).length=xs.length
  rw [List.length_map]
  exact Array.zip_length _ _ _ _
 theorem negatives_length (b : RawBox.Data) (s : W) (xs : List W) : (negatives (b,s,xs)).length=xs.length := by
  change ((_ : List W).map _).length=xs.length
  rw [List.length_map]
  change ((_ : List W).map _).length=xs.length
  rw [List.length_map]
  exact Array.zip_length _ _ _ _
 theorem trueComplement_small {n : ℕ} {bs : List Bool} (h : bs.length≤n) : Small n (trueComplement bs) := by
  intro cs hc
  change cs∈[bs.map Bool.not] at hc
  rcases List.mem_singleton.mp hc with rfl
  simpa only [List.length_map] using h
 theorem falseComplement_small {n : ℕ} {bs : List Bool} (h : bs.length≤n) : Small n (falseComplement bs) := by
  intro cs hc
  change cs∈[bs.map Bool.not] at hc
  rcases List.mem_singleton.mp hc with rfl
  simpa only [List.length_map] using h
 theorem base_small {n M : ℕ} (p : RawBudget.Data) (b : RawBox.Data) {xs : List W} (h : Array.Small n M xs) : Small n (base (p,b,xs)) := by
  have hl : (baseMask (b,xs)).length≤n := by
    change ((_ : List W).map _).length≤n
    rw [List.length_map]
    change ((_ : List W).map _).length≤n
    rw [List.length_map]
    change (Array.sub (xs,b.2.1)).length≤n
    exact (Array.zip_length _ _ _ _).le.trans h.length
  change Small n (if RawBudget.measureLarge (p,baseMask (b,xs)) then _ else _)
  split
  · exact trueComplement_small hl
  · intro cs hc
    change cs∈[baseMask (b,xs)] at hc
    rcases List.mem_singleton.mp hc with rfl
    exact hl
 theorem extend_small {n : ℕ} {o : Data} (ho : Small n o) {hs ns : List Bool} (hh : hs.length≤n) (hn : ns.length≤n) :
    Small n (extend (o,hs,ns)) := by
  intro cs hc
  change cs∈Code.append (o.2,[hs,ns]) at hc
  rw [Code.append_eval] at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact ho cs hc
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl <;> assumption
 theorem combine_small {n : ℕ} {os : List Data} (h : ∀ o∈os, Small n o) : Small n (combine os) := by
  intro cs hc
  change cs∈Code.flatten (os.map Prod.snd) at hc
  rw [Code.flatten_eval] at hc
  obtain ⟨ss,hs,hcs⟩ := List.mem_flatten.mp hc
  obtain ⟨o,ho,rfl⟩ := List.mem_map.mp hs
  exact h o ho cs hcs
end RawOrientation
end MeanPayoff.TreeDevice.Certified

end

end OAI
