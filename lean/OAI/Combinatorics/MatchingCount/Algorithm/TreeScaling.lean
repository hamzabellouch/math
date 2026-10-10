import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeStateTable

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma height_div (a b : Fraction) : height (div (a,b))≤height a+height b+1 := by
  have hn:=normalize_size_num (a.1*b.2,a.2*b.1)
  have hd:=normalize_size_den (a.1*b.2,a.2*b.1)
  have hm:=nat_size_mul a.1 b.2
  have hm':=nat_size_mul a.2 b.1
  have ha:=le_max_left a.1.size a.2.size
  have ha':=le_max_right a.1.size a.2.size
  have hb:=le_max_left b.1.size b.2.size
  have hb':=le_max_right b.1.size b.2.size
  dsimp only at hn hd
  change (div (a,b)).1.size≤_ at hn
  change (div (a,b)).2.size≤_ at hd
  unfold height
  apply max_le <;> omega
lemma maximum_height (a b : Fraction) : height (maximum (a,b))≤ max (height a) (height b) := by
  rcases maximum_eq a b with h|h <;> rw [h]
  · exact le_max_left _ _
  · exact le_max_right _ _
lemma maximum_fold_height (xs : List Fraction) (z : Fraction) (B : ℕ)
    (hz : height z≤B) (hx : ∀ x∈xs,height x≤B) :
    height (xs.foldl (fun z x=>maximum (x,z)) z)≤B := by
  induction xs generalizing z with
  | nil=>exact hz
  | cons x xs ih=>
    apply ih _ ((maximum_height x z).trans (max_le (hx x (by simp)) hz))
    intro x hx'; exact hx x (by simp [hx'])
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.ExecutableScaling
open TreeTyped TreeFraction ExecutableBottleneck ExecutableLadder Polynomial

abbrev Vector := List (ℕ×Fraction)
abbrev State := Matrix×Vector

def ratio (x : (Matrix×ℕ)×(ℕ×Fraction)) : Fraction :=
  div (cell (x.1.1,(x.1.2,x.2.1)),x.2.2)
def ratioRealizer : Realizer ratio := composition (pair
  (composition (pair first.fst (pair first.snd second.fst)) cellRealizer)
  second.snd) divRealizer
lemma polynomial_ratio : PolynomialTime ratioRealizer := by
  unfold ratioRealizer
  apply polynomial_composition _ polynomial_div
  apply polynomial_pair _ (polynomial_snd polynomial_second)
  apply polynomial_composition _ polynomial_cell
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

def rowMax (x : State×ℕ) : Fraction :=
  ((x.1.2.filter (fun z=>decide (z.1≠x.2))).map (fun z=>ratio ((x.1.1,x.2),z))).foldl
    (fun a b=>maximum (b,a)) (0,1)
def rowMaxRealizer : Realizer rowMax := by
  let neq : Realizer (fun z : ℕ×(ℕ×Fraction)=>decide (z.2.1≠z.1)) :=
    (composition (composition (pair second.fst first) natEqual) boolNot).congr (by intro x; simp)
  let vs : Realizer (fun x : State×ℕ=>x.1.2.filter (fun z=>decide (z.1≠x.2))) :=
    composition (pair second first.snd) (filterWith neq)
  let vals : Realizer (fun x : State×ℕ=>(x.1.2.filter (fun z=>decide (z.1≠x.2))).map (fun z=>ratio ((x.1.1,x.2),z))) :=
    composition (pair (pair first.fst second) vs) (mapWith ratioRealizer)
  exact (composition (pair vals (constant (0,1))) (fold maximumRealizer)).congr (fun _=>rfl)
lemma polynomial_rowMax : PolynomialTime rowMaxRealizer := by
  unfold rowMaxRealizer
  dsimp only
  apply polynomial_congr
  have := polynomial_maximumFold
  have := polynomial_ratio
  have : PolynomialTime (composition (composition (pair (second (A:=ℕ) (B:=ℕ×Fraction)).fst first) natEqual) boolNot) := by
    dsimp only [Realizer.fst,Realizer.snd]
    tree_cost
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

def step (x : ℕ×State) : State :=
  (x.2.1,setState (x.2.2,(x.1,rowMax (x.2,x.1))))
def stepRealizer : Realizer step :=
  pair second.fst (composition (pair second.snd (pair first
    (composition (pair second first) rowMaxRealizer))) (setStateRealizer natEqual))
lemma polynomial_step : PolynomialTime stepRealizer := by
  unfold stepRealizer
  apply polynomial_pair (polynomial_fst polynomial_second)
  apply polynomial_composition _ (polynomial_setState (A:=Fraction) polynomial_natEqual)
  apply polynomial_pair (polynomial_snd polynomial_second)
  exact polynomial_pair polynomial_first (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_rowMax)

lemma cell_height (M : Matrix) (i j : ℕ) : height (cell (M,(i,j)))≤weight M+1 := by
  unfold cell
  dsimp only
  by_cases hi : i<M.length
  · rw [List.getD_eq_getElem _ _ hi]
    by_cases hj : j<M[i].length
    · rw [List.getD_eq_getElem _ _ hj]
      exact (height_le_weight _).trans ((weight_mem (List.getElem_mem hj)).trans
        ((weight_mem (List.getElem_mem hi)).trans (Nat.le_succ _)))
    · rw [List.getD_eq_default _ _ (by omega)]
      have : height one=1:=by norm_num [height,one,Nat.size]
      omega
  · rw [List.getD_eq_default M [] (by omega)]
    simp only [List.getD_nil]
    have : height one=1:=by norm_num [height,one,Nat.size]
    omega

lemma rowMax_height (M : Matrix) (v : Vector) (i H : ℕ) (hv : ∀ z∈v,height z.2≤H) :
    height (rowMax ((M,v),i))≤weight M+H+2 := by
  apply maximum_fold_height _ _ _ (by norm_num [height])
  intro x hx
  obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hx
  have hy:=List.mem_filter.mp hz
  have hh:=height_div (cell (M,(i,z.1))) z.2
  have hg:=cell_height M i z.1
  have hb:=hv z hy.1
  exact hh.trans (by omega)

lemma step_height (i : ℕ) (M : Matrix) (v : Vector) (H : ℕ)
    (hv : ∀ z∈v,height z.2≤H) :
    ∀ z∈(step (i,(M,v))).2,height z.2≤H+weight M+2 := by
  intro z hz
  obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hz
  dsimp only
  split_ifs
  · exact (rowMax_height M v i H hv).trans (by omega)
  · exact (hv a ha).trans (by omega)
lemma step_keys (i : ℕ) (s : State) : ((step (i,s)).2.map Prod.fst)=s.2.map Prod.fst := by
  simp [step,setState,List.map_map]
lemma vector_weight (v : Vector) (H : ℕ) (hv : ∀ z∈v,height z.2≤H) :
    weight v≤(weight (v.map Prod.fst)+1)*(8*H+5) := by
  induction v with
  | nil=>simp only [List.map_nil,weight_nil]; omega
  | cons z zs ih=>
    have hz:weight z.2≤8*H+3:=(weight_le_height z.2).trans (by have :=hv z (by simp);omega)
    have ht:=ih (fun a ha=>hv a (by simp [ha]))
    rw [List.map_cons,weight_cons,weight_cons,←Prod.eta z,weight_prod]
    nlinarith

lemma vector_keys_weight (v : Vector) : weight (v.map Prod.fst)≤weight v := by
  induction v with
  | nil=>rfl
  | cons a as ih=>
    rw [List.map_cons,weight_cons,weight_cons,←Prod.eta a,weight_prod]
    dsimp only
    omega
lemma fold_step_data (is : List ℕ) (M : Matrix) (v : Vector) (H : ℕ)
    (hv : ∀ z∈v,height z.2≤H) :
    (is.foldl (fun s i=>step (i,s)) (M,v)).1=M ∧
    (is.foldl (fun s i=>step (i,s)) (M,v)).2.map Prod.fst=v.map Prod.fst ∧
    ∀ z∈(is.foldl (fun s i=>step (i,s)) (M,v)).2,
      height z.2≤H+is.length*(weight M+2) := by
  induction is generalizing v H with
  | nil=>exact ⟨rfl,rfl,by simpa using hv⟩
  | cons i is ih=>
    have ht:=ih (step (i,(M,v))).2 (H+weight M+2) (step_height i M v H hv)
    refine ⟨ht.1,ht.2.1.trans (step_keys i (M,v)),?_⟩
    intro z hz
    have h:=ht.2.2 z hz
    simp only [List.length_cons]
    nlinarith
lemma polynomial_sweep : PolynomialTime (fold stepRealizer) := by
  apply polynomial_fold polynomial_step (1+X+(X+1)*(8*(X+X*(X+2))+5))
  intro is ⟨M,v⟩ pre post he
  let S:=weight (is,(M,v))
  have hM : weight M≤S := (weight_fst (M,v)).trans (weight_snd (is,(M,v)))
  have hv : weight v≤S := (weight_snd (M,v)).trans (weight_snd (is,(M,v)))
  have hk : weight (v.map Prod.fst)≤S := (vector_keys_weight v).trans hv
  have hp : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix he).trans (weight_fst (is,(M,v))))
  have ht:=fold_step_data pre M v S (fun z hz=>(height_le_weight z.2).trans ((weight_snd z).trans ((weight_mem hz).trans hv)))
  have hw:=vector_weight (pre.foldl (fun s i=>step (i,s)) (M,v)).2 (S+pre.length*(weight M+2)) ht.2.2
  rw [ht.2.1] at hw
  rw [←Prod.eta (pre.foldl (fun s i=>step (i,s)) (M,v)),weight_prod,ht.1]
  simp only [eval_add,eval_mul,eval_X,eval_one,eval_ofNat]
  change _≤1+S+(S+1)*(8*(S+S*(S+2))+5)
  have hi : S+pre.length*(weight M+2)≤S+S*(S+2) := Nat.add_le_add_left (Nat.mul_le_mul hp (by omega)) S
  exact Nat.add_le_add (by omega) (hw.trans (Nat.mul_le_mul (by omega) (by omega)))

def initial (M : Matrix) : State := (M,(List.range M.length).map fun i=>(i,(2,1)))
def initialRealizer : Realizer initial :=
  pair identity (composition (composition listLength range) (map (pair identity (constant (2,1)))))
lemma polynomial_initial : PolynomialTime initialRealizer := by
  unfold initialRealizer
  apply polynomial_pair polynomial_identity
  apply polynomial_composition
  · exact polynomial_boundedRange polynomial_listLength X (fun a=>by simpa using list_length_le_weight a)
  · tree_cost

def scale (M : Matrix) : Vector :=
  ((List.range M.length).foldl (fun s i=>step (i,s)) (initial M)).2
def scaleRealizer : Realizer scale :=
  composition (composition (pair (composition listLength range) initialRealizer) (fold stepRealizer)) second
lemma polynomial_scale : PolynomialTime scaleRealizer := by
  unfold scaleRealizer
  apply polynomial_composition _ polynomial_second
  apply polynomial_composition _ polynomial_sweep
  apply polynomial_pair _ polynomial_initial
  exact polynomial_boundedRange polynomial_listLength X (fun a=>by simpa using list_length_le_weight a)
end MatchingFPRAS.ExecutableScaling

end OAI
