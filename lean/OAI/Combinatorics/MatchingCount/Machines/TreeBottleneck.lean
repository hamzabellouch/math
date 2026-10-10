import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.TreeChoiceCosts

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

def maximum (x : Fraction×Fraction) : Fraction := if less x then x.2 else x.1
def minimum (x : Fraction×Fraction) : Fraction := if less x then x.1 else x.2
def maximumRealizer : Realizer maximum := (choose lessRealizer second first).congr (fun _=>rfl)
def minimumRealizer : Realizer minimum := (choose lessRealizer first second).congr (fun _=>rfl)
lemma polynomial_maximum : PolynomialTime maximumRealizer := by
  exact polynomial_congr _ (polynomial_choose polynomial_less polynomial_second polynomial_first)
lemma polynomial_minimum : PolynomialTime minimumRealizer := by
  exact polynomial_congr _ (polynomial_choose polynomial_less polynomial_first polynomial_second)
lemma maximum_eq (x y : Fraction) : maximum (x,y)=x ∨ maximum (x,y)=y := by
  unfold maximum; split_ifs <;> simp
lemma minimum_eq (x y : Fraction) : minimum (x,y)=x ∨ minimum (x,y)=y := by
  unfold minimum; split_ifs <;> simp
lemma maximum_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    maximum (repr x,repr y)=repr (max x y) := by
  unfold maximum
  rw [less_val _ _ x.pos y.pos,val_repr hx,val_repr hy]
  simp only [decide_eq_true_eq]
  split_ifs with h
  · rw [max_eq_right (le_of_lt h)]
  · rw [max_eq_left (le_of_not_gt h)]
lemma minimum_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    minimum (repr x,repr y)=repr (min x y) := by
  unfold minimum
  rw [less_val _ _ x.pos y.pos,val_repr hx,val_repr hy]
  simp only [decide_eq_true_eq]
  split_ifs with h
  · rw [min_eq_left (le_of_lt h)]
  · rw [min_eq_right (le_of_not_gt h)]
lemma maximum_weight (x y : Fraction) : weight (maximum (x,y))≤ max (weight x) (weight y) := by
  rcases maximum_eq x y with h|h <;> rw [h]
  · exact le_max_left _ _
  · exact le_max_right _ _
lemma minimum_weight (x y : Fraction) : weight (minimum (x,y))≤ max (weight x) (weight y) := by
  rcases minimum_eq x y with h|h <;> rw [h]
  · exact le_max_left _ _
  · exact le_max_right _ _
lemma maximum_fold_weight (xs : List Fraction) (z : Fraction) (B : ℕ)
    (hz : weight z≤B) (hx : ∀ x∈xs,weight x≤B) :
    weight (xs.foldl (fun z x=>maximum (x,z)) z)≤B := by
  induction xs generalizing z with
  | nil => exact hz
  | cons x xs ih =>
    apply ih _ ((maximum_weight x z).trans (max_le (hx x (by simp)) hz))
    intro x hx'; exact hx x (by simp [hx'])
lemma polynomial_maximumFold : PolynomialTime (fold maximumRealizer) := by
  apply polynomial_fold polynomial_maximum Polynomial.X
  intro xs z pre post he
  simp only [Polynomial.eval_X]
  apply maximum_fold_weight pre z _ (weight_snd (xs,z))
  intro x hx
  exact (weight_mem hx).trans ((weight_prefix he).trans (weight_fst (xs,z)))
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.ExecutableBottleneck
open TreeTyped TreeFraction Polynomial

abbrev Matrix := List (List Fraction)
def one : Fraction := (1,1)
def cell (x : Matrix×(ℕ×ℕ)) : Fraction := (x.1.getD x.2.1 []).getD x.2.2 one
def cellRealizer : Realizer cell := composition
  (pair (composition (pair first second.fst) (getDFast [])) second.snd) (getDFast one)
lemma polynomial_cell : PolynomialTime cellRealizer := by
  unfold cellRealizer
  have h₁:=polynomial_getDFast ([] : List Fraction)
  have h₂:=polynomial_getDFast one
  exact polynomial_composition (polynomial_pair (polynomial_composition
    (polynomial_pair polynomial_first (polynomial_fst polynomial_second)) h₁)
      (polynomial_snd polynomial_second)) h₂

def square {A B : Type} (n : ℕ) (a : A) (f : A×(ℕ×ℕ)→B) : List (List B) :=
  (List.range n).map fun i=>(List.range n).map fun j=>f (a,(i,j))
def squareRealizer {A B : Type} [Codec A] [Codec B] {n : A→ℕ} {f : A×(ℕ×ℕ)→B}
    (N : Realizer n) (F : Realizer f) : Realizer (fun a=>square (n a) a f) := by
  let rs:=composition N range
  let e:=composition (pair first.fst (pair first.snd second)) F
  let row:=composition (pair identity (composition first rs)) (mapWith e)
  exact composition (pair identity rs) (mapWith row)
lemma polynomial_square {A B : Type} [Codec A] [Codec B] {n : A→ℕ} {f : A×(ℕ×ℕ)→B}
    {N : Realizer n} {F : Realizer f} (hN : PolynomialTime N) (hF : PolynomialTime F)
    (p : Polynomial ℕ) (hn : ∀ a,n a≤p.eval (weight a)) : PolynomialTime (squareRealizer N F) := by
  have hR:=polynomial_boundedRange hN p hn
  unfold squareRealizer
  dsimp only
  exact polynomial_composition (polynomial_pair polynomial_identity hR)
    (polynomial_mapWith (polynomial_composition
      (polynomial_pair polynomial_identity (polynomial_composition polynomial_first hR))
      (polynomial_mapWith (polynomial_composition
        (polynomial_pair (polynomial_fst polynomial_first)
          (polynomial_pair (polynomial_snd polynomial_first) polynomial_second)) hF))))

lemma cell_weight {M : Matrix} {B : ℕ} (h₁ : weight one≤B)
    (hM : ∀ r∈M,∀ x∈r,weight x≤B) (i j : ℕ) : weight (cell (M,(i,j)))≤B := by
  unfold cell
  dsimp only
  by_cases hi : i<M.length
  · rw [List.getD_eq_getElem _ _ hi]
    by_cases hj : j<(M[i]).length
    · rw [List.getD_eq_getElem _ _ hj]
      exact hM _ (List.getElem_mem hi) _ (List.getElem_mem hj)
    · rw [List.getD_eq_default _ _ (by omega)]; exact h₁
  · rw [List.getD_eq_default M [] (by omega)]
    simpa using h₁

def via (x : (Matrix×(ℕ×ℕ))×ℕ) : Fraction :=
  minimum (cell (x.1.1,(x.1.2.1,x.2)),cell (x.1.1,(x.2,x.1.2.2)))
def viaRealizer : Realizer via := composition (pair
  (composition (pair first.fst (pair first.snd.fst second)) cellRealizer)
  (composition (pair first.fst (pair second first.snd.snd)) cellRealizer)) minimumRealizer
lemma polynomial_via : PolynomialTime viaRealizer := by
  unfold viaRealizer
  apply polynomial_composition _ TreeFraction.polynomial_minimum
  apply polynomial_pair
  · apply polynomial_composition _ polynomial_cell
    exact polynomial_pair (polynomial_fst polynomial_first)
      (polynomial_pair (polynomial_fst (polynomial_snd polynomial_first)) polynomial_second)
  · apply polynomial_composition _ polynomial_cell
    exact polynomial_pair (polynomial_fst polynomial_first)
      (polynomial_pair polynomial_second (polynomial_snd (polynomial_snd polynomial_first)))

def entry (x : Matrix×(ℕ×ℕ)) : Fraction :=
  if x.2.1=x.2.2 then one else
    ((List.range x.1.length).map fun c=>via (x,c)).foldl (fun z v=>maximum (v,z)) (cell x)
def entryRealizer : Realizer entry := by
  let vals:=composition (pair identity (composition (composition first listLength) range)) (mapWith viaRealizer)
  exact (choose (composition second natEqual) (constant one)
    (composition (pair vals cellRealizer) (fold maximumRealizer))).congr (by
      intro x; simp only [entry,Function.comp_apply,decide_eq_true_eq,id_eq])
lemma polynomial_entry : PolynomialTime entryRealizer := by
  have hR : PolynomialTime (composition (composition (first (A:=Matrix) (B:=ℕ×ℕ)) listLength) range) := by
    apply polynomial_boundedRange (by tree_poly) X
    intro x; simpa using (list_length_le_weight x.1).trans (weight_fst x)
  unfold entryRealizer
  dsimp only
  apply polynomial_congr
  apply polynomial_choose (polynomial_composition polynomial_second polynomial_natEqual) (polynomial_constant one)
  apply polynomial_composition _ polynomial_maximumFold
  apply polynomial_pair _ polynomial_cell
  exact polynomial_composition (polynomial_pair polynomial_identity hR) (polynomial_mapWith polynomial_via)

def advance (M : Matrix) : Matrix := square M.length M entry
def advanceRealizer : Realizer advance := squareRealizer listLength entryRealizer
lemma polynomial_advance : PolynomialTime advanceRealizer := by
  exact polynomial_square polynomial_listLength polynomial_entry X (fun a=>by simpa using list_length_le_weight a)
lemma advance_length (M : Matrix) : (advance M).length=M.length := by
  simp [advance,square]
lemma entry_weight {M : Matrix} {B : ℕ} (h₁ : weight one≤B)
    (hM : ∀ r∈M,∀ x∈r,weight x≤B) (i j : ℕ) : weight (entry (M,(i,j)))≤B := by
  unfold entry
  dsimp only
  split_ifs
  · exact h₁
  · apply maximum_fold_weight _ _ _ (cell_weight h₁ hM i j)
    intro x hx
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hx
    exact (minimum_weight _ _).trans (max_le (cell_weight h₁ hM i c) (cell_weight h₁ hM c j))
lemma advance_entries {M : Matrix} {B : ℕ} (h₁ : weight one≤B)
    (hM : ∀ r∈M,∀ x∈r,weight x≤B) : ∀ r∈advance M,∀ x∈r,weight x≤B := by
  intro r hr x hx
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hr
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hx
  exact entry_weight h₁ hM i j
lemma advance_weight {M : Matrix} {B : ℕ} (h₁ : weight one≤B)
    (hM : ∀ r∈M,∀ x∈r,weight x≤B) : weight (advance M)≤1+M.length*(2+M.length*(B+1)) := by
  unfold advance square
  have h:=weight_map_bound (as:=List.range M.length)
    (N:=1+M.length*(B+1)) (f:=fun i=>(List.range M.length).map fun j=>entry (M,(i,j))) (by
      intro i _
      simpa [List.length_range,Nat.add_comm] using weight_map_bound (as:=List.range M.length)
        (f:=fun j=>entry (M,(i,j))) (fun j _=>entry_weight h₁ hM i j))
  simp only [List.length_range] at h
  exact h.trans_eq (by ring)

def seedEntry (x : Matrix×(ℕ×ℕ)) : Fraction := if x.2.1=x.2.2 then one
  else maximum (one,cell (x.1,(min x.2.1 x.2.2,max x.2.1 x.2.2)))
def seedEntryRealizer : Realizer seedEntry := by
  let inds : Realizer (fun x : Matrix×(ℕ×ℕ)=>if x.2.1<x.2.2 then x.2 else (x.2.2,x.2.1)) := (choose (composition second TreeTyped.less) second (pair second.snd second.fst)).congr (by intro x; simp only [Function.comp_apply,decide_eq_true_eq])
  exact (choose (composition second natEqual) (constant one)
    (composition (pair (constant one) (composition (pair first inds) cellRealizer)) maximumRealizer)).congr (by
      intro x
      simp only [seedEntry,Function.comp_apply,decide_eq_true_eq]
      split_ifs with h h'
      · rfl
      · rw [min_eq_left (le_of_lt h'),max_eq_right (le_of_lt h')]
      · rw [min_eq_right (le_of_not_gt h'),max_eq_left (le_of_not_gt h')])
lemma polynomial_seedEntry : PolynomialTime seedEntryRealizer := by
  unfold seedEntryRealizer
  dsimp only
  apply polynomial_congr
  apply polynomial_choose (polynomial_composition polynomial_second polynomial_natEqual)
    (polynomial_constant one)
  apply polynomial_composition _ TreeFraction.polynomial_maximum
  apply polynomial_pair (polynomial_constant one)
  apply polynomial_composition _ polynomial_cell
  apply polynomial_pair polynomial_first
  apply polynomial_congr
  exact polynomial_choose (polynomial_composition polynomial_second TreeTyped.polynomial_less)
    polynomial_second (polynomial_pair (polynomial_snd polynomial_second)
      (polynomial_fst polynomial_second))

def seed (M : Matrix) : Matrix := square M.length M seedEntry
def seedRealizer : Realizer seed := squareRealizer listLength seedEntryRealizer
lemma polynomial_seed : PolynomialTime seedRealizer :=
  polynomial_square polynomial_listLength polynomial_seedEntry X (fun a=>by simpa using list_length_le_weight a)

def close (M : Matrix) : Matrix := M.foldl (fun z _=>advance z) (seed M)
def closeRealizer : Realizer close := composition (pair identity seedRealizer)
  (fold (composition second advanceRealizer))
lemma fold_advance_invariant (ls : List (List Fraction)) (M : Matrix) (B : ℕ)
    (h₁ : weight one≤B) (hM : ∀ r∈M,∀ x∈r,weight x≤B) :
    let R:=ls.foldl (fun z _=>advance z) M
    R.length=M.length ∧ (∀ r∈R,∀ x∈r,weight x≤B) ∧
      weight R≤weight M+1+M.length*(2+M.length*(B+1)) := by
  have hInv : ∀ (ls : List (List Fraction)) (M : Matrix),
      (∀ r∈M,∀ x∈r,weight x≤B) →
      (ls.foldl (fun z _=>advance z) M).length=M.length ∧
        (∀ r∈ls.foldl (fun z _=>advance z) M,∀ x∈r,weight x≤B) := by
    intro ls
    induction ls with
    | nil => intro M hm; exact ⟨rfl,hm⟩
    | cons r ls ih =>
      intro M hm
      obtain ⟨hl,hR⟩:=ih (advance M) (advance_entries h₁ hm)
      exact ⟨hl.trans (advance_length M),hR⟩
  refine ⟨(hInv ls M hM).1,(hInv ls M hM).2,?_⟩
  cases ls using List.reverseRecOn with
  | nil => simpa only [List.foldl_nil,Nat.add_assoc] using (Nat.le_add_right (weight M) (1+M.length*(2+M.length*(B+1))))
  | append_singleton ls r ih =>
    rw [List.foldl_append]
    dsimp only [List.foldl]
    have hw:=advance_weight h₁ (hInv ls M hM).2
    rw [(hInv ls M hM).1] at hw
    omega

lemma polynomial_closeFold : PolynomialTime (fold (composition (second (A:=List Fraction)) advanceRealizer)) := by
  apply polynomial_fold (polynomial_composition polynomial_second polynomial_advance)
    (X+1+X*(2+X*(X+C (weight one)+1)))
  intro ls M pre _ _
  let S:=weight (ls,M)
  have hM : weight M≤S := weight_snd (ls,M)
  have hn : M.length≤S := (list_length_le_weight M).trans hM
  have hi:=fold_advance_invariant pre M (S+weight one) (by omega) (by
    intro r hr x hx
    exact ((weight_mem hx).trans ((weight_mem hr).trans hM)).trans (Nat.le_add_right _ _))
  have hb := hi.2.2
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one,
    Polynomial.eval_ofNat,Polynomial.eval_C]
  change weight (pre.foldl (fun z _=>advance z) M)≤S+1+S*(2+S*(S+weight one+1))
  have hp:=Nat.mul_le_mul hn (Nat.add_le_add_left (Nat.mul_le_mul_right (S+weight one+1) hn) 2)
  omega
lemma polynomial_close : PolynomialTime closeRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_seed) polynomial_closeFold

end MatchingFPRAS.ExecutableBottleneck

end OAI
