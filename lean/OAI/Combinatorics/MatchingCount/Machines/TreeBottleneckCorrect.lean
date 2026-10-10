import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.DiscreteLadderSteps
import OAI.Combinatorics.MatchingCount.Machines.TreeBottleneck

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma maximum_fold_repr (xs : List ℚ) (z : ℚ) (hz : 0≤z) (hx : ∀ x∈xs,0≤x) :
    (xs.map TreeFraction.repr).foldl (fun z x=>maximum (x,z)) (TreeFraction.repr z)=
      TreeFraction.repr (xs.foldl (fun z x=>max x z) z) := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [maximum_repr (hx x (by simp)) hz]
    exact ih _ (hz.trans (le_max_right _ _)) (fun x h=>hx x (by simp [h]))
lemma le_fold_max (xs : List ℚ) (z : ℚ) : z≤xs.foldl (fun z x=>max x z) z := by
  induction xs generalizing z with
  | nil => exact le_rfl
  | cons x xs ih => exact (le_max_right x z).trans (ih _)
lemma mem_le_fold_max (xs : List ℚ) (z v : ℚ) (hv : v∈xs) : v≤xs.foldl (fun z x=>max x z) z := by
  induction xs generalizing z with
  | nil => simp at hv
  | cons x xs ih =>
    rcases List.mem_cons.mp hv with rfl|hv
    · exact (le_max_left _ _).trans (le_fold_max xs _)
    · exact ih _ hv
lemma fold_max_le (xs : List ℚ) (z B : ℚ) (hz : z≤B) (hx : ∀ x∈xs,x≤B) :
    xs.foldl (fun z x=>max x z) z≤B := by
  induction xs generalizing z with
  | nil => exact hz
  | cons x xs ih =>
    exact ih _ (max_le (hx x (by simp)) hz) (fun x h=>hx x (by simp [h]))
lemma fold_max_ofFn {n : ℕ} (w : Fin n→ℚ) (z : ℚ) (a : Fin n) :
    (List.ofFn w).foldl (fun z x=>max x z) z=max z (Finset.univ.sup' ⟨a,Finset.mem_univ a⟩ w) := by
  apply le_antisymm
  · apply fold_max_le _ _ _ (le_max_left _ _)
    intro x hx
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hx
    exact (Finset.le_sup' w (Finset.mem_univ i)).trans (le_max_right _ _)
  · apply max_le (le_fold_max _ _)
    apply Finset.sup'_le
    intro i _
    exact mem_le_fold_max _ _ _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.ExecutableBottleneck
open TreeTyped TreeFraction

def matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) : Matrix :=
  List.ofFn fun i=>List.ofFn fun j=>TreeFraction.repr (w i j)
lemma matrixRep_length {n : ℕ} (w : Fin n→Fin n→ℚ) : (matrixRep w).length=n := by
  simp [matrixRep]
lemma cell_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (a b : Fin n) :
    cell (matrixRep w,(a.val,b.val))=TreeFraction.repr (w a b) := by
  simp [cell,matrixRep,List.getD_eq_getElem?_getD,a.isLt,b.isLt]

lemma square_eq_ofFn {A B : Type} (n : ℕ) (x : A) (f : A×(ℕ×ℕ)→B) :
    square n x f=List.ofFn fun i : Fin n=>List.ofFn fun j : Fin n=>f (x,(i.val,j.val)) := by
  apply List.ext_getElem
  · simp [square]
  · intro i hi hi'
    simp only [square,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    apply List.ext_getElem
    · simp
    · intro j hj hj'
      simp
lemma one_repr : one=TreeFraction.repr (1:ℚ) := rfl
lemma seedEntry_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (a b : Fin n) :
    seedEntry (matrixRep w,(a.val,b.val))=TreeFraction.repr (BottleneckAlgorithm.seed w a b) := by
  unfold seedEntry BottleneckAlgorithm.seed BottleneckAlgorithm.edge
  dsimp only
  by_cases hab : a=b
  · subst b; simp only [↓reduceIte,one_repr]
  · have hv : a.val≠b.val := fun he=>hab (Fin.ext he)
    rw [ite_eq_right hv,ite_eq_right hab]
    by_cases hlt : a<b
    · rw [ite_eq_left hlt,min_eq_left (show a.val≤b.val from le_of_lt hlt),max_eq_right (show a.val≤b.val from le_of_lt hlt),cell_matrixRep,one_repr]
      exact maximum_repr (by norm_num) (hw a b)
    · rw [ite_eq_right hlt,min_eq_right (show b.val≤a.val from le_of_not_gt hlt),max_eq_left (show b.val≤a.val from le_of_not_gt hlt),cell_matrixRep,one_repr]
      exact maximum_repr (by norm_num) (hw b a)
lemma seed_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) :
    seed (matrixRep w)=matrixRep (BottleneckAlgorithm.seed w) := by
  rw [seed,matrixRep_length,square_eq_ofFn]
  unfold matrixRep
  congr 1
  funext a
  congr 1
  funext b
  exact seedEntry_matrixRep w hw a b

lemma via_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (a b c : Fin n) :
    via ((matrixRep w,(a.val,b.val)),c.val)=TreeFraction.repr (min (w a c) (w c b)) := by
  unfold via
  dsimp only
  rw [cell_matrixRep,cell_matrixRep]
  exact minimum_repr (hw a c) (hw c b)
lemma entry_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (a b : Fin n) :
    entry (matrixRep w,(a.val,b.val))=TreeFraction.repr (BottleneckAlgorithm.advance w a b) := by
  unfold entry BottleneckAlgorithm.advance
  dsimp only
  by_cases hab : a=b
  · subst b; simp only [↓reduceIte,one_repr]
  · have hv : a.val≠b.val := fun he=>hab (Fin.ext he)
    rw [ite_eq_right hv,ite_eq_right hab,cell_matrixRep,matrixRep_length]
    have he : (List.range n).map (fun c=>via ((matrixRep w,(a.val,b.val)),c))=
        (List.ofFn fun c : Fin n=>min (w a c) (w c b)).map TreeFraction.repr := by
      apply List.ext_getElem
      · simp
      · intro i hi hi'
        have hi0 : i<n := by simpa using hi
        simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
        exact via_matrixRep w hw a b ⟨i,hi0⟩
    rw [he,maximum_fold_repr _ _ (hw a b) (by
      intro x hx
      obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hx
      exact le_min (hw a i) (hw i b)),fold_max_ofFn _ _ a]
lemma advance_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) :
    advance (matrixRep w)=matrixRep (BottleneckAlgorithm.advance w) := by
  rw [advance,matrixRep_length,square_eq_ofFn]
  unfold matrixRep
  congr 1
  funext a
  congr 1
  funext b
  exact entry_matrixRep w hw a b
lemma fold_advance_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (_hw : ∀ a b,0≤w a b)
    (ls : List (List Fraction)) (k : ℕ) :
    ls.foldl (fun z _=>advance z) (matrixRep (BottleneckAlgorithm.close w k))=
      matrixRep (BottleneckAlgorithm.close w (k+ls.length)) := by
  induction ls generalizing k with
  | nil => simp
  | cons r ls ih =>
    rw [List.foldl_cons,advance_matrixRep _ (fun a b=>
      (show (0:ℚ)≤1 by norm_num).trans (BottleneckAlgorithm.close_one w k a b))]
    change ls.foldl (fun z _=>advance z) (matrixRep (BottleneckAlgorithm.close w (k+1)))=_
    rw [ih]
    congr 2
    simp only [List.length_cons]; omega

theorem close_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) :
    close (matrixRep w)=matrixRep (BottleneckAlgorithm.close w n) := by
  unfold close
  rw [seed_matrixRep w hw]
  change (matrixRep w).foldl (fun z _=>advance z) (matrixRep (BottleneckAlgorithm.close w 0))=_
  rw [fold_advance_matrixRep _ hw,matrixRep_length,Nat.zero_add]
end MatchingFPRAS.ExecutableBottleneck

end OAI
