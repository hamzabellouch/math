import Mathlib
import OAI.Combinatorics.StripMass.LocalPadding

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
open Finset
namespace Pairing

lemma map_not_occupied_omit {n : ℕ} (p : Pairing n) (a : Fin (n+1)) :
    ¬(p.map (Fin.succAboveOrderEmb a)).Occupied a := by
  rintro ⟨_,h⟩
  obtain ⟨i,j,_,hi,_⟩ := (map_adj _ p _ _).mp h
  exact Fin.succAbove_ne a i hi

lemma moveIntoVacancy_eq_self {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (ha : ¬p.Occupied a) (hb : ¬p.Occupied b) :
    p.moveIntoVacancy a b hab hb=p := by
  apply ext_adj
  intro i j
  rw [moveIntoVacancy_adj]
  have hn (x y : Fin n) (h : p.Adj x y) : Equiv.swap a b x=x := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro he; exact ha ⟨y,he ▸ h⟩
    · intro he; exact hb ⟨y,he ▸ h⟩
  constructor
  · intro h
    have hi := hn _ _ h
    have hj := hn _ _ (adj_symm h)
    simp only [Equiv.swap_apply_self] at hi hj
    rwa [←hi,←hj] at h
  · intro h
    rw [hn _ _ h,hn _ _ (adj_symm h)]
    exact h

lemma moveIntoVacancy_map_omit {n : ℕ} (p : Pairing n) (a b : Fin (n+1))
    (hab : a.val+1=b.val) :
    (p.map (Fin.succAboveOrderEmb b)).moveIntoVacancy a b hab (p.map_not_occupied_omit b)=
      p.map (Fin.succAboveOrderEmb a) := by
  apply ext_adj
  intro x y
  rw [moveIntoVacancy_adj,map_adj,map_adj]
  constructor
  · rintro ⟨i,j,h,hi,hj⟩
    refine ⟨i,j,h,?_,?_⟩
    · have hh:=congrArg (Equiv.swap a b) hi
      simpa only [Fin.succAboveOrderEmb_apply,Fin.swap_succAbove_adjacent a b hab,
        Equiv.swap_apply_self] using hh
    · have hh:=congrArg (Equiv.swap a b) hj
      simpa only [Fin.succAboveOrderEmb_apply,Fin.swap_succAbove_adjacent a b hab,
        Equiv.swap_apply_self] using hh
  · rintro ⟨i,j,h,hi,hj⟩
    refine ⟨i,j,h,?_,?_⟩
    · have hh:=congrArg (Equiv.swap a b) hi
      simp only [Fin.succAboveOrderEmb_apply] at hh
      rw [←Fin.swap_succAbove_adjacent a b hab i,Equiv.swap_apply_self] at hh
      exact hh
    · have hh:=congrArg (Equiv.swap a b) hj
      simp only [Fin.succAboveOrderEmb_apply] at hh
      rw [←Fin.swap_succAbove_adjacent a b hab j,Equiv.swap_apply_self] at hh
      exact hh
end Pairing

variable {K : Type*} [CommRing K]
lemma localR_swap_vacant {n : ℕ} (a : Position n) (p q : Pairing n)
    (hb : ¬p.Occupied a.right) :
    (localR a (swapWeights : Weights K)) q p =
      if p.moveIntoVacancy a.left a.right a.adjacent hb=q then 1 else 0 := by
  simp only [localR,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  by_cases ha : p.Occupied a.left
  · rw [sum_eq_single .diagonal₀]
    · simp [swapWeights,Weights.tile,optionMatrix,Pairing.tileStep,ha,hb]
    · intro t _ ht
      cases t <;> simp_all [swapWeights,Weights.tile,optionMatrix,Pairing.tileStep]
    · simp
  · rw [Pairing.moveIntoVacancy_eq_self p _ _ a.adjacent ha hb]
    rw [sum_eq_single .vacant]
    · simp [Weights.tile,optionMatrix,Pairing.tileStep,ha,hb]
    · intro t _ ht
      cases t <;> simp_all [swapWeights,Weights.tile,optionMatrix,Pairing.tileStep]
    · simp

lemma localR_swap_omit {n : ℕ} (a : Position (n+1)) :
    localR a (swapWeights : Weights K) *
        functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb a.right)) =
      functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb a.left)) := by
  ext q p
  rw [mul_functionMatrix,localR_swap_vacant _ _ _ (p.map_not_occupied_omit a.right),
    Pairing.moveIntoVacancy_map_omit]
  simp [functionMatrix,optionMatrix]

end

 

 

noncomputable section
open scoped Classical
namespace PartialColumn
variable {K : Type*} [CommRing K] {n : ℕ}

lemma insert_before_gate (r : Fin (n+1)) (w : Fin (n+1) → Weights K)
    (v : Fin n → Weights K) (hw : ∀ i, w (r.succAbove i)=v i) (i : Fin n) (hi : i.val<r.val) :
    localR (position i.castSucc) (w i.castSucc) *
        functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.succ)) =
      functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.succ)) *
        localR (position i) (v i) := by
  have hiw := hw i
  rw [Fin.succAbove_of_castSucc_lt r i hi] at hiw
  rw [hiw]
  apply localR_natural
  · change r.succ.succAbove i.castSucc=i.castSucc.castSucc
    apply Fin.succAbove_of_castSucc_lt
    change i.val<r.val+1
    omega
  · change r.succ.succAbove i.succ=i.castSucc.succ
    rw [Fin.succAbove_of_castSucc_lt _ _ (by change i.val+1<r.val+1; omega)]
    exact Fin.ext rfl

lemma insert_after_gate (r : Fin (n+1)) (w : Fin (n+1) → Weights K)
    (v : Fin n → Weights K) (hw : ∀ i, w (r.succAbove i)=v i) (i : Fin n) (hi : r.val ≤ i.val) :
    localR (position i.succ) (w i.succ) *
        functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.castSucc)) =
      functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.castSucc)) *
        localR (position i) (v i) := by
  have hiw := hw i
  rw [Fin.succAbove_of_le_castSucc r i hi] at hiw
  rw [hiw]
  apply localR_natural
  · change r.castSucc.succAbove i.castSucc=i.succ.castSucc
    rw [Fin.succAbove_of_le_castSucc _ _ (by change r.val ≤ i.val; exact hi)]
    exact Fin.ext rfl
  · change r.castSucc.succAbove i.succ=i.succ.succ
    apply Fin.succAbove_of_le_castSucc
    change r.val ≤ i.val+1
    omega

lemma insert_before_program (r : Fin (n+1)) (w : Fin (n+1) → Weights K)
    (v : Fin n → Weights K) (hw : ∀ i, w (r.succAbove i)=v i)
    (k : ℕ) (hk : k≤r.val) :
    (program w k (by omega)).matrix *
        functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.succ)) =
      functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.succ)) *
        (program v k (by omega)).matrix := by
  induction k with
  | zero => change 1*_=_*1; simp
  | succ k ih =>
    have hkn : k<n := by have:=r.isLt; omega
    change (localR (position (n:=n+1) ⟨k,by omega⟩) (w ⟨k,by omega⟩) *
      (program w k _).matrix)*_ = _ *
      (localR (position (n:=n) ⟨k,hkn⟩) (v ⟨k,hkn⟩) * (program v k _).matrix)
    have hgate := insert_before_gate r w v hw ⟨k,hkn⟩ (by change k<r.val; omega)
    simp only [Fin.castSucc_mk] at hgate
    rw [Matrix.mul_assoc,ih (by omega),←Matrix.mul_assoc,hgate,Matrix.mul_assoc]

lemma insert_after_program (r : Fin (n+1)) (w : Fin (n+1) → Weights K)
    (v : Fin n → Weights K) (hw : ∀ i, w (r.succAbove i)=v i) (hr : w r=swapWeights)
    (k : ℕ) (hk : r.val ≤ k) (hkn : k≤n) :
    (program w (k+1) (by omega)).matrix *
        functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.succ)) =
      functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.castSucc)) *
        (program v k hkn).matrix := by
  induction k,hk using Nat.le_induction with
  | base =>
    rw [program,Program.matrix]
    have hrr : (⟨r.val,by omega⟩ : Fin (n+1))=r := Fin.ext rfl
    rw [hrr]
    rw [Matrix.mul_assoc,insert_before_program r w v hw r.val le_rfl,←Matrix.mul_assoc,hr]
    have hs := localR_swap_omit (K:=K) (position r)
    change localR (position r) swapWeights *
      functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.succ)) =
      functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.castSucc)) at hs
    rw [hs]
  | succ k hk ih =>
    have hi : k<n := by omega
    change (localR (position (n:=n+1) ⟨k+1,by omega⟩) (w ⟨k+1,by omega⟩) *
      (program w (k+1) _).matrix)*_ = _ *
      (localR (position (n:=n) ⟨k,hi⟩) (v ⟨k,hi⟩) * (program v k _).matrix)
    have hgate := insert_after_gate r w v hw ⟨k,hi⟩ hk
    simp only [Fin.succ_mk] at hgate
    rw [Matrix.mul_assoc,ih (by omega),←Matrix.mul_assoc,hgate,Matrix.mul_assoc]

end PartialColumn

 

 

namespace Pairing

lemma map_map {n m l : ℕ} (f : Fin n ↪o Fin m) (g : Fin m ↪o Fin l) (p : Pairing n) :
    (p.map f).map g=p.map (f.trans g) := by
  apply Subtype.ext
  change (p.val.map _).map _=p.val.map _
  rw [Finset.map_map]
  rfl

lemma map_empty {n m : ℕ} (f : Fin n ↪o Fin m) : (empty n).map f=empty m := by
  apply Subtype.ext
  exact Finset.map_empty _

lemma omit_padBottom {n : ℕ} (r : Fin (n+1)) (p : Pairing n) :
    (p.map (Fin.succAboveOrderEmb r)).padBottom =
      p.padBottom.map (Fin.succAboveOrderEmb r.succ) := by
  unfold padBottom
  rw [map_map,map_map]
  congr 1
  apply DFunLike.ext
  intro i
  change (r.succAbove i).succ=r.succ.succAbove i.succ
  by_cases hi : i.val<r.val <;> simp [Fin.succAbove,Fin.lt_def,hi]

lemma omit_padTop {n : ℕ} (r : Fin (n+1)) (p : Pairing n) :
    (p.map (Fin.succAboveOrderEmb r)).padTop =
      p.padTop.map (Fin.succAboveOrderEmb r.castSucc) := by
  unfold padTop
  rw [map_map,map_map]
  congr 1
  apply DFunLike.ext
  intro i
  change (r.succAbove i).castSucc=r.castSucc.succAbove i.castSucc
  by_cases hi : i.val<r.val <;> simp [Fin.succAbove,Fin.lt_def,hi]

lemma omit_last {n : ℕ} (r : Fin (n+1)) :
    (Fin.succAboveOrderEmb r.castSucc) (Fin.last n)=Fin.last (n+1) := by
  change r.castSucc.succAbove (Fin.last n)=Fin.last (n+1)
  rw [Fin.succAbove_of_le_castSucc _ _ (by change r.val≤n; omega)]
  rfl

lemma omit_eq_padTop_exists {n : ℕ} (r : Fin (n+1)) (t : Pairing (n+1))
    (q : Pairing (n+1)) (h : t.map (Fin.succAboveOrderEmb r.castSucc)=q.padTop) :
    ∃ p : Pairing n, p.padTop=t := by
  apply Exists.intro (t.restrict Fin.castSuccOrderEmb)
  apply padTop_restrict
  intro ht
  have hh : (t.map (Fin.succAboveOrderEmb r.castSucc)).Occupied (Fin.last (n+1)) := by
    rw [←omit_last r]
    exact (map_occupied _ t _).mpr ht
  rw [h] at hh
  exact q.padTop_not_occupied_last hh

end Pairing
end

 

 

noncomputable section
open scoped Classical
open Finset
namespace PartialColumn
variable {K : Type*} [CommRing K] {n : ℕ}

lemma program_column_all (w : Fin n → Weights K) (p q : Pairing n) :
    (program w n le_rfl).matrix q.padTop p.padBottom=column w q p := by
  by_cases hn : 0<n
  · exact program_column hn w p q
  · have h : n=0 := by omega
    subst n
    rw [p.eq_empty_of_le_one (by omega),q.eq_empty_of_le_one (by omega),column_empty_row]
    simp only [ite_true]
    change (1 : Matrix (Pairing 1) (Pairing 1) K) (empty 0).padTop (empty 0).padBottom=1
    rw [show (empty 0).padTop=(empty 0).padBottom by rw [Pairing.padTop,Pairing.padBottom,
      Pairing.map_empty,Pairing.map_empty]]
    exact Matrix.one_apply_eq _

lemma omit_top_matrix (r : Fin (n+1))
    (M : Matrix (Pairing (n+1)) (Pairing (n+1)) K) (p : Pairing n) (q : Pairing (n+1)) :
    (functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.castSucc)) * M) q.padTop p.padBottom =
      (functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r)) *
        M.submatrix Pairing.padTop Pairing.padBottom) q p := by
  rw [Matrix.mul_apply,Matrix.mul_apply]
  symm
  apply Fintype.sum_of_injective Pairing.padTop (Pairing.map_injective Fin.castSuccOrderEmb)
  · intro t ht
    have hn : t.map (Fin.succAboveOrderEmb r.castSucc)≠q.padTop := by
      intro he
      exact ht (Pairing.omit_eq_padTop_exists r t q he)
    simp only [functionMatrix,optionMatrix,Function.comp_apply,Option.some.injEq,
      ite_eq_right hn,zero_mul]
  · intro t
    simp only [Matrix.submatrix_apply,functionMatrix,optionMatrix,Function.comp_apply,
      Option.some.injEq,←Pairing.omit_padTop]
    simp only [Pairing.padTop,(Pairing.map_injective Fin.castSuccOrderEmb).eq_iff]

 

theorem column_insert_swap (r : Fin (n+1)) (w : Fin (n+1) → Weights K)
    (v : Fin n → Weights K) (hw : ∀ i, w (r.succAbove i)=v i) (hr : w r=swapWeights) :
    column w * functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r)) =
      functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r)) * column v := by
  have H := insert_after_program r w v hw hr n (by omega) le_rfl
  have he : (program v n le_rfl).matrix.submatrix Pairing.padTop Pairing.padBottom=column v := by
    ext q p; exact program_column_all v p q
  ext q p
  have hh:=congrArg (fun M => M q.padTop p.padBottom) H
  rw [mul_functionMatrix,←Pairing.omit_padBottom,program_column_all,omit_top_matrix,he] at hh
  rw [mul_functionMatrix]
  exact hh

end PartialColumn
end

 

 

noncomputable section
open scoped Classical
namespace PartialColumn
variable {n m : ℕ}

 
def twoRows {K : Type*} (w : Fin n → Weights K) (r : ℕ) (a b : Weights K) : Fin n → Weights K :=
  fun i => if i.val=r then a else if i.val=r+1 then b else w i

lemma twoRows₀ {K : Type*} (w : Fin n → Weights K) (r : ℕ) (hr : r+2≤n) (a b : Weights K) :
    twoRows w r a b ⟨r,by omega⟩=a := by simp [twoRows]
lemma twoRows₁ {K : Type*} (w : Fin n → Weights K) (r : ℕ) (hr : r+2≤n) (a b : Weights K) :
    twoRows w r a b ⟨r+1,by omega⟩=b := by simp [twoRows]
lemma twoRows_other {K : Type*} (w : Fin n → Weights K) (r : ℕ) (a b : Weights K)
    (i : Fin n) (hi : i.val≠r) (hj : i.val≠r+1) : w i=twoRows w r a b i := by simp [twoRows,hi,hj]

 

theorem column_merge_intertwiner (r : ℕ) (hr : r+2≤n+1)
    (w : Fin (n+1) → Weights (SpectralField m)) (z : SpectralField m)
    (hz : z≠0) (hL : torusL z≠0) (hL1 : torusL (constF m phase*z)≠0)
    (hL2 : torusL (constF m phase^2*z)≠0)
    (hw₀ : w ⟨r,by omega⟩=torusWeights (constF m phase^2*z))
    (hw₁ : w ⟨r+1,by omega⟩=torusWeights z) :
    let j : Fin (n+1) := ⟨r+1,by omega⟩
    let v := twoRows w r (torusWeights (constF m phase*z)) swapWeights
    let E := functionMatrix (K:=SpectralField m) (Pairing.map (Fin.succAboveOrderEmb j))
    let S := localR (rowPosition r hr) (mergeWeights (constF m phase))
    column w * (S*E) = (S*E) * column (fun i => v (j.succAbove i)) := by
  dsimp only
  let j : Fin (n+1) := ⟨r+1,by omega⟩
  let v := twoRows w r (torusWeights (constF m phase*z)) swapWeights
  let E := functionMatrix (K:=SpectralField m) (Pairing.map (Fin.succAboveOrderEmb j))
  let S := localR (rowPosition r hr) (mergeWeights (constF m phase))
  change column w*(S*E)=(S*E)*column (fun i => v (j.succAbove i))
  have hpass := column_insert_swap j v (fun i => v (j.succAbove i)) (fun _ => rfl)
    (twoRows₁ w r hr _ _)
  have htrain : (column w*S)*E=(S*column v)*E := by
    ext q p
    rw [mul_functionMatrix,mul_functionMatrix]
    apply column_merge r hr w v z hz hL hL1 hL2 hw₀ hw₁
      (twoRows₀ w r hr _ _) (twoRows₁ w r hr _ _) (twoRows_other w r _ _)
    exact p.map_not_occupied_omit j
  rw [←Matrix.mul_assoc,htrain,Matrix.mul_assoc,hpass,←Matrix.mul_assoc]

 
theorem column_deletion_intertwiner (r : ℕ) (hr : r+2≤n+2)
    (w : Fin (n+2) → Weights (SpectralField m)) (z : SpectralField m)
    (hz : z≠0) (hL : torusL z≠0) (hL3 : torusL (constF m phase^3*z)≠0)
    (hw₀ : w ⟨r,by omega⟩=torusWeights (constF m phase^3*z))
    (hw₁ : w ⟨r+1,by omega⟩=torusWeights z) :
    let j : Fin (n+2) := ⟨r+1,by omega⟩
    let k : Fin (n+1) := ⟨r,by omega⟩
    let v := twoRows w r swapWeights swapWeights
    let ER := functionMatrix (K:=SpectralField m) (Pairing.map (Fin.succAboveOrderEmb j))
    let EL := functionMatrix (K:=SpectralField m) (Pairing.map (Fin.succAboveOrderEmb k))
    let S : Matrix (Pairing (n+2)) (Pairing (n+2)) (SpectralField m) := localR (rowPosition r hr) deletionWeights
    (column w * (S*(ER*EL)) : Matrix (Pairing (n+2)) (Pairing n) (SpectralField m)) = (S*(ER*EL)) * column (fun i => v (j.succAbove (k.succAbove i))) := by
  dsimp only
  let j : Fin (n+2) := ⟨r+1,by omega⟩
  let k : Fin (n+1) := ⟨r,by omega⟩
  let v := twoRows w r swapWeights swapWeights
  let ER := functionMatrix (K:=SpectralField m) (Pairing.map (Fin.succAboveOrderEmb j))
  let EL := functionMatrix (K:=SpectralField m) (Pairing.map (Fin.succAboveOrderEmb k))
  let S : Matrix (Pairing (n+2)) (Pairing (n+2)) (SpectralField m) := localR (rowPosition r hr) deletionWeights
  change column w*(S*(ER*EL))=(S*(ER*EL))*column (fun i => v (j.succAbove (k.succAbove i)))
  have hjk : j.succAbove k=⟨r,by omega⟩ := by
    rw [Fin.succAbove_of_castSucc_lt]
    · rfl
    · change r<r+1; omega
  have hpassR := column_insert_swap j v (fun i => v (j.succAbove i)) (fun _ => rfl)
    (twoRows₁ w r hr _ _)
  have hpassL := column_insert_swap k (fun i => v (j.succAbove i))
    (fun i => v (j.succAbove (k.succAbove i))) (fun _ => rfl)
    (by rw [hjk]; exact twoRows₀ w r hr _ _)
  have htrain : (column w*S)*(ER*EL)=(S*column v)*(ER*EL) := by
    ext q p
    rw [←Matrix.mul_assoc,←Matrix.mul_assoc,mul_functionMatrix,mul_functionMatrix,
      mul_functionMatrix,mul_functionMatrix]
    apply column_deletion r hr w v z hz hL hL3 hw₀ hw₁
      (twoRows₀ w r hr _ _) (twoRows₁ w r hr _ _) (twoRows_other w r _ _)
    · rw [←hjk]
      exact fun h => p.map_not_occupied_omit k ((Pairing.map_occupied _ _ _).mp h)
    · exact (p.map (Fin.succAboveOrderEmb k)).map_not_occupied_omit j
  rw [←Matrix.mul_assoc,htrain]
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (column v) ER EL,hpassR,Matrix.mul_assoc,hpassL]

end PartialColumn
end

 

 

noncomputable section
open scoped Classical
open Finset

lemma Pairing.tileStep_empty_iff {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) :
    p.tileStep a b hab t=some (empty n) ↔ p=empty n ∧ t=.vacant := by
  constructor
  · intro h
    have hg:=p.stepWiring_realizes a b hab t (empty n) h
    have hp : p=empty n := by
      apply (Pairing.eq_empty_iff p).mpr
      rintro i ⟨j,hij⟩
      obtain ⟨k,hk,_⟩ := hg.no_loop (.old i) (.old j) hij
      exact empty_not_occupied k hk
    have ht : t=.vacant := by
      apply (Tile.eq_vacant_iff t).mpr
      rintro i ⟨j,hij⟩
      obtain ⟨k,hk,_⟩ := hg.no_loop (.box i) (.box j) hij
      exact empty_not_occupied k hk
    exact ⟨hp,ht⟩
  · rintro ⟨rfl,rfl⟩
    simp [Pairing.tileStep]

lemma localR_empty_row {K : Type*} [CommRing K] {n : ℕ} (a : Position n) (w : Weights K)
    (p : Pairing n) : localR a w (empty n) p=if p=empty n then 1 else 0 := by
  unfold localR
  simp only [Matrix.sum_apply,Matrix.smul_apply,optionMatrix,Pairing.tileStep_empty_iff]
  by_cases hp : p=empty n
  · simp [hp,Weights.tile]
  · simp [hp]

lemma localR_mulVec_empty {K : Type*} [CommRing K] {n : ℕ} (a : Position n) (w : Weights K)
    (v : Pairing n → K) : (localR a w).mulVec v (empty n)=v (empty n) := by
  simp [Matrix.mulVec,dotProduct,localR_empty_row]

 

theorem normalizedVacuum_torus_exchange {n m : ℕ} (r : ℕ) (hr : r+2≤n)
    (x : Fin n → SpectralField m) (z : SpectralField m) (hz : z≠0)
    (hw : x ⟨r+1,by omega⟩≠0) (hLz : torusL z≠0)
    (hLw : torusL (x ⟨r+1,by omega⟩)≠0) (hLx : torusL (x ⟨r,by omega⟩)≠0)
    (hx : z*x ⟨r+1,by omega⟩=x ⟨r,by omega⟩)
    (hreg : VacuumRegular (fun i => torusWeights (x i)))
    (hreg' : VacuumRegular (fun i => torusWeights (x (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩ i)))) :
    normalizedVacuum (fun i => torusWeights (x i)) =
      (localR (PartialColumn.rowPosition r hr) (torusWeights z)).mulVec
        (normalizedVacuum (fun i => torusWeights (x (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩ i)))) := by
  symm
  apply normalizedVacuum_unique _ hreg
  have hs := normalizedVacuum_stationary _ hreg'
  constructor
  · rw [localR_mulVec_empty]; exact hs.1
  · rw [Matrix.mulVec_mulVec,PartialColumn.torus_column_exchange r hr x z hz hw hLz hLw hLx hx,
      ←Matrix.mulVec_mulVec,hs.2]


 

 


lemma Pairing.map_eq_empty_iff {n m : ℕ} (e : Fin n ↪o Fin m) (p : Pairing n) :
    p.map e=empty m ↔ p=empty n := by
  rw [←Pairing.map_empty e]
  exact (Pairing.map_injective e).eq_iff

lemma functionMatrix_map_mulVec_empty {K : Type*} [CommRing K] {n m : ℕ}
    (e : Fin n ↪o Fin m) (v : Pairing n → K) :
    (functionMatrix (K:=K) (Pairing.map e)).mulVec v (empty m)=v (empty n) := by
  simp [Matrix.mulVec,dotProduct,functionMatrix,optionMatrix,Pairing.map_eq_empty_iff]

 
def mergeMap {n m : ℕ} (r : ℕ) (hr : r+2≤n+1) :
    Matrix (Pairing (n+1)) (Pairing n) (SpectralField m) :=
  localR (PartialColumn.rowPosition r hr) (mergeWeights (constF m phase)) *
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb ⟨r+1,by omega⟩))

 
def deletionMap {n m : ℕ} (r : ℕ) (hr : r+2≤n+2) :
    Matrix (Pairing (n+2)) (Pairing n) (SpectralField m) :=
  localR (PartialColumn.rowPosition r hr) deletionWeights *
    (functionMatrix (Pairing.map (Fin.succAboveOrderEmb (⟨r+1,by omega⟩ : Fin (n+2)))) *
      functionMatrix (Pairing.map (Fin.succAboveOrderEmb (⟨r,by omega⟩ : Fin (n+1)))))

lemma mergeMap_mulVec_empty {n m : ℕ} (r : ℕ) (hr : r+2≤n+1)
    (v : Pairing n → SpectralField m) :
    (mergeMap r hr).mulVec v (empty (n+1))=v (empty n) := by
  simp only [mergeMap]
  let E : Matrix (Pairing (n+1)) (Pairing n) (SpectralField m) :=
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb ⟨r+1,by omega⟩))
  let S := localR (PartialColumn.rowPosition r hr) (mergeWeights (constF m phase))
  calc
    _ = S.mulVec (E.mulVec v) (empty (n+1)) :=
      congrFun (Matrix.mulVec_mulVec v S E).symm _
    _ = E.mulVec v (empty (n+1)) := localR_mulVec_empty _ _ _
    _ = _ := functionMatrix_map_mulVec_empty _ _
lemma deletionMap_mulVec_empty {n m : ℕ} (r : ℕ) (hr : r+2≤n+2)
    (v : Pairing n → SpectralField m) :
    (deletionMap r hr).mulVec v (empty (n+2))=v (empty n) := by
  simp only [deletionMap]
  let E₁ : Matrix (Pairing (n+2)) (Pairing (n+1)) (SpectralField m) :=
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb ⟨r+1,by omega⟩))
  let E₀ : Matrix (Pairing (n+1)) (Pairing n) (SpectralField m) :=
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb ⟨r,by omega⟩))
  let S := localR (PartialColumn.rowPosition r hr) (deletionWeights : Weights (SpectralField m))
  calc
    _ = S.mulVec ((E₁*E₀).mulVec v) (empty (n+2)) :=
      congrFun (Matrix.mulVec_mulVec v S (E₁*E₀)).symm _
    _ = (E₁*E₀).mulVec v (empty (n+2)) := localR_mulVec_empty _ _ _
    _ = E₁.mulVec (E₀.mulVec v) (empty (n+2)) :=
      congrFun (Matrix.mulVec_mulVec v E₁ E₀).symm _
    _ = E₀.mulVec v (empty (n+1)) := functionMatrix_map_mulVec_empty _ _
    _ = _ := functionMatrix_map_mulVec_empty _ _

 
theorem normalizedVacuum_merge {n m : ℕ} (r : ℕ) (hr : r+2≤n+1)
    (w : Fin (n+1) → Weights (SpectralField m)) (z : SpectralField m)
    (hz : z≠0) (hL : torusL z≠0) (hL1 : torusL (constF m phase*z)≠0)
    (hL2 : torusL (constF m phase^2*z)≠0)
    (hw₀ : w ⟨r,by omega⟩=torusWeights (constF m phase^2*z))
    (hw₁ : w ⟨r+1,by omega⟩=torusWeights z)
    (hreg : VacuumRegular w)
    (hreg' : VacuumRegular (fun i => (PartialColumn.twoRows w r
      (torusWeights (constF m phase*z)) swapWeights) ((⟨r+1,by omega⟩ : Fin (n+1)).succAbove i))) :
    normalizedVacuum w = (mergeMap r hr).mulVec (normalizedVacuum
      (fun i => (PartialColumn.twoRows w r (torusWeights (constF m phase*z)) swapWeights)
        ((⟨r+1,by omega⟩ : Fin (n+1)).succAbove i))) := by
  symm
  apply normalizedVacuum_unique _ hreg
  have hs:=normalizedVacuum_stationary _ hreg'
  constructor
  · rw [mergeMap_mulVec_empty]; exact hs.1
  · have he := PartialColumn.column_merge_intertwiner r hr w z hz hL hL1 hL2 hw₀ hw₁
    change column w*mergeMap r hr = mergeMap r hr*column _ at he
    rw [Matrix.mulVec_mulVec,he,←Matrix.mulVec_mulVec,hs.2]

theorem normalizedVacuum_deletion {n m : ℕ} (r : ℕ) (hr : r+2≤n+2)
    (w : Fin (n+2) → Weights (SpectralField m)) (z : SpectralField m)
    (hz : z≠0) (hL : torusL z≠0) (hL3 : torusL (constF m phase^3*z)≠0)
    (hw₀ : w ⟨r,by omega⟩=torusWeights (constF m phase^3*z))
    (hw₁ : w ⟨r+1,by omega⟩=torusWeights z)
    (hreg : VacuumRegular w)
    (hreg' : VacuumRegular (fun i => w ((⟨r+1,by omega⟩ : Fin (n+2)).succAbove
      ((⟨r,by omega⟩ : Fin (n+1)).succAbove i)))) :
    normalizedVacuum w = (deletionMap r hr).mulVec (normalizedVacuum
      (fun i => w ((⟨r+1,by omega⟩ : Fin (n+2)).succAbove
        ((⟨r,by omega⟩ : Fin (n+1)).succAbove i)))) := by
  let j : Fin (n+2) := ⟨r+1,by omega⟩
  let k : Fin (n+1) := ⟨r,by omega⟩
  have hrows : (fun i => (PartialColumn.twoRows w r swapWeights swapWeights)
      (j.succAbove (k.succAbove i)))=(fun i => w (j.succAbove (k.succAbove i))) := by
    funext i
    symm
    apply PartialColumn.twoRows_other
    · intro h
      have hk:=Fin.succAbove_ne k i
      apply hk
      have hjk : j.succAbove k=⟨r,by omega⟩ := by
        rw [Fin.succAbove_of_castSucc_lt]
        · rfl
        · change r<r+1; omega
      apply Fin.succAbove_right_injective
      rw [hjk]
      exact Fin.ext h
    · exact fun h => Fin.succAbove_ne j (k.succAbove i) (Fin.ext h)
  have he := PartialColumn.column_deletion_intertwiner r hr w z hz hL hL3 hw₀ hw₁
  change column w*deletionMap r hr=deletionMap r hr*column _ at he
  rw [hrows] at he
  symm
  apply normalizedVacuum_unique _ hreg
  have hs:=normalizedVacuum_stationary _ hreg'
  constructor
  · rw [deletionMap_mulVec_empty]; exact hs.1
  · rw [Matrix.mulVec_mulVec,he,←Matrix.mulVec_mulVec,hs.2]

end
end CriticalStrip.Diagram

end OAI
