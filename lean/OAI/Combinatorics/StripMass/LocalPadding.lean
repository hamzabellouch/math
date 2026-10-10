import Mathlib
import OAI.Combinatorics.StripMass.ColumnSweep
import OAI.Combinatorics.StripMass.MirrorExterior

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
open Finset
namespace Position
variable {n : ℕ}
def padTop (a : Position n) : Position (n+1) :=
  ⟨a.left.castSucc,a.right.castSucc,a.adjacent⟩
def padBottom (a : Position n) : Position (n+1) :=
  ⟨a.left.succ,a.right.succ,by have:=a.adjacent; simp only [Fin.val_succ]; omega⟩
end Position

namespace Pairing
lemma map_injective {n m : ℕ} (f : Fin n ↪o Fin m) : Function.Injective (Pairing.map f) := by
  intro p q h
  simpa only [restrict_map] using congrArg (Pairing.restrict f) h
end Pairing

lemma optionMatrix_map {K P Q : Type*} [Zero K] [One K] (e : P → Q) (he : Function.Injective e)
    (f : P → Option P) (g : Q → Option Q) (h : ∀ p, g (e p)=(f p).map e) (p q : P) :
    (optionMatrix g : Matrix Q Q K) (e q) (e p) = optionMatrix f q p := by
  unfold optionMatrix
  rw [h]
  cases hf : f p <;> simp [he.eq_iff]

lemma localR_padTop {K : Type*} [CommRing K] {n : ℕ} (a : Position n) (w : Weights K)
    (p q : Pairing n) :
    localR a.padTop w q.padTop p.padTop=localR a w q p := by
  unfold localR
  simp only [Matrix.sum_apply,Matrix.smul_apply]
  apply sum_congr rfl
  intro t _
  congr 1
  exact optionMatrix_map Pairing.padTop (Pairing.map_injective Fin.castSuccOrderEmb)
    _ _ (fun p => p.map_tileStep Fin.castSuccOrderEmb a.left a.right a.adjacent a.adjacent t) p q

lemma localR_padBottom {K : Type*} [CommRing K] {n : ℕ} (a : Position n) (w : Weights K)
    (p q : Pairing n) :
    localR a.padBottom w q.padBottom p.padBottom=localR a w q p := by
  unfold localR
  simp only [Matrix.sum_apply,Matrix.smul_apply]
  apply sum_congr rfl
  intro t _
  congr 1
  exact optionMatrix_map Pairing.padBottom (Pairing.map_injective (Fin.succOrderEmb n))
    _ _ (fun p => p.map_tileStep (Fin.succOrderEmb n) a.left a.right a.adjacent a.padBottom.adjacent t) p q

lemma localR_zero_of_support {K : Type*} [CommRing K] {n : ℕ} (a : Position n) (w : Weights K)
    (p q : Pairing n) (i : Fin n) (hia : i≠a.left) (hib : i≠a.right)
    (h : ¬ (q.Occupied i ↔ p.Occupied i)) : localR a w q p=0 := by
  unfold localR
  simp only [Matrix.sum_apply,Matrix.smul_apply,optionMatrix]
  apply sum_eq_zero
  intro t _
  have hn : p.tileStep a.left a.right a.adjacent t≠some q := by
    intro hh
    have hs := p.tileStep_support a.left a.right a.adjacent t q hh i
    exact h (by simpa only [Pairing.stepSupport,ite_eq_right hia,ite_eq_right hib] using hs)
  simp only [hn,ite_false,smul_zero]

lemma localR_padTop_outside {K : Type*} [CommRing K] {n : ℕ} (a : Position n) (w : Weights K)
    (p : Pairing (n+1)) (q : Pairing n) (hp : ¬ ∃ r : Pairing n, r.padTop=p) :
    localR a.padTop w q.padTop p=0 := by
  apply localR_zero_of_support a.padTop w p q.padTop (Fin.last n)
  · intro he; have hh:=congrArg Fin.val he; simp [Position.padTop] at hh; omega
  · intro he; have hh:=congrArg Fin.val he; simp [Position.padTop] at hh; omega
  · simp only [Pairing.padTop_not_occupied_last,false_iff,not_not]
    by_contra hh
    exact hp ⟨p.restrict Fin.castSuccOrderEmb,Pairing.padTop_restrict p hh⟩

lemma localR_padBottom_outside {K : Type*} [CommRing K] {n : ℕ} (a : Position n) (w : Weights K)
    (p : Pairing n) (q : Pairing (n+1)) (hq : ¬ ∃ r : Pairing n, r.padBottom=q) :
    localR a.padBottom w q p.padBottom=0 := by
  apply localR_zero_of_support a.padBottom w p.padBottom q 0
  · intro he; have hh:=congrArg Fin.val he; simp [Position.padBottom] at hh
  · intro he; have hh:=congrArg Fin.val he; simp [Position.padBottom] at hh
  · simp only [Pairing.padBottom_not_occupied_zero,iff_false,not_not]
    by_contra hh
    exact hq ⟨q.restrict (Fin.succOrderEmb n),Pairing.padBottom_restrict q hh⟩

lemma localR_top_matrix {K : Type*} [CommRing K] {n : ℕ} (a : Position n) (w : Weights K)
    (M : Matrix (Pairing (n+1)) (Pairing (n+1)) K) (p q : Pairing n) :
    (localR a.padTop w * M) q.padTop p.padBottom =
      (localR a w * M.submatrix Pairing.padTop Pairing.padBottom) q p := by
  simp only [Matrix.mul_apply,Matrix.submatrix_apply]
  symm
  apply Fintype.sum_of_injective Pairing.padTop (Pairing.map_injective Fin.castSuccOrderEmb)
  · intro r hr
    simp only [localR_padTop_outside a w r q hr,zero_mul]
  · intro r
    rw [localR_padTop]

lemma localR_bottom_matrix {K : Type*} [CommRing K] {n : ℕ} (a : Position n) (w : Weights K)
    (M : Matrix (Pairing (n+1)) (Pairing (n+1)) K) (p q : Pairing n) :
    (M * localR a.padBottom w) q.padTop p.padBottom =
      (M.submatrix Pairing.padTop Pairing.padBottom * localR a w) q p := by
  simp only [Matrix.mul_apply,Matrix.submatrix_apply]
  symm
  apply Fintype.sum_of_injective Pairing.padBottom (Pairing.map_injective (Fin.succOrderEmb n))
  · intro r hr
    simp only [localR_padBottom_outside a w p r hr,mul_zero]
  · intro r
    rw [localR_padBottom]

end

 

 

noncomputable section
namespace PartialColumn
variable {K : Type*} [CommRing K] {n : ℕ}

omit [CommRing K] in
lemma program_congr (w v : Fin n → Weights K) (k : ℕ) (hk : k≤n)
    (h : ∀ i : Fin n, i.val<k → w i=v i) : program w k hk=program v k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Program.snoc (program w k _) (position ⟨k,hk⟩) (w ⟨k,hk⟩)=
      Program.snoc (program v k _) (position ⟨k,hk⟩) (v ⟨k,hk⟩)
    rw [ih (by omega) (fun i hi => h i (by omega)),h ⟨k,hk⟩ (by simp)]

lemma program_commute (w : Fin n → Weights K) (k : ℕ) (hk : k≤n)
    (R : Matrix (Pairing (n+1)) (Pairing (n+1)) K)
    (h : ∀ i : Fin n, i.val<k → localR (position i) (w i)*R=R*localR (position i) (w i)) :
    (program w k hk).matrix*R=R*(program w k hk).matrix := by
  induction k with
  | zero => simp [program,Program.matrix]
  | succ k ih =>
    change (localR (position ⟨k,hk⟩) (w ⟨k,hk⟩)*(program w k _).matrix)*R=
      R*(localR (position ⟨k,hk⟩) (w ⟨k,hk⟩)*(program w k _).matrix)
    rw [Matrix.mul_assoc,ih (by omega) (fun i hi => h i (by omega)),
      ←Matrix.mul_assoc,h ⟨k,hk⟩ (by simp),Matrix.mul_assoc]

lemma exchange_program (w v : Fin n → Weights K) (r : ℕ) (hr : r+2≤n)
    (L R : Matrix (Pairing (n+1)) (Pairing (n+1)) K)
    (he : ∀ i : Fin n, i.val≠r → i.val≠r+1 → w i=v i)
    (hlow : ∀ i : Fin n, i.val<r → localR (position i) (w i)*R=R*localR (position i) (w i))
    (hhigh : ∀ i : Fin n, r + 1 < i.val → localR (position i) (w i)*L=L*localR (position i) (w i))
    (hyb : localR (position ⟨r+1,by omega⟩) (w ⟨r+1,by omega⟩) *
        localR (position ⟨r,by omega⟩) (w ⟨r,by omega⟩) * R =
      L * localR (position ⟨r+1,by omega⟩) (v ⟨r+1,by omega⟩) *
        localR (position ⟨r,by omega⟩) (v ⟨r,by omega⟩)) :
    (program w n le_rfl).matrix *R=L*(program v n le_rfl).matrix := by
  have hbase : (program w (r+2) hr).matrix*R=L*(program v (r+2) hr).matrix := by
    have hcomm := program_commute w r (by omega) R hlow
    have heq := program_congr w v r (by omega) (fun i hi => he i (by omega) (by omega))
    change (localR (position ⟨r+1,by omega⟩) (w ⟨r+1,by omega⟩) *
      (localR (position ⟨r,by omega⟩) (w ⟨r,by omega⟩) * (program w r _).matrix))*R =
      L*(localR (position ⟨r+1,by omega⟩) (v ⟨r+1,by omega⟩) *
      (localR (position ⟨r,by omega⟩) (v ⟨r,by omega⟩) * (program v r _).matrix))
    rw [Matrix.mul_assoc,Matrix.mul_assoc,hcomm,←Matrix.mul_assoc,
      ←Matrix.mul_assoc,hyb,heq]
    simp only [Matrix.mul_assoc]
  have hstep (k : ℕ) (hkr : r+2≤k) (hkn : k≤n) :
      (program w k hkn).matrix*R=L*(program v k hkn).matrix := by
    induction k,hkr using Nat.le_induction with
    | base => exact hbase
    | succ k hk ih =>
      have hk' : k<n := by omega
      change (localR (position ⟨k,hk'⟩) (w ⟨k,hk'⟩) * (program w k _).matrix)*R =
        L*(localR (position ⟨k,hk'⟩) (v ⟨k,hk'⟩)*(program v k _).matrix)
      rw [Matrix.mul_assoc,ih (by omega),←Matrix.mul_assoc,hhigh ⟨k,hk'⟩ (by dsimp; omega),
        he ⟨k,hk'⟩ (by dsimp; omega) (by dsimp; omega),Matrix.mul_assoc]
  exact hstep n hr le_rfl

end PartialColumn

 

 

open scoped Classical
namespace TriplePosition
variable {n m : ℕ} (s : TriplePosition n)

 

lemma coefficient_replacement {K : Type*} [CommRing K]
    (a b c d e f : Weights K) (p q : Pairing n)
    (h : ∀ k, s.exteriorPredicate p q k →
      ThreeBox.coefficient a.tile b.tile c.tile k =
        ThreeBox.coefficient d.tile e.tile f.tile (ThreeBox.mirrorIndex k)) :
    (localR s.right c * localR s.left b * localR s.right a) q p =
      (localR s.left f * localR s.right e * localR s.left d) q p := by
  rw [triple_expansion,triple_expansion_mirror]
  change (∑ t : ThreeBox.Config, if Circuit.eval p (s.rightCircuit t)=some q
    then a.tile t.1*b.tile t.2.1*c.tile t.2.2 else 0) =
    (∑ t : ThreeBox.Config, if Circuit.eval p (s.leftCircuit t)=some q
    then d.tile t.1*e.tile t.2.1*f.tile t.2.2 else 0)
  simp_rw [s.eval_profile_iff,s.mirror_eval_profile_iff,s.mirror_predicate]
  rw [ThreeBox.profile_partition,ThreeBox.profile_partition]
  let e' : Fin 51 ≃ Fin 51 := ⟨ThreeBox.mirrorIndex,ThreeBox.mirrorIndex,
    ThreeBox.mirrorIndex_involutive,ThreeBox.mirrorIndex_involutive⟩
  have he (k : Fin 51) : e' k = ThreeBox.mirrorIndex k := rfl
  refine Fintype.sum_equiv e' _ _ ?_
  intro k
  change (if s.exteriorPredicate p q k then _ else 0) =
    (if s.exteriorPredicate p q (ThreeBox.mirrorIndex (ThreeBox.mirrorIndex k)) then _ else 0)
  rw [ThreeBox.mirrorIndex_involutive]
  by_cases hk : s.exteriorPredicate p q k
  · simpa only [ite_eq_left hk, he] using h k hk
  · simp only [ite_eq_right hk]

 

theorem deletion (z : SpectralField m) (hz : z≠0) (hL : torusL z≠0)
    (hL3 : torusL (constF m phase^3*z)≠0) (p q : Pairing n)
    (hb : ¬p.Occupied s.b) (hc : ¬p.Occupied s.c) :
    (localR s.right (torusWeights z) * localR s.left (torusWeights (constF m phase^3*z)) *
        localR s.right deletionWeights : Matrix (Pairing n) (Pairing n) (SpectralField m)) q p =
      (localR s.left deletionWeights * localR s.right swapWeights *
        localR s.left swapWeights : Matrix (Pairing n) (Pairing n) (SpectralField m)) q p := by
  apply s.coefficient_replacement
  intro k hk
  apply ThreeBox.coefficient_deletion z hz hL hL3 k
  · intro hi; exact hb ((hk.2.1 1).mpr hi)
  · intro hi; exact hc ((hk.2.1 2).mpr hi)

 

theorem merge (z : SpectralField m) (hz : z≠0) (hL : torusL z≠0)
    (hL1 : torusL (constF m phase*z)≠0) (hL2 : torusL (constF m phase^2*z)≠0)
    (p q : Pairing n) (hc : ¬p.Occupied s.c) :
    (localR s.right (torusWeights z) * localR s.left (torusWeights (constF m phase^2*z)) *
        localR s.right (mergeWeights (constF m phase)) : Matrix (Pairing n) (Pairing n) (SpectralField m)) q p =
      (localR s.left (mergeWeights (constF m phase)) * localR s.right swapWeights *
        localR s.left (torusWeights (constF m phase*z)) : Matrix (Pairing n) (Pairing n) (SpectralField m)) q p := by
  apply s.coefficient_replacement
  intro k hk
  apply ThreeBox.coefficient_merge z hz hL hL1 hL2 k
  intro hi; exact hc ((hk.2.1 2).mpr hi)

end TriplePosition
end

 

 

noncomputable section
open scoped Classical
open Finset
namespace PartialColumn
variable {K : Type*} [CommRing K] {n : ℕ}

lemma program_zero_above (w : Fin n → Weights K) (k : ℕ) (hk : k≤n)
    (p q : Pairing (n+1)) (j : Fin (n+1)) (hj : k<j.val)
    (h : ¬ (q.Occupied j ↔ p.Occupied j)) : (program w k hk).matrix q p=0 := by
  induction k generalizing q with
  | zero =>
    change (1 : Matrix (Pairing (n+1)) (Pairing (n+1)) K) q p=0
    exact Matrix.one_apply_ne (fun he => h (he ▸ Iff.rfl))
  | succ k ih =>
    change (localR (position (n := n) ⟨k,hk⟩) (w ⟨k,hk⟩) * (program w k _).matrix) q p=0
    rw [Matrix.mul_apply]
    apply sum_eq_zero
    intro r _
    by_cases hr : q.Occupied j ↔ r.Occupied j
    · rw [ih (by omega) r (by omega) (fun hh => h (hr.trans hh)),mul_zero]
    · rw [localR_zero_of_support _ _ r q j (by intro he; have hh:=congrArg Fin.val he; change j.val=k at hh; omega)
        (by intro he; have hh:=congrArg Fin.val he; change j.val=k+1 at hh; omega) hr,zero_mul]

 

lemma exchange_program_column (w v : Fin n → Weights K) (r : ℕ) (hr : r+2≤n)
    (L R : Matrix (Pairing (n+1)) (Pairing (n+1)) K) (p : Pairing (n+1))
    (P : Pairing (n+1) → Prop)
    (hzero : ∀ t, ¬P t → (program w r (by omega)).matrix t p=0)
    (he : ∀ i : Fin n, i.val≠r → i.val≠r+1 → w i=v i)
    (hlow : ∀ i : Fin n, i.val<r → localR (position i) (w i)*R=R*localR (position i) (w i))
    (hhigh : ∀ i : Fin n, r + 1 < i.val → localR (position i) (w i)*L=L*localR (position i) (w i))
    (hyb : ∀ t, P t → ∀ q,
      (localR (position (n := n) ⟨r+1,by omega⟩) (w ⟨r+1,by omega⟩) *
        localR (position (n := n) ⟨r,by omega⟩) (w ⟨r,by omega⟩) * R) q t =
      (L * localR (position (n := n) ⟨r+1,by omega⟩) (v ⟨r+1,by omega⟩) *
        localR (position (n := n) ⟨r,by omega⟩) (v ⟨r,by omega⟩)) q t) :
    ∀ q, ((program w n le_rfl).matrix*R) q p = (L*(program v n le_rfl).matrix) q p := by
  have hbase (q : Pairing (n+1)) :
      ((program w (r+2) hr).matrix*R) q p = (L*(program v (r+2) hr).matrix) q p := by
    have hcomm := program_commute w r (by omega) R hlow
    have heq := program_congr w v r (by omega) (fun i hi => he i (by omega) (by omega))
    change ((localR (position (n := n) ⟨r+1,by omega⟩) (w ⟨r+1,by omega⟩) *
      (localR (position (n := n) ⟨r,by omega⟩) (w ⟨r,by omega⟩) * (program w r _).matrix))*R) q p =
      (L*(localR (position (n := n) ⟨r+1,by omega⟩) (v ⟨r+1,by omega⟩) *
      (localR (position (n := n) ⟨r,by omega⟩) (v ⟨r,by omega⟩) * (program v r _).matrix))) q p
    rw [Matrix.mul_assoc,Matrix.mul_assoc,hcomm,←Matrix.mul_assoc,←Matrix.mul_assoc]
    rw [←Matrix.mul_assoc L,←Matrix.mul_assoc,←heq]
    rw [Matrix.mul_apply, Matrix.mul_apply]
    apply sum_congr rfl
    intro t _
    by_cases ht : P t
    · rw [hyb t ht q]
    · rw [hzero t ht,mul_zero,mul_zero]
  have hstep (k : ℕ) (hkr : r+2≤k) (hkn : k≤n) :
      ∀ q, ((program w k hkn).matrix*R) q p=(L*(program v k hkn).matrix) q p := by
    induction k,hkr using Nat.le_induction with
    | base => exact hbase
    | succ k hk ih =>
      intro q
      have hk' : k<n := by omega
      change ((localR (position (n := n) ⟨k,hk'⟩) (w ⟨k,hk'⟩) * (program w k _).matrix)*R) q p =
        (L*(localR (position (n := n) ⟨k,hk'⟩) (v ⟨k,hk'⟩) * (program v k _).matrix)) q p
      rw [Matrix.mul_assoc]
      have hi : (localR (position (n := n) ⟨k,hk'⟩) (w ⟨k,hk'⟩) *
        ((program w k (by omega)).matrix*R)) q p =
        (localR (position (n := n) ⟨k,hk'⟩) (w ⟨k,hk'⟩) * (L*(program v k (by omega)).matrix)) q p := by
        rw [Matrix.mul_apply, Matrix.mul_apply]
        apply sum_congr rfl
        intro t _
        rw [ih (by omega) t]
      rw [hi,←Matrix.mul_assoc,hhigh ⟨k,hk'⟩ (by change r+1<k; omega),
        he ⟨k,hk'⟩ (by change k≠r; omega) (by change k≠r+1; omega),Matrix.mul_assoc]
  exact hstep n hr le_rfl

end PartialColumn
end

 

 

noncomputable section
open scoped Classical
namespace PartialColumn
variable {n m : ℕ}

def rowPosition (r : ℕ) (hr : r+2≤n) : Position n :=
  ⟨⟨r,by omega⟩,⟨r+1,by omega⟩,rfl⟩

def rowTriple (r : ℕ) (hr : r+2≤n) : TriplePosition (n+1) :=
  ⟨⟨r,by omega⟩,⟨r+1,by omega⟩,⟨r+2,by omega⟩,rfl,rfl⟩

lemma row_disjoint_low (r : ℕ) (hr : r+2≤n) (i : Fin n) (hi : i.val<r) :
    (position i).Disjoint (rowPosition r hr).padBottom := by
  have hid := i.isLt
  dsimp [Position.Disjoint,position,rowPosition,Position.padBottom]
  refine ⟨?_,?_,?_,?_⟩ <;> intro he <;> have hh:=congrArg Fin.val he <;> simp at hh <;> omega

lemma row_disjoint_high (r : ℕ) (hr : r+2≤n) (i : Fin n) (hi : r + 1 < i.val) :
    (position i).Disjoint (rowPosition r hr).padTop := by
  dsimp [Position.Disjoint,position,rowPosition,Position.padTop]
  refine ⟨?_,?_,?_,?_⟩ <;> intro he <;> have hh:=congrArg Fin.val he <;> simp at hh <;> omega

 

theorem torus_column_exchange (r : ℕ) (hr : r+2≤n) (x : Fin n → SpectralField m)
    (z : SpectralField m) (hz : z≠0) (hw : x ⟨r+1,by omega⟩≠0)
    (hLz : torusL z≠0) (hLw : torusL (x ⟨r+1,by omega⟩)≠0)
    (hLx : torusL (x ⟨r,by omega⟩)≠0)
    (hx : z*x ⟨r+1,by omega⟩=x ⟨r,by omega⟩) :
    column (fun i => torusWeights (x i)) * localR (rowPosition r hr) (torusWeights z) =
      localR (rowPosition r hr) (torusWeights z) *
        column (fun i => torusWeights (x (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩ i))) := by
  let w : Fin n → Weights (SpectralField m) := fun i => torusWeights (x i)
  let v : Fin n → Weights (SpectralField m) := fun i =>
    torusWeights (x (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩ i))
  have hyb : localR (position ⟨r+1,by omega⟩) (w ⟨r+1,by omega⟩) *
        localR (position ⟨r,by omega⟩) (w ⟨r,by omega⟩) *
        localR (rowPosition r hr).padBottom (torusWeights z) =
      localR (rowPosition r hr).padTop (torusWeights z) *
        localR (position ⟨r+1,by omega⟩) (v ⟨r+1,by omega⟩) *
        localR (position ⟨r,by omega⟩) (v ⟨r,by omega⟩) := by
    simpa only [w,v,Equiv.swap_apply_left,Equiv.swap_apply_right,hx,
      rowTriple,TriplePosition.left,TriplePosition.right,position,rowPosition,
      Position.padTop,Position.padBottom,Fin.castSucc_mk,Fin.succ_mk,Nat.add_assoc] using
      (rowTriple r hr).torus_yang_baxter z (x ⟨r+1,by omega⟩) hz hw hLz hLw (by rwa [hx])
  have he (i : Fin n) (hi : i.val≠r) (hj : i.val≠r+1) : w i=v i := by
    dsimp [w,v]
    rw [Equiv.swap_apply_of_ne_of_ne (fun he => hi (congrArg Fin.val he))
      (fun he => hj (congrArg Fin.val he))]
  have H := exchange_program w v r hr
    (localR (rowPosition r hr).padTop (torusWeights z))
    (localR (rowPosition r hr).padBottom (torusWeights z)) he
    (fun i hi => localR_commute _ _ (row_disjoint_low r hr i hi) _ _)
    (fun i hi => localR_commute _ _ (row_disjoint_high r hr i hi) _ _) hyb
  have hcw : (program w n le_rfl).matrix.submatrix Pairing.padTop Pairing.padBottom=column w := by
    ext q p
    exact program_column (by omega) w p q
  have hcv : (program v n le_rfl).matrix.submatrix Pairing.padTop Pairing.padBottom=column v := by
    ext q p
    exact program_column (by omega) v p q
  ext q p
  have HH:=congrArg (fun M => M q.padTop p.padBottom) H
  rw [localR_bottom_matrix,localR_top_matrix,hcw,hcv] at HH
  exact HH


 

 

lemma column_restricted_train {K : Type*} [CommRing K]
    (w v : Fin n → Weights K) (r : ℕ) (hr : r+2≤n) (a : Weights K)
    (p : Pairing n) (P : Pairing (n+1) → Prop)
    (hzero : ∀ t, ¬P t → (program w r (by omega)).matrix t p.padBottom=0)
    (he : ∀ i : Fin n, i.val≠r → i.val≠r+1 → w i=v i)
    (hyb : ∀ t, P t → ∀ q,
      (localR (position (n := n) ⟨r+1,by omega⟩) (w ⟨r+1,by omega⟩) *
        localR (position (n := n) ⟨r,by omega⟩) (w ⟨r,by omega⟩) *
        localR (rowPosition r hr).padBottom a) q t =
      (localR (rowPosition r hr).padTop a *
        localR (position (n := n) ⟨r+1,by omega⟩) (v ⟨r+1,by omega⟩) *
        localR (position (n := n) ⟨r,by omega⟩) (v ⟨r,by omega⟩)) q t) (q : Pairing n) :
    (column w * localR (rowPosition r hr) a) q p =
      (localR (rowPosition r hr) a * column v) q p := by
  have H := exchange_program_column w v r hr
    (localR (rowPosition r hr).padTop a) (localR (rowPosition r hr).padBottom a)
    p.padBottom P hzero he
    (fun i hi => localR_commute _ _ (row_disjoint_low r hr i hi) _ _)
    (fun i hi => localR_commute _ _ (row_disjoint_high r hr i hi) _ _) hyb q.padTop
  have hcw : (program w n le_rfl).matrix.submatrix Pairing.padTop Pairing.padBottom=column w := by
    ext q p; exact program_column (by omega) w p q
  have hcv : (program v n le_rfl).matrix.submatrix Pairing.padTop Pairing.padBottom=column v := by
    ext q p; exact program_column (by omega) v p q
  rw [localR_bottom_matrix,localR_top_matrix,hcw,hcv] at H
  exact H

 
theorem column_deletion (r : ℕ) (hr : r+2≤n)
    (w v : Fin n → Weights (SpectralField m)) (z : SpectralField m)
    (hz : z≠0) (hL : torusL z≠0) (hL3 : torusL (constF m phase^3*z)≠0)
    (hw₀ : w ⟨r,by omega⟩=torusWeights (constF m phase^3*z))
    (hw₁ : w ⟨r+1,by omega⟩=torusWeights z)
    (hv₀ : v ⟨r,by omega⟩=swapWeights) (hv₁ : v ⟨r+1,by omega⟩=swapWeights)
    (he : ∀ i : Fin n, i.val≠r → i.val≠r+1 → w i=v i)
    (p q : Pairing n) (hb : ¬p.Occupied ⟨r,by omega⟩)
    (hc : ¬p.Occupied ⟨r+1,by omega⟩) :
    ((column w * localR (rowPosition r hr) deletionWeights :
      Matrix (Pairing n) (Pairing n) (SpectralField m))) q p =
    ((localR (rowPosition r hr) deletionWeights * column v :
      Matrix (Pairing n) (Pairing n) (SpectralField m))) q p := by
  apply column_restricted_train w v r hr deletionWeights p
    (fun t => ¬t.Occupied ⟨r+1,by omega⟩ ∧ ¬t.Occupied ⟨r+2,by omega⟩) _ he _ q
  · intro t ht
    by_cases h₁ : t.Occupied ⟨r+1,by omega⟩
    · apply program_zero_above w r (by omega) p.padBottom t ⟨r+1,by omega⟩ (by simp)
      intro hh
      exact hb ((Pairing.padBottom_occupied_succ p ⟨r,by omega⟩).mp (hh.mp h₁))
    · have h₂ : t.Occupied ⟨r+2,by omega⟩ := Classical.not_not.mp (fun h₂ => ht ⟨h₁,h₂⟩)
      apply program_zero_above w r (by omega) p.padBottom t ⟨r+2,by omega⟩ (by simp)
      intro hh
      exact hc ((Pairing.padBottom_occupied_succ p ⟨r+1,by omega⟩).mp (hh.mp h₂))
  · intro t ht s
    rw [hw₀,hw₁,hv₀,hv₁]
    simpa only [rowTriple,TriplePosition.left,TriplePosition.right,position,rowPosition,
      Position.padTop,Position.padBottom,Fin.castSucc_mk,Fin.succ_mk,Nat.add_assoc]
      using (rowTriple r hr).deletion z hz hL hL3 t s ht.1 ht.2

 
theorem column_merge (r : ℕ) (hr : r+2≤n)
    (w v : Fin n → Weights (SpectralField m)) (z : SpectralField m)
    (hz : z≠0) (hL : torusL z≠0) (hL1 : torusL (constF m phase*z)≠0)
    (hL2 : torusL (constF m phase^2*z)≠0)
    (hw₀ : w ⟨r,by omega⟩=torusWeights (constF m phase^2*z))
    (hw₁ : w ⟨r+1,by omega⟩=torusWeights z)
    (hv₀ : v ⟨r,by omega⟩=torusWeights (constF m phase*z))
    (hv₁ : v ⟨r+1,by omega⟩=swapWeights)
    (he : ∀ i : Fin n, i.val≠r → i.val≠r+1 → w i=v i)
    (p q : Pairing n) (hc : ¬p.Occupied ⟨r+1,by omega⟩) :
    ((column w * localR (rowPosition r hr) (mergeWeights (constF m phase)) :
      Matrix (Pairing n) (Pairing n) (SpectralField m))) q p =
    ((localR (rowPosition r hr) (mergeWeights (constF m phase)) * column v :
      Matrix (Pairing n) (Pairing n) (SpectralField m))) q p := by
  apply column_restricted_train w v r hr (mergeWeights (constF m phase)) p
    (fun t => ¬t.Occupied ⟨r+2,by omega⟩) _ he _ q
  · intro t ht
    apply program_zero_above w r (by omega) p.padBottom t ⟨r+2,by omega⟩ (by simp)
    intro hh
    exact hc ((Pairing.padBottom_occupied_succ p ⟨r+1,by omega⟩).mp (hh.mp (Classical.not_not.mp ht)))
  · intro t ht s
    rw [hw₀,hw₁,hv₀,hv₁]
    simpa only [rowTriple,TriplePosition.left,TriplePosition.right,position,rowPosition,
      Position.padTop,Position.padBottom,Fin.castSucc_mk,Fin.succ_mk,Nat.add_assoc]
      using (rowTriple r hr).merge z hz hL hL1 hL2 t s ht

end PartialColumn
end

 

 

noncomputable section
open scoped Classical
open Finset

variable {K : Type*} [CommRing K]

def functionMatrix {P Q : Type*} (f : P → Q) : Matrix Q P K := optionMatrix (some ∘ f)

lemma functionMatrix_mul {P Q R : Type*} [Fintype Q] (f : P → Q) (g : Q → R) :
    (functionMatrix (K := K) g : Matrix R Q K) * functionMatrix (K := K) f = functionMatrix (g ∘ f) := by
  exact optionMatrix_mul (some ∘ f) (some ∘ g)

lemma mul_functionMatrix {P Q R : Type*} [Fintype Q] (f : P → Q) (M : Matrix R Q K)
    (r : R) (p : P) : (M * functionMatrix (K := K) f) r p = M r (f p) := by
  simp only [Matrix.mul_apply,functionMatrix,optionMatrix,Function.comp_apply,Option.some.injEq]
  rw [sum_eq_single (f p)]
  · simp
  · intro q _ hq; simp [Ne.symm hq]
  · simp

lemma functionMatrix_mul_apply {P Q R : Type*} [Fintype P] (f : P → Q)
    (hf : Function.Injective f) (M : Matrix P R K) (p : P) (r : R) :
    (functionMatrix (K := K) f * M) (f p) r = M p r := by
  simp only [Matrix.mul_apply,functionMatrix,optionMatrix,Function.comp_apply,Option.some.injEq,
    hf.eq_iff]
  rw [sum_eq_single p]
  · simp
  · intro q _ hq; simp [hq]
  · simp

lemma functionMatrix_mul_outside {P Q R : Type*} [Fintype P] (f : P → Q)
    (M : Matrix P R K) (q : Q) (r : R) (h : ¬ ∃ p, f p=q) :
    (functionMatrix (K := K) f * M) q r=0 := by
  simp only [Matrix.mul_apply,functionMatrix,optionMatrix,Function.comp_apply,Option.some.injEq]
  apply sum_eq_zero
  intro p _
  rw [ite_eq_right (fun he => h ⟨p,he⟩),zero_mul]

lemma optionMatrix_natural {P Q : Type*} [Fintype P] [Fintype Q]
    (f : P → Q) (a : P → Option P) (b : Q → Option Q)
    (h : ∀ p, b (f p)=(a p).map f) :
    (optionMatrix b : Matrix Q Q K) * functionMatrix (K := K) f = functionMatrix (K := K) f * optionMatrix a := by
  calc
    _ = optionMatrix (fun p => ((some ∘ f) p).bind b) :=
      optionMatrix_mul (some ∘ f) b
    _ = optionMatrix (fun p => (a p).bind (some ∘ f)) := by
      congr 1
      funext p
      simp only [Function.comp_apply, Option.bind_some]
      rw [h p]
      cases a p <;> rfl
    _ = _ := (optionMatrix_mul a (some ∘ f)).symm

lemma localR_natural {n m : ℕ} (f : Fin n ↪o Fin m)
    (a : Position n) (b : Position m) (ha : f a.left=b.left) (hb : f a.right=b.right)
    (w : Weights K) :
    localR b w * functionMatrix (K := K) (Pairing.map f) = functionMatrix (K := K) (Pairing.map f) * localR a w := by
  simp only [localR,Matrix.sum_mul,Matrix.mul_sum,Matrix.smul_mul,Matrix.mul_smul]
  apply sum_congr rfl
  intro t _
  congr 1
  apply optionMatrix_natural
  intro p
  simpa only [ha,hb] using p.map_tileStep f a.left a.right a.adjacent (by rw [ha,hb]; exact b.adjacent) t

end
end CriticalStrip.Diagram

 

 

namespace Fin
open scoped _root_.Fin
lemma swap_succAbove_adjacent {n : ℕ} (a b : Fin (n+1)) (hab : a.val+1=b.val)
    (i : Fin n) : Equiv.swap a b (b.succAbove i)=a.succAbove i := by
  by_cases hi : i.val<a.val
  · have hia : i.castSucc≠a := by intro he; have:=congrArg Fin.val he; simp at this; omega
    have hib : i.castSucc≠b := by intro he; have:=congrArg Fin.val he; simp at this; omega
    simp only [Fin.succAbove, show i.castSucc<a from hi, show i.castSucc<b from (by change i.val<b.val; omega),
      ite_true,Equiv.swap_apply_of_ne_of_ne hia hib]
  · by_cases he : i.val=a.val
    · have ha : i.castSucc=a := Fin.ext he
      have hb : i.succ=b := Fin.ext (by simp only [Fin.val_succ]; omega)
      simp only [Fin.succAbove,ha,lt_self_iff_false,ite_false,hb,
        show a<b from (by change a.val<b.val; omega),ite_true,Equiv.swap_apply_left]
    · have hia : i.succ≠a := by intro hh; have:=congrArg Fin.val hh; simp at this; omega
      have hib : i.succ≠b := by intro hh; have:=congrArg Fin.val hh; simp at this; omega
      simp only [Fin.succAbove,show ¬i.castSucc<a from hi,
        show ¬i.castSucc<b from (by change ¬i.val<b.val; omega),ite_false,
        Equiv.swap_apply_of_ne_of_ne hia hib]
end Fin

end OAI
