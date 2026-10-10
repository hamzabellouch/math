import Mathlib
import OAI.Probability.Contingency.ResidualMargins

namespace OAI

/-! Completion Translation. -/

noncomputable section

open scoped BigOperators
open scoped BigOperators
namespace Contingency.CompletionTranslation
variable {m n : ℕ}

 
def adjustment (i₀ : Fin m) (j₀ : Fin n) (R : Fin m → ℤ) (P : Fin n → ℤ) :
    Fin m → Fin n → ℤ := fun i j =>
  if i=i₀ then
    if j=j₀ then R i₀-∑ j ∈ Finset.univ.erase j₀, P j else P j
  else if j=j₀ then R i else 0

@[simp] theorem adjustment_row (i₀ : Fin m) (j₀ : Fin n) (R : Fin m → ℤ) (P : Fin n → ℤ)
    (i : Fin m) : (∑ j, adjustment i₀ j₀ R P i j)=R i := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j₀)]
  by_cases hi : i=i₀
  · subst i
    simp only [adjustment,ite_true]
    have he : (∑ j ∈ Finset.univ.erase j₀, if j=j₀ then R i₀-∑ j ∈ Finset.univ.erase j₀,P j else P j)=
        ∑ j ∈ Finset.univ.erase j₀,P j := by
      apply Finset.sum_congr rfl; intro j hj
      rw [ite_eq_right (Finset.mem_erase.mp hj).1]
    rw [he]; ring
  · simp only [adjustment,ite_eq_right hi,ite_true]
    have he : (∑ j ∈ Finset.univ.erase j₀, if j=j₀ then R i else 0)=0 := by
      apply Finset.sum_eq_zero; intro j hj
      rw [ite_eq_right (Finset.mem_erase.mp hj).1]
    rw [he]; ring

@[simp] theorem adjustment_col (i₀ : Fin m) (j₀ : Fin n) (R : Fin m → ℤ) (P : Fin n → ℤ)
    (heq : (∑ i,R i)=∑ j,P j) (j : Fin n) : (∑ i,adjustment i₀ j₀ R P i j)=P j := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i₀)]
  have he : (∑ i ∈ Finset.univ.erase i₀, adjustment i₀ j₀ R P i j)=
      ∑ i ∈ Finset.univ.erase i₀, if j=j₀ then R i else 0 := by
    apply Finset.sum_congr rfl; intro i hi
    rw [adjustment,ite_eq_right (Finset.mem_erase.mp hi).1]
  rw [he]
  by_cases hj : j=j₀
  · subst j
    simp only [adjustment,ite_true]
    have hR := Finset.sum_erase_add Finset.univ R (Finset.mem_univ i₀)
    have hP := Finset.sum_erase_add Finset.univ P (Finset.mem_univ j₀)
    omega
  · simp [adjustment,hj]

@[simp] theorem adjustment_neg (i₀ : Fin m) (j₀ : Fin n) (R : Fin m → ℤ) (P : Fin n → ℤ)
    (i : Fin m) (j : Fin n) :
    adjustment i₀ j₀ (fun i => -R i) (fun j => -P j) i j = -adjustment i₀ j₀ R P i j := by
  simp only [adjustment,Finset.sum_neg_distrib]
  split_ifs <;> ring

 

def Accepted (r : Fin m → ℕ) (c : Fin n → ℕ) (D : Fin m → Fin n → ℤ) :=
  {X : Tables r c // ∀ i j, 0≤(X.val i j:ℤ)+D i j}

instance (r : Fin m → ℕ) (c : Fin n → ℕ) (D : Fin m → Fin n → ℤ) : Finite (Accepted r c D) :=
  inferInstanceAs (Finite {X : Tables r c // ∀ i j, 0≤(X.val i j:ℤ)+D i j})

noncomputable def translate (r r' : Fin m → ℕ) (c c' : Fin n → ℕ)
    (D : Fin m → Fin n → ℤ)
    (hR : ∀ i, ∑ j,D i j=(r' i:ℤ)-r i) (hP : ∀ j,∑ i,D i j=(c' j:ℤ)-c j)
    (X : Accepted r c D) : Accepted r' c' (fun i j => -D i j) := by
  let Y := fun i j => ((X.val.val i j:ℤ)+D i j).toNat
  have hY (i j) : (Y i j:ℤ)=(X.val.val i j:ℤ)+D i j := Int.toNat_of_nonneg (X.property i j)
  refine ⟨⟨Y,?_,?_⟩,?_⟩
  · intro i
    apply Int.ofNat_inj.mp
    simp only [Nat.cast_sum,hY,Finset.sum_add_distrib,hR]
    have hh := X.val.property.1 i
    have hh' : (∑ j,(X.val.val i j:ℤ))=(r i:ℤ) := by exact_mod_cast hh
    rw [hh']; ring
  · intro j
    apply Int.ofNat_inj.mp
    simp only [Nat.cast_sum,hY,Finset.sum_add_distrib,hP]
    have hh := X.val.property.2 j
    have hh' : (∑ i,(X.val.val i j:ℤ))=(c j:ℤ) := by exact_mod_cast hh
    rw [hh']; ring
  · intro i j
    change 0≤(Y i j:ℤ)+(-D i j)
    rw [hY]; omega

@[simp] theorem translate_value (r r' : Fin m → ℕ) (c c' : Fin n → ℕ)
    (D : Fin m → Fin n → ℤ)
    (hR : ∀ i, ∑ j,D i j=(r' i:ℤ)-r i) (hP : ∀ j,∑ i,D i j=(c' j:ℤ)-c j)
    (X : Accepted r c D) (i j) :
    ((translate r r' c c' D hR hP X).val.val i j:ℤ)=(X.val.val i j:ℤ)+D i j :=
  Int.toNat_of_nonneg (X.property i j)

noncomputable def translationEquiv (r r' : Fin m → ℕ) (c c' : Fin n → ℕ)
    (D : Fin m → Fin n → ℤ)
    (hR : ∀ i, ∑ j,D i j=(r' i:ℤ)-r i) (hP : ∀ j,∑ i,D i j=(c' j:ℤ)-c j) :
    Accepted r c D ≃ Accepted r' c' (fun i j => -D i j) := by
  have hnR : ∀ i,∑ j,-D i j=(r i:ℤ)-r' i := by
    intro i; rw [Finset.sum_neg_distrib,hR]; ring
  have hnP : ∀ j,∑ i,-D i j=(c j:ℤ)-c' j := by
    intro j; rw [Finset.sum_neg_distrib,hP]; ring
  let inv : Accepted r' c' (fun i j => -D i j) → Accepted r c D := fun Y =>
    ⟨(translate r' r c' c (fun i j => -D i j) hnR hnP Y).val,by
      intro i j
      simp⟩
  refine ⟨translate r r' c c' D hR hP,inv,?_,?_⟩
  · intro X
    apply Subtype.ext; apply Subtype.ext
    funext i j; apply Int.ofNat_inj.mp
    change ((translate r' r c' c _ hnR hnP (translate r r' c c' D hR hP X)).val.val i j:ℤ)=_
    rw [translate_value,translate_value]; ring
  · intro Y
    apply Subtype.ext; apply Subtype.ext
    funext i j; apply Int.ofNat_inj.mp
    rw [translate_value]
    change ((translate r' r c' c _ hnR hnP Y).val.val i j:ℤ)+D i j=(Y.val.val i j:ℤ)
    rw [translate_value]; ring

 
theorem accepted_card_symm (r r' : Fin m → ℕ) (c c' : Fin n → ℕ)
    (D : Fin m → Fin n → ℤ)
    (hR : ∀ i, ∑ j,D i j=(r' i:ℤ)-r i) (hP : ∀ j,∑ i,D i j=(c' j:ℤ)-c j) :
    Nat.card (Accepted r c D)=Nat.card (Accepted r' c' (fun i j => -D i j)) :=
  Nat.card_congr (translationEquiv r r' c c' D hR hP)

 

def Rejected (r : Fin m → ℕ) (c : Fin n → ℕ) (D : Fin m → Fin n → ℤ) :=
  {X : Tables r c // ¬∀ i j, 0≤(X.val i j:ℤ)+D i j}

theorem rejection_union_count (r : Fin m → ℕ) (c : Fin n → ℕ)
    (D : Fin m → Fin n → ℤ) (t : ℕ) (hD : ∀ i j, -(t:ℤ)≤D i j) :
    Nat.card (Rejected r c D) ≤ ∑ s : Cell m n, Nat.card (SmallEntryBad r c s.1 s.2 t) := by
  classical
  have hb (X : Rejected r c D) : ∃ s : Cell m n, X.val.val s.1 s.2<t := by
    have h := X.property
    push Not at h
    obtain ⟨i,j,h⟩ := h
    exact ⟨(i,j),by change X.val.val i j<t; have := hD i j; omega⟩
  let F : Rejected r c D → Σ s : Cell m n, SmallEntryBad r c s.1 s.2 t :=
    fun X => ⟨(hb X).choose,⟨X.val,(hb X).choose_spec⟩⟩
  have hi : Function.Injective F := by
    intro X Y he
    apply Subtype.ext
    exact congrArg (fun z : Σ s : Cell m n, SmallEntryBad r c s.1 s.2 t => z.2.val) he
  have hh := Nat.card_le_card_of_injective F hi
  rw [Nat.card_sigma] at hh
  exact hh

theorem rejection_count (d a t : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (D : Fin m → Fin n → ℤ) (hd : 1≤d) (hm : m≤d) (hn : n≤d)
    (ha : 4*d≤a) (hr : ∀ i,a≤r i) (hc : ∀ j,a≤c j) (ht : 2*t≤a)
    (hD : ∀ i j, -(t:ℤ)≤D i j) :
    Nat.card (Rejected r c D)*a ≤ 4*t*d^3*(m*n)*Nat.card (Tables r c) := by
  have hu := Nat.mul_le_mul_right a (rejection_union_count r c D t hD)
  have hh : (∑ s : Cell m n, Nat.card (SmallEntryBad r c s.1 s.2 t))*a ≤
      ∑ s : Cell m n, 4*t*d^3*Nat.card (Tables r c) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro s _
    exact small_entry_count d a t r c s.1 s.2 hd hm hn ha (hr s.1) (hc s.2) ht
  have he : (∑ s : Cell m n, 4*t*d^3*Nat.card (Tables r c))=
      4*t*d^3*(m*n)*Nat.card (Tables r c) := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
    ring
  exact hu.trans (he ▸ hh)

theorem accepted_rejected_count (r : Fin m → ℕ) (c : Fin n → ℕ) (D : Fin m → Fin n → ℤ) :
    Nat.card (Accepted r c D)+Nat.card (Rejected r c D)=Nat.card (Tables r c) := by
  classical
  have hh := Nat.card_congr (Equiv.sumCompl (fun X : Tables r c => ∀ i j,0≤(X.val i j:ℤ)+D i j))
  rw [Nat.card_sum] at hh
  exact hh

 

theorem accepted_half (d : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (D : Fin m → Fin n → ℤ) (hd : 14≤d) (hm : m≤d) (hn : n≤d) (hmn : m*n≤d)
    (hr : ∀ i,d^12≤r i) (hc : ∀ j,d^12≤c j)
    (hD : ∀ i j, -(10*(d:ℤ))≤D i j) :
    Nat.card (Tables r c) ≤ 2*Nat.card (Accepted r c D) := by
  have hd1 : 1≤d := by omega
  have hd7 : 80≤d^7 := by
    calc
      80 ≤ 14^7 := by norm_num
      _ ≤ d^7 := Nat.pow_le_pow_left hd _
  have hd5 : 1≤d^5 := one_le_pow₀ hd1
  have hd11 : 80≤d^11 := by
    calc
      80 ≤ 14^11 := by norm_num
      _ ≤ d^11 := Nat.pow_le_pow_left hd _
  have he12 : d^12=d*d^11 := by ring
  have h4 : 4*d≤d^12 := by nlinarith only [hd11,he12]
  have ht : 2*(10*d)≤d^12 := by nlinarith only [hd11,he12]
  have hD' : ∀ i j, -((10*d:ℕ):ℤ)≤D i j := by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hD
  have hh := rejection_count d (d^12) (10*d) r c D hd1 hm hn h4 hr hc ht hD'
  have hhalf : 2*(4*(10*d)*d^3*(m*n))≤d^12 := by
    calc
      _ ≤ 80*d^5 := by nlinarith only [Nat.mul_le_mul_left (40*d^4) hmn]
      _ ≤ d^12 := by
        have := Nat.mul_le_mul_left (d^5) hd7
        nlinarith only [this,show d^12=d^5*d^7 by ring]
  have hwhole := accepted_rejected_count r c D
  have hc' := Nat.mul_le_mul_right (Nat.card (Tables r c)) hhalf
  have hb : 2*Nat.card (Rejected r c D)≤Nat.card (Tables r c) := by
    by_contra h
    have hpos : 0<d^12 := pow_pos (by omega) _
    have hgt := Nat.mul_lt_mul_of_pos_right (show Nat.card (Tables r c)<2*Nat.card (Rejected r c D) by omega) hpos
    nlinarith only [hh,hc',hgt]
  omega

end Contingency.CompletionTranslation

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
variable {m n a b : ℕ} (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (er : Fin a ≃ {i // U≤r i}) (ec : Fin b ≃ {j // U≤c j})

def blockRow (X : GraphState U r c) (i : Fin a) : ℕ :=
  rowNat U L r c (graphUnderlying U r c X) (er i).val

def blockCol (X : GraphState U r c) (j : Fin b) : ℕ :=
  colNat U L r c (graphUnderlying U r c X) (ec j).val

def blockEquiv (X : GraphState U r c) :
    Completion U L r c (graphUnderlying U r c X) ≃
      Tables (blockRow U L r c er X) (blockCol U L r c ec X) :=
  (completionTableEquiv U L r c _ (graph_feasible U r c X)).trans
    (restrictTableEquiv (fun i => U≤r i) (fun j => U≤c j) er ec
      (fun i hi => by
        unfold rowNat
        rw [residualRow_zero U L r c _ (graph_feasible U r c X) i (by omega)]
        rfl)
      (fun j hj => by
        unfold colNat
        rw [residualCol_zero U L r c _ (graph_feasible U r c X) j (by omega)]
        rfl))

theorem block_totals (X : GraphState U r c) (h : (∑ i,r i)=∑ j,c j) :
    (∑ i,blockRow U L r c er X i)=∑ j,blockCol U L r c ec X j := by
  obtain ⟨A⟩ := completion_nonempty U L r c X h
  let B := blockEquiv U L r c er ec X A
  calc
    _ = ∑ i,∑ j,B.val i j := by simp only [B.property.1]
    _ = ∑ j,∑ i,B.val i j := Finset.sum_comm
    _ = _ := by simp only [B.property.2]

include ec in
theorem block_row_lower (X : GraphState U r c) (i : Fin a) (j : Fin b) :
    L≤blockRow U L r c er X i := by
  have hf := graph_feasible U r c X
  have hh := (hf.2.2.1 (er i).val).1
  have hp : (L:ℤ)≤rowPadding U L r c (er i).val := by
    unfold rowPadding
    have he : IsLarge U r c ((er i).val,(ec j).val) := ⟨(er i).property,(ec j).property⟩
    have h := Finset.single_le_sum (f:=fun j => if IsLarge U r c ((er i).val,j) then (L:ℤ) else 0)
      (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ (ec j).val)
    simpa only [ite_eq_left he] using h
  apply Int.ofNat_le.mp
  change (L:ℤ)≤(rowNat U L r c _ _ :ℤ)
  rw [rowNat_cast U L r c _ hf]
  dsimp [residualRow]; omega

include er in
theorem block_col_lower (X : GraphState U r c) (i : Fin a) (j : Fin b) :
    L≤blockCol U L r c ec X j := by
  have hf := graph_feasible U r c X
  have hh := (hf.2.2.2 (ec j).val).1
  have hp : (L:ℤ)≤colPadding U L r c (ec j).val := by
    unfold colPadding
    have he : IsLarge U r c ((er i).val,(ec j).val) := ⟨(er i).property,(ec j).property⟩
    have h := Finset.single_le_sum (f:=fun i => if IsLarge U r c (i,(ec j).val) then (L:ℤ) else 0)
      (fun i _ => by split_ifs <;> positivity) (Finset.mem_univ (er i).val)
    simpa only [ite_eq_left he] using h
  apply Int.ofNat_le.mp
  change (L:ℤ)≤(colNat U L r c _ _ :ℤ)
  rw [colNat_cast U L r c _ hf]
  dsimp [residualCol]; omega

include er ec in
theorem block_dimensions : a ≤ m ∧ b ≤ n := by
  constructor
  · have h := Fintype.card_le_of_injective (fun i : Fin a => (er i).val)
      (Subtype.val_injective.comp er.injective)
    simpa using h
  · have h := Fintype.card_le_of_injective (fun j : Fin b => (ec j).val)
      (Subtype.val_injective.comp ec.injective)
    simpa using h

theorem block_movement (X Y : GraphState U r c) (h : GraphAdj U r c X Y) :
    (∀ i,|(blockRow U L r c er Y i:ℤ)-blockRow U L r c er X i|≤2) ∧
    (∀ j,|(blockCol U L r c ec Y j:ℤ)-blockCol U L r c ec X j|≤2) := by
  have hh := graph_margin_movement U L r c X Y h
  constructor
  · intro i
    simpa only [blockRow,rowNat_cast U L r c _ (graph_feasible U r c Y),
      rowNat_cast U L r c _ (graph_feasible U r c X)] using hh.1 (er i).val
  · intro j
    simpa only [blockCol,colNat_cast U L r c _ (graph_feasible U r c Y),
      colNat_cast U L r c _ (graph_feasible U r c X)] using hh.2 (ec j).val

end
end Contingency.PaddedGraph

namespace Contingency.CompletionTranslation
variable {m n : ℕ}

theorem adjustment_bound (d : ℕ) (hd : 1≤d) (hn : n≤d)
    (i₀ : Fin m) (j₀ : Fin n) (R : Fin m → ℤ) (P : Fin n → ℤ)
    (hR : ∀ i,|R i|≤2) (hP : ∀ j,|P j|≤2) (i : Fin m) (j : Fin n) :
    |adjustment i₀ j₀ R P i j|≤10*(d:ℤ) := by
  have hd' : (1:ℤ)≤d := by exact_mod_cast hd
  have hb : |∑ j ∈ Finset.univ.erase j₀,P j|≤2*(d:ℤ) := by
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase j₀,|P j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.univ.erase j₀,(2:ℤ) := Finset.sum_le_sum (fun j _ => hP j)
      _ ≤ 2*(d:ℤ) := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        have hh : (Finset.univ.erase j₀).card≤d :=
          (Finset.card_le_card (Finset.erase_subset _ _)).trans (by simpa using hn)
        exact_mod_cast (by omega : (Finset.univ.erase j₀).card*2≤2*d)
  unfold adjustment
  split_ifs
  · exact (abs_sub _ _).trans (by linarith [hR i₀])
  · linarith [hP j]
  · linarith [hR i]
  · simp
end Contingency.CompletionTranslation

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
open CompletionTranslation
variable {m n a b : ℕ} (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (er : Fin a ≃ {i // U≤r i}) (ec : Fin b ≃ {j // U≤c j})
    (i₀ : Fin a) (j₀ : Fin b)

def blockD (X Y : GraphState U r c) : Fin a → Fin b → ℤ :=
  adjustment i₀ j₀
    (fun i => (blockRow U L r c er Y i:ℤ)-blockRow U L r c er X i)
    (fun j => (blockCol U L r c ec Y j:ℤ)-blockCol U L r c ec X j)

theorem blockD_row (X Y : GraphState U r c) (i : Fin a) :
    (∑ j,blockD U L r c er ec i₀ j₀ X Y i j)=
      (blockRow U L r c er Y i:ℤ)-blockRow U L r c er X i :=
  adjustment_row _ _ _ _ _

theorem blockD_col (X Y : GraphState U r c) (hrc : (∑ i,r i)=∑ j,c j) (j : Fin b) :
    (∑ i,blockD U L r c er ec i₀ j₀ X Y i j)=
      (blockCol U L r c ec Y j:ℤ)-blockCol U L r c ec X j := by
  apply adjustment_col
  simp only [Finset.sum_sub_distrib,← Nat.cast_sum,block_totals U L r c er ec _ hrc]

theorem blockD_reverse (X Y : GraphState U r c) :
    blockD U L r c er ec i₀ j₀ Y X=fun i j => -blockD U L r c er ec i₀ j₀ X Y i j := by
  have heR : (fun i => (blockRow U L r c er X i:ℤ)-blockRow U L r c er Y i)=
      (fun i => -((blockRow U L r c er Y i:ℤ)-blockRow U L r c er X i)) := by funext i; ring
  have heP : (fun j => (blockCol U L r c ec X j:ℤ)-blockCol U L r c ec Y j)=
      (fun j => -((blockCol U L r c ec Y j:ℤ)-blockCol U L r c ec X j)) := by funext j; ring
  funext i j
  simp only [blockD,heR,heP,adjustment_neg]

def acceptCount (X Y : GraphState U r c) : ℕ :=
  Nat.card (Accepted (blockRow U L r c er X) (blockCol U L r c ec X)
    (blockD U L r c er ec i₀ j₀ X Y))

theorem acceptCount_symm (X Y : GraphState U r c) (hrc : (∑ i,r i)=∑ j,c j) :
    acceptCount U L r c er ec i₀ j₀ X Y=acceptCount U L r c er ec i₀ j₀ Y X := by
  unfold acceptCount
  rw [blockD_reverse U L r c er ec i₀ j₀ X Y]
  exact accepted_card_symm _ _ _ _ _ (blockD_row U L r c er ec i₀ j₀ X Y)
    (blockD_col U L r c er ec i₀ j₀ X Y hrc)

theorem block_card (X : GraphState U r c) :
    Nat.card (Tables (blockRow U L r c er X) (blockCol U L r c ec X))=
      weight U L r c (graphUnderlying U r c X) := by
  rw [weight,ite_eq_left (graph_feasible U r c X)]
  exact (Nat.card_congr (blockEquiv U L r c er ec X)).symm

theorem acceptCount_le (X Y : GraphState U r c) :
    acceptCount U L r c er ec i₀ j₀ X Y≤weight U L r c (graphUnderlying U r c X) := by
  rw [← block_card U L r c er ec X]
  exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

theorem acceptCount_half (d : ℕ) (hd : 14≤d) (hm : m ≤ d) (hn : n ≤ d) (hmn : m*n≤d)
    (X Y : GraphState U r c) (h : GraphAdj U r c X Y) :
    weight U (d^12) r c (graphUnderlying U r c X)≤2*acceptCount U (d^12) r c er ec i₀ j₀ X Y := by
  rw [← block_card U (d^12) r c er ec X]
  have hdim := block_dimensions U r c er ec
  apply accepted_half d _ _ _ hd (hdim.1.trans hm) (hdim.2.trans hn)
    ((Nat.mul_le_mul hdim.1 hdim.2).trans hmn)
    (fun i => block_row_lower U (d^12) r c er ec X i j₀)
    (fun j => block_col_lower U (d^12) r c er ec X i₀ j)
  intro i j
  have hh := block_movement U (d^12) r c er ec X Y h
  have hb := adjustment_bound d (by omega) (hdim.2.trans hn) i₀ j₀ _ _ hh.1 hh.2 i j
  exact (abs_le.mp hb).1

end
end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
open CompletionTranslation FiniteChain
variable {m n a b : ℕ} (U L d : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (er : Fin a ≃ {i // U≤r i}) (ec : Fin b ≃ {j // U≤c j})
    (i₀ : Fin a) (j₀ : Fin b)

def edgeCount (X Y : GraphState U r c) : ℝ :=
  if GraphAdj U r c X Y then (acceptCount U L r c er ec i₀ j₀ X Y:ℝ) else 0

theorem edgeCount_nonneg (X Y : GraphState U r c) : 0≤edgeCount U L r c er ec i₀ j₀ X Y := by
  unfold edgeCount; split_ifs <;> positivity

theorem edgeCount_symm (hrc : (∑ i,r i)=∑ j,c j) (X Y : GraphState U r c) :
    edgeCount U L r c er ec i₀ j₀ X Y=edgeCount U L r c er ec i₀ j₀ Y X := by
  unfold edgeCount
  have he : GraphAdj U r c X Y ↔ GraphAdj U r c Y X := ⟨GraphAdj.symm U r c,GraphAdj.symm U r c⟩
  simp only [he,acceptCount_symm U L r c er ec i₀ j₀ X Y hrc]

theorem edgeCount_diagonal (X : GraphState U r c) : edgeCount U L r c er ec i₀ j₀ X X=0 := by
  simp [edgeCount,GraphAdj.irrefl]

theorem edgeCount_sum (hmn : m*n≤d) (X : GraphState U r c) :
    (∑ Y,edgeCount U L r c er ec i₀ j₀ X Y)≤
      (5*(d:ℝ)^2+1)*weight U L r c (graphUnderlying U r c X) := by
  simp only [edgeCount,← Finset.sum_filter]
  calc
    _ ≤ ∑ Y ∈ Finset.univ.filter (GraphAdj U r c X),
        (weight U L r c (graphUnderlying U r c X):ℝ) := by
      apply Finset.sum_le_sum; intro Y _
      exact_mod_cast acceptCount_le U L r c er ec i₀ j₀ X Y
    _ = ((Finset.univ.filter (GraphAdj U r c X)).card:ℝ)*weight U L r c (graphUnderlying U r c X) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast graph_degree U r c d hmn X

theorem proposal_hold (hd : 1≤d) : proposalRate (32*d^2)*(5*(d:ℝ)^2+1)≤1/2 := by
  have hb := (smallProposal_bounds d hd).2
  have hd' : (1:ℝ)≤d := by exact_mod_cast hd
  have hd2 : (1:ℝ)≤(d:ℝ)^2 := one_le_pow₀ hd'
  calc
    _ ≤ (1/(32*(d:ℝ)^2))*(5*(d:ℝ)^2+1) := mul_le_mul_of_nonneg_right hb (by positivity)
    _ ≤ 1/2 := by
      rw [one_div_mul_eq_div]
      apply (div_le_iff₀ (by positivity : 0<32*(d:ℝ)^2)).mpr
      nlinarith

def smallData (hrc : (∑ i,r i)=∑ j,c j) (hd : 1≤d) (hmn : m*n≤d) : AcceptedData (GraphState U r c) where
  f X := weight U L r c (graphUnderlying U r c X)
  fpos X := by exact_mod_cast graph_weight_pos U L r c X hrc
  count := edgeCount U L r c er ec i₀ j₀
  nonneg := edgeCount_nonneg U L r c er ec i₀ j₀
  symmetric := edgeCount_symm U L r c er ec i₀ j₀ hrc
  diagonal := edgeCount_diagonal U L r c er ec i₀ j₀
  q := proposalRate (32*d^2)
  qpos := by unfold proposalRate; positivity
  hold X := by
    have hq : 0≤proposalRate (32*d^2) := by unfold proposalRate; positivity
    have hh := mul_le_mul_of_nonneg_left (edgeCount_sum U L d r c er ec i₀ j₀ hmn X) hq
    calc
      _ ≤ proposalRate (32*d^2)*((5*(d:ℝ)^2+1)*weight U L r c (graphUnderlying U r c X)) := hh
      _ = (proposalRate (32*d^2)*(5*(d:ℝ)^2+1))*weight U L r c (graphUnderlying U r c X) := by ring
      _ ≤ (1/2)*weight U L r c (graphUnderlying U r c X) :=
        mul_le_mul_of_nonneg_right (proposal_hold d hd) (by positivity)
      _ = _ := by ring

variable [Nonempty (GraphState U r c)]

theorem small_transition_lower (hrc : (∑ i,r i)=∑ j,c j)
    (hd : 14≤d) (hm : m ≤ d) (hn : n ≤ d) (hmn : m*n≤d)
    (X Y : GraphState U r c) (h : GraphAdj U r c X Y) :
    (smallData U (d^12) d r c er ec i₀ j₀ hrc (by omega) hmn).chain.P X Y ≥
      1/(128*(d:ℝ)^2)*min 1
        ((weight U (d^12) r c (graphUnderlying U r c Y):ℝ)/weight U (d^12) r c (graphUnderlying U r c X)) := by
  have hne : X≠Y := by rintro rfl; exact GraphAdj.irrefl U r c X h
  have hf : (0:ℝ)<weight U (d^12) r c (graphUnderlying U r c X) := by
    exact_mod_cast graph_weight_pos U (d^12) r c X hrc
  have hh : (weight U (d^12) r c (graphUnderlying U r c X):ℝ) ≤
      2*(acceptCount U (d^12) r c er ec i₀ j₀ X Y:ℝ) := by
    exact_mod_cast acceptCount_half U r c er ec i₀ j₀ d hd hm hn hmn X Y h
  change (if X=Y then _ else _ )≥_
  rw [ite_eq_right hne]
  change proposalRate (32*d^2)*edgeCount U (d^12) r c er ec i₀ j₀ X Y /
    (weight U (d^12) r c (graphUnderlying U r c X):ℝ) ≥ _
  rw [edgeCount,ite_eq_left h]
  have hq := (smallProposal_bounds d (by omega)).1
  have hc : (0:ℝ)≤acceptCount U (d^12) r c er ec i₀ j₀ X Y := by positivity
  have hd' : (0:ℝ)<d := by exact_mod_cast (by omega : 0<d)
  calc
    _ ≥ (1/(64*(d:ℝ)^2))*acceptCount U (d^12) r c er ec i₀ j₀ X Y /
      (weight U (d^12) r c (graphUnderlying U r c X):ℝ) := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hq hc) hf.le
    _ ≥ 1/(128*(d:ℝ)^2) := by
      apply (le_div_iff₀ hf).mpr
      field_simp
      nlinarith
    _ ≥ _ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) _) (by positivity : 0≤1/(128*(d:ℝ)^2))

end
end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
variable {m n a b : ℕ} (U L C d : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)

def extendGraph (H : GraphState U r c → ℝ) : State m n → ℝ :=
  Function.extend (graphUnderlying U r c) H (fun _ => 0)

@[simp] theorem extendGraph_apply (H : GraphState U r c → ℝ) (X : GraphState U r c) :
    extendGraph U r c H (graphUnderlying U r c X)=H X :=
  (graphUnderlying_injective U r c).extend_apply H (fun _ => 0) X

lemma sum_le_mapped_support {α β : Type*} [DecidableEq α] [Fintype β]
    (E : Finset α) (f : α → ℝ) (F : β → α)
    (hf : ∀ e,0≤f e) (hs : ∀ e∈E,f e≠0 → ∃ x,F x=e) :
    (∑ e∈E,f e) ≤ ∑ x,if F x∈E then f (F x) else 0 := by
  classical
  let I := Finset.univ.image F
  let g := fun e => if e∈E then f e else 0
  have hg : ∀ e,0≤g e := by
    intro e; dsimp [g]; split_ifs
    · exact hf e
    · exact le_rfl
  have heq : (∑ e∈E,f e)=∑ e∈E,g e := by
    apply Finset.sum_congr rfl; intro e he
    exact (ite_eq_left he).symm
  have hz : ∀ e∈E∪I,e∉I → g e=0 := by
    intro e _ hi
    dsimp [g]
    split_ifs with he
    · by_contra hp
      obtain ⟨x,hx⟩ := hs e he hp
      exact hi (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,hx⟩)
    · rfl
  have hi : (∑ e∈I,g e)=∑ e∈E∪I,g e := Finset.sum_subset Finset.subset_union_right hz
  calc
    _ = ∑ e∈E,g e := heq
    _ ≤ ∑ e∈E∪I,g e := Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun e _ _ => hg e)
    _ = ∑ e∈I,g e := hi.symm
    _ ≤ ∑ x,g (F x) := Finset.sum_image_le_of_nonneg (fun e _ => hg e)

theorem graphEdge_value (hrc : (∑ i,r i)=∑ j,c j)
    (hC : ∀ i,paddedRow U L r c i≤C) (H : GraphState U r c → ℝ)
    (X Y : GraphState U r c) :
    edgeEnergy (smallKernel 0 U L C r c) (extendGraph U r c H ∘ coordinatesState U r c)
      s(graphCoordinates U r c X,graphCoordinates U r c Y) =
    min (weight U L r c (graphUnderlying U r c X):ℝ) (weight U L r c (graphUnderlying U r c Y):ℝ)*(H X-H Y)^2 := by
  rw [edgeEnergy_mk]
  simp only [Function.comp_apply,graphCoordinates,
    coordinates_state_inverse U r c _ (graph_feasible U r c X).2.1,
    coordinates_state_inverse U r c _ (graph_feasible U r c Y).2.1,
    state_kernel_weight U L C r c hrc hC _ (graph_feasible U r c X),
    state_kernel_weight U L C r c hrc hC _ (graph_feasible U r c Y),extendGraph_apply]

theorem graphEnergy_le_pairs (H : GraphState U r c → ℝ) :
    graphEnergy U L C r c (extendGraph U r c H) ≤
      ∑ xy : GraphState U r c × GraphState U r c,
        if s(graphCoordinates U r c xy.1,graphCoordinates U r c xy.2)∈fullEdges U r c then
          edgeEnergy (smallKernel 0 U L C r c) (extendGraph U r c H ∘ coordinatesState U r c)
            s(graphCoordinates U r c xy.1,graphCoordinates U r c xy.2) else 0 := by
  classical
  have hh := sum_le_mapped_support (fullEdges U r c)
    (edgeEnergy (smallKernel 0 U L C r c) (extendGraph U r c H ∘ coordinatesState U r c))
    (fun xy : GraphState U r c × GraphState U r c =>
      s(graphCoordinates U r c xy.1,graphCoordinates U r c xy.2))
    (edgeEnergy_nonneg _ _ (smallKernel_nonneg 0 (by positivity) U L C r c))
    (fun e he hp => by
      obtain ⟨X,Y,hXY⟩ := positive_edge U L C r c (extendGraph U r c H) e he hp
      exact ⟨(X,Y),hXY.symm⟩)
  exact hh

theorem graphEnergy_le_ordered (hrc : (∑ i,r i)=∑ j,c j)
    (hC : ∀ i,paddedRow U L r c i≤C) (H : GraphState U r c → ℝ) :
    graphEnergy U L C r c (extendGraph U r c H) ≤
      ∑ X,∑ Y,if GraphAdj U r c X Y then
        min (weight U L r c (graphUnderlying U r c X):ℝ) (weight U L r c (graphUnderlying U r c Y):ℝ)*(H X-H Y)^2 else 0 := by
  classical
  have hh := graphEnergy_le_pairs U L C r c H
  rw [Fintype.sum_prod_type] at hh
  refine hh.trans_eq ?_
  apply Finset.sum_congr rfl; intro X _
  apply Finset.sum_congr rfl; intro Y _
  by_cases h : GraphAdj U r c X Y
  · have h' : s(graphCoordinates U r c X,graphCoordinates U r c Y)∈fullEdges U r c := h
    simp only [ite_eq_left h,ite_eq_left h']
    exact graphEdge_value U L C r c hrc hC H X Y
  · have h' : s(graphCoordinates U r c X,graphCoordinates U r c Y)∉fullEdges U r c := h
    simp only [ite_eq_right h,ite_eq_right h']

variable (er : Fin a ≃ {i // U≤r i}) (ec : Fin b ≃ {j // U≤c j})
    (i₀ : Fin a) (j₀ : Fin b)

theorem graphEnergy_le_accepted (hrc : (∑ i,r i)=∑ j,c j)
    (hd : 14≤d) (hm : m ≤ d) (hn : n ≤ d) (hmn : m*n≤d)
    (hC : ∀ i,paddedRow U (d^12) r c i≤C) (H : GraphState U r c → ℝ) :
    graphEnergy U (d^12) C r c (extendGraph U r c H) ≤
      2*(∑ X,∑ Y,edgeCount U (d^12) r c er ec i₀ j₀ X Y*(H X-H Y)^2) := by
  apply (graphEnergy_le_ordered U (d^12) C r c hrc hC H).trans
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum; intro X _
  apply Finset.sum_le_sum; intro Y _
  by_cases h : GraphAdj U r c X Y
  · simp only [ite_eq_left h,edgeCount]
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply (min_le_left _ _).trans
    exact_mod_cast acceptCount_half U r c er ec i₀ j₀ d hd hm hn hmn X Y h
  · simp [h,edgeCount]

end
end Contingency.PaddedGraph

end

end OAI
