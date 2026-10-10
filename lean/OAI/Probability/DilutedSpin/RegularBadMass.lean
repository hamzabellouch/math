import OAI.Probability.DilutedSpin.PhysicalOverlapLimit

namespace OAI

section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance regularBadMassDecidableEq (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
noncomputable local instance regularBadMassDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

lemma uniform_indicator_eq (P : Fin L → Prop) :
    (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun x => if P x then (1:ℝ) else 0)=
      ((Finset.univ.filter P).card:ℝ)/(L:ℝ) := by
  unfold FiniteLaw.expect FiniteLaw.uniform
  simp only [Fintype.card_fin]
  rw [← Finset.mul_sum,← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,div_eq_mul_inv,mul_comm]

lemma uniform_interval_le (a b : ℕ) :
    (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun x => if a ≤ x.val ∧ x.val ≤ b then (1:ℝ) else 0)  ≤ 
      ((b+1-a:ℕ):ℝ)/(L:ℝ) := by
  have he := uniform_indicator_eq (L := L) (fun x : Fin L => a ≤ x.val ∧ x.val ≤ b)
  have he' : (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun x => if a ≤ x.val ∧ x.val ≤ b then (1:ℝ) else 0) =
      ((Finset.univ.filter (fun x : Fin L => a ≤ x.val ∧ x.val ≤ b)).card:ℝ)/(L:ℝ) := by
    convert he using 1
    · congr 1; funext x; split_ifs <;> rfl
    · congr 3; ext x; simp
  rw [he']
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter (fun x : Fin L => a ≤ x.val ∧ x.val ≤ b))
    (t := Finset.Icc a b) Fin.val
    (by intro x hx; exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hx).2)
    (by intro x hx y hy hxy; exact Fin.ext hxy)
  simpa only [Nat.card_Icc] using h

lemma uniform_boundary_le (r : ℕ) :
    (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun x => if x.val ≤ r ∨ L ≤ x.val+r then (1:ℝ) else 0)  ≤ 
      (2*(r+1:ℕ):ℝ)/(L:ℝ) := by
  have hmono := (FiniteLaw.uniform : FiniteLaw (Fin L)).expect_mono (fun x =>
    (show (if x.val ≤ r ∨ L ≤ x.val+r then (1:ℝ) else 0)  ≤ 
       (if 0 ≤ x.val ∧ x.val ≤ r then 1 else 0)+(if L-r ≤ x.val ∧ x.val ≤ L-1 then 1 else 0) by
      have hxr : x.val ≤ L-1 := by have := x.isLt; omega
      have hriff : L ≤ x.val+r ↔ L-r ≤ x.val := by omega
      simp only [hriff,Nat.zero_le,true_and,hxr,and_true]
      split_ifs <;> norm_num at *
      omega))
  rw [FiniteLaw.expect_add] at hmono
  apply hmono.trans
  apply (add_le_add (uniform_interval_le 0 r) (uniform_interval_le (L-r) (L-1))).trans
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h : (r+1-0)+(L-1+1-(L-r)) ≤ 2*(r+1) := by omega
  exact_mod_cast h

lemma uniform_near_le (r : ℕ) (y : Fin L) :
    (FiniteLaw.uniform : FiniteLaw (Fin L)).expect (fun x =>
      if x.val ≤ y.val+r ∧ y.val ≤ x.val+r then (1:ℝ) else 0)  ≤  (2*(r+1:ℕ):ℝ)/(L:ℝ) := by
  have he : (fun x : Fin L => if x.val ≤ y.val+r ∧ y.val ≤ x.val+r then (1:ℝ) else 0)=
      (fun x => if y.val-r ≤ x.val ∧ x.val ≤ y.val+r then 1 else 0) := by
    funext x
    have h : (x.val ≤ y.val+r ∧ y.val ≤ x.val+r) ↔ (y.val-r ≤ x.val ∧ x.val ≤ y.val+r) := by omega
    simp only [h]
  rw [he]
  apply (uniform_interval_le (y.val-r) (y.val+r)).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (show y.val+r+1-(y.val-r) ≤ 2*(r+1) by omega)

lemma average_boundary_le (r : ℕ) (i : α) :
    average (fun q : α → Fin L => (q i).val ≤ r ∨ L ≤ (q i).val+r) (fun _ => 1)  ≤ 
      (2*(r+1:ℕ):ℝ)/(L:ℝ) := by
  unfold average depthLaw
  have he := FiniteLaw.expect_pi_marginal (fun _ : α => (FiniteLaw.uniform : FiniteLaw (Fin L))) i
    (fun x => if x.val ≤ r ∨ L ≤ x.val+r then (1:ℝ) else 0)
  convert he.le.trans (uniform_boundary_le r) using 1
  congr 1; funext depth; split_ifs <;> rfl

lemma average_near_le (r : ℕ) (i j : α) (hij : i≠j) :
    average (fun q : α → Fin L => (q i).val ≤ (q j).val+r ∧ (q j).val ≤ (q i).val+r) (fun _ => 1)  ≤ 
      (2*(r+1:ℕ):ℝ)/(L:ℝ) := by
  rw [average_split_comm i]
  apply (FiniteLaw.expect_mono _ (fun rest => ?_)).trans_eq (FiniteLaw.expect_const _ _)
  have hj : j≠i := Ne.symm hij
  simp only [insertCoordinate_self]
  have hrest (t : Fin L) : insertCoordinate i t rest j=rest ⟨j,hj⟩ := insertCoordinate_other i t rest ⟨j,hj⟩
  simp only [hrest]
  exact uniform_near_le r (rest ⟨j,hj⟩)

omit [Fintype α] [DecidableEq α] in
lemma regular_of_discrete {η : ℝ} {r : ℕ} (hηr : η*(L:ℝ) ≤ r) (q : α → Fin L)
    (hb : ∀ i, ¬((q i).val ≤ r ∨ L ≤ (q i).val+r))
    (hc : ∀ i j, i≠j → ¬((q i).val ≤ (q j).val+r ∧ (q j).val ≤ (q i).val+r)) : Regular η q := by
  have hL : (0:ℝ)<L := Nat.cast_pos.mpr (NeZero.pos L)
  constructor
  · intro i
    obtain ⟨hi,hj⟩ := not_or.mp (hb i)
    have hi' : (r:ℝ)<(q i).val := by exact_mod_cast Nat.lt_of_not_ge hi
    have hj' : ((q i).val:ℝ)+r<L := by exact_mod_cast Nat.lt_of_not_ge hj
    constructor
    · exact (lt_div_iff₀ hL).mpr (hηr.trans_lt hi')
    · apply (div_lt_iff₀ hL).mpr
      nlinarith
  · intro i j hij
    have hh := hc i j hij
    have hd : (r:ℝ) < |((q i).val:ℝ)-(q j).val| := by
      by_cases h : (q i).val ≤ (q j).val+r
      · have h' : (q i).val+r<(q j).val := by omega
        have hr : ((q i).val:ℝ)+r<(q j).val := by exact_mod_cast h'
        rw [abs_of_neg (by linarith : ((q i).val:ℝ)-(q j).val<0)]
        linarith
      · have hr : ((q j).val:ℝ)+r<(q i).val := by exact_mod_cast Nat.lt_of_not_ge h
        rw [abs_of_pos (by linarith : 0<((q i).val:ℝ)-(q j).val)]
        linarith
    unfold normalized
    rw [← sub_div,abs_div,abs_of_pos hL]
    exact (lt_div_iff₀ hL).mpr (hηr.trans_lt hd)

lemma nonregular_pointwise {η : ℝ} {r : ℕ} (hηr : η*(L:ℝ) ≤ r) (q : α → Fin L) :
    (if ¬Regular η q then (1:ℝ) else 0)  ≤ 
      (∑ i, if (q i).val ≤ r ∨ L ≤ (q i).val+r then 1 else 0)+
      ∑ i, ∑ j, if i≠j ∧ (q i).val ≤ (q j).val+r ∧ (q j).val ≤ (q i).val+r then 1 else 0 := by
  have hn (P : Prop) : (0:ℝ) ≤ if P then 1 else 0 := by split_ifs <;> norm_num
  have hbn : 0 ≤ ∑ i, if (q i).val ≤ r ∨ L ≤ (q i).val+r then (1:ℝ) else 0 := Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  have hcn : 0 ≤ ∑ i, ∑ j, if i≠j ∧ (q i).val ≤ (q j).val+r ∧ (q j).val ≤ (q i).val+r then (1:ℝ) else 0 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
  by_cases hb : ∃ i, (q i).val ≤ r ∨ L ≤ (q i).val+r
  · obtain ⟨i,hi⟩ := hb
    have hs : 1 ≤ ∑ j : α, if (q j).val ≤ r ∨ L ≤ (q j).val+r then (1:ℝ) else 0 := by
      calc
        1 = (if (q i).val ≤ r ∨ L ≤ (q i).val+r then (1:ℝ) else 0) := by rw [ite_eq_left hi]
        _ ≤ _ := Finset.single_le_sum (f := fun j : α => if (q j).val ≤ r ∨ L ≤ (q j).val+r then (1:ℝ) else 0) (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
    split_ifs <;> linarith
  · by_cases hc : ∃ i j, i≠j ∧ (q i).val ≤ (q j).val+r ∧ (q j).val ≤ (q i).val+r
    · obtain ⟨i,j,hij⟩ := hc
      have hs : 1 ≤ ∑ j' : α, if i≠j' ∧ (q i).val ≤ (q j').val+r ∧ (q j').val ≤ (q i).val+r then (1:ℝ) else 0 := by
        calc
          1 = (if i≠j ∧ (q i).val ≤ (q j).val+r ∧ (q j).val ≤ (q i).val+r then (1:ℝ) else 0) := by rw [ite_eq_left hij]
          _ ≤ _ := Finset.single_le_sum (f := fun j' : α => if i≠j' ∧ (q i).val ≤ (q j').val+r ∧ (q j').val ≤ (q i).val+r then (1:ℝ) else 0) (fun j' _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
      have ht : (∑ j' : α, if i≠j' ∧ (q i).val ≤ (q j').val+r ∧ (q j').val ≤ (q i).val+r then (1:ℝ) else 0) ≤
          ∑ i' : α, ∑ j' : α, if i'≠j' ∧ (q i').val ≤ (q j').val+r ∧ (q j').val ≤ (q i').val+r then (1:ℝ) else 0 :=
        Finset.single_le_sum (f := fun i' : α => ∑ j' : α, if i'≠j' ∧ (q i').val ≤ (q j').val+r ∧ (q j').val ≤ (q i').val+r then (1:ℝ) else 0) (fun i' _ => Finset.sum_nonneg (fun j' _ => by split_ifs <;> norm_num)) (Finset.mem_univ i)
      split_ifs <;> linarith
    · have hr := regular_of_discrete hηr q (by simpa only [not_exists] using hb)
        (by simpa only [not_exists,not_and] using hc)
      rw [ite_eq_right (not_not.mpr hr)]
      exact add_nonneg hbn hcn

lemma nonregular_average_bound {η : ℝ} {r : ℕ} (hηr : η*(L:ℝ) ≤ r) :
    average (fun q : α → Fin L => ¬Regular η q) (fun _ => 1)  ≤ 
      ((Fintype.card α:ℝ)+(Fintype.card α:ℝ)^2)*(2*(r+1:ℕ):ℝ)/(L:ℝ) := by
  have hm := (depthLaw α L).expect_mono (nonregular_pointwise hηr)
  rw [FiniteLaw.expect_add,FiniteLaw.expect_fintype_sum] at hm
  simp_rw [FiniteLaw.expect_fintype_sum] at hm
  apply le_trans (b := (∑ i : α, (depthLaw α L).expect (fun q => if (q i).val ≤ r ∨ L ≤ (q i).val+r then (1:ℝ) else 0)) +
    ∑ i : α, ∑ j : α, (depthLaw α L).expect (fun q => if i≠j ∧ (q i).val ≤ (q j).val+r ∧ (q j).val ≤ (q i).val+r then (1:ℝ) else 0))
  · convert hm using 1
    unfold average; congr 1; funext depth; split_ifs <;> rfl
  have hc (i j : α) : (depthLaw α L).expect (fun q =>
      if i≠j ∧ (q i).val ≤ (q j).val+r ∧ (q j).val ≤ (q i).val+r then (1:ℝ) else 0)  ≤  (2*(r+1:ℕ):ℝ)/(L:ℝ) := by
    by_cases hij : i=j
    · subst j
      simp only [ne_eq,not_true_eq_false,false_and,ite_false,FiniteLaw.expect_const]
      positivity
    · have hh := average_near_le (L := L) r i j hij
      unfold average at hh
      convert hh using 1
      · congr 1
        funext q
        dsimp only
        by_cases hq : (q i).val ≤ (q j).val+r ∧ (q j).val ≤ (q i).val+r
        · simp only [ite_eq_left hq,ite_eq_left (And.intro hij hq)]
        · simp only [ite_eq_right hq,ite_eq_right (not_and_of_not_right _ hq)]
  have hb := Finset.sum_le_sum (fun (i : α) (_ : i∈Finset.univ) => average_boundary_le (L := L) r i)
  have ht := Finset.sum_le_sum (fun (i : α) (_ : i∈Finset.univ) => Finset.sum_le_sum (fun (j : α) (_ : j∈Finset.univ) => hc i j))
  have hs := add_le_add hb ht
  have hs' : (∑ i : α, average (fun q : α → Fin L => (q i).val ≤ r ∨ L ≤ (q i).val+r) (fun _ => 1)) +
      (∑ i : α, ∑ j : α, (depthLaw α L).expect (fun q => if i≠j ∧ (q i).val ≤ (q j).val+r ∧ (q j).val ≤ (q i).val+r then (1:ℝ) else 0)) ≤
      ((Fintype.card α:ℝ)+(Fintype.card α:ℝ)^2)*(2*(r+1:ℕ):ℝ)/(L:ℝ) := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
    apply hs.trans_eq
    push_cast
    ring
  apply le_trans (b := (∑ i : α, average (fun q : α → Fin L => (q i).val ≤ r ∨ L ≤ (q i).val+r) (fun _ => 1)) +
      (∑ i : α, ∑ j : α, (depthLaw α L).expect (fun q => if i≠j ∧ (q i).val ≤ (q j).val+r ∧ (q j).val ≤ (q i).val+r then (1:ℝ) else 0))) _ hs'
  apply le_of_eq
  apply congrArg (fun x => x+_)
  apply Finset.sum_congr rfl
  intro i _
  unfold average
  congr 1; funext q; split_ifs <;> rfl

end DilutedSpinGlass.DepthAverage

end

end OAI
