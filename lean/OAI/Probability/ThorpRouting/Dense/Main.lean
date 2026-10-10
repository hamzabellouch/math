import Mathlib
import OAI.Probability.ThorpRouting.Dense.SingleSlotsEquiv

namespace OAI

namespace ThorpNine.Dense

open scoped BigOperators
namespace Thorp

lemma sharedPartnerMean_nonneg (r s : ℕ) (A : Finset (Card ((s+1)+r))) :
    0 ≤ sharedPartnerMean r s A := by
  unfold sharedPartnerMean
  positivity

lemma sum_suffix_pair_counts (r s : ℕ) (A : Finset (Card ((s+1)+r))) :
    (∑ y : Card s, ((suffixMarks r (s+1) A (Fin.cons false y)).card +
      (suffixMarks r (s+1) A (Fin.cons true y)).card)) = A.card := by
  classical
  have hh := sum_card_blockMarks ((cardSplit r (s+1)).trans (Equiv.prodComm _ _)) A
  rw [←Equiv.sum_comp (headTailEquiv s).symm,Fintype.sum_prod_type,Fintype.sum_bool] at hh
  simpa [suffixMarks,headTailEquiv,Fin.consEquiv,Finset.sum_add_distrib,add_comm] using hh

lemma sharedPartnerMean_twice_le (r s : ℕ) (A : Finset (Card ((s+1)+r))) :
    2*sharedPartnerMean r s A ≤ A.card := by
  have hcap (y : Card (s+1)) : (suffixMarks r (s+1) A y).card ≤ 2^r := by
    simpa only [card_positions] using Finset.card_le_univ (suffixMarks r (s+1) A y)
  have hp : (0:ℝ) < (2:ℝ)^r := by positivity
  rw [sharedPartnerMean,←mul_div_assoc,div_le_iff₀ hp,Finset.mul_sum]
  have hs : (A.card:ℝ) = ∑ y : Card s,
      ((suffixMarks r (s+1) A (Fin.cons false y)).card +
        (suffixMarks r (s+1) A (Fin.cons true y)).card : ℝ) := by
    exact_mod_cast (sum_suffix_pair_counts r s A).symm
  rw [hs,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro y _
  have h₀ : (suffixMarks r (s+1) A (Fin.cons false y)).card ≤ (2:ℝ)^r := by
    exact_mod_cast hcap (Fin.cons false y)
  have h₁ : (suffixMarks r (s+1) A (Fin.cons true y)).card ≤ (2:ℝ)^r := by
    exact_mod_cast hcap (Fin.cons true y)
  nlinarith [mul_nonneg (sub_nonneg.mpr h₀)
    (Nat.cast_nonneg (suffixMarks r (s+1) A (Fin.cons true y)).card),
    mul_nonneg (sub_nonneg.mpr h₁)
    (Nat.cast_nonneg (suffixMarks r (s+1) A (Fin.cons false y)).card)]


lemma palindrome_level_dense_mgf (r s : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card ((s+1)+r)) (t : ℝ) (ht : 0 ≤ t) :
    finiteMean (fun ω : BenesCoins ((s+1)+r) =>
      Real.exp (t * palindromeLevelCost (s+1) ((s+1)+r) e ω)) ≤
        Real.exp ((Real.exp (denseLevelCoefficient s t)-1) *
          sharedPartnerMean r s (Finset.univ.image e)) := by
  classical
  rw [finiteMean_prod,finiteMean_comm]
  calc
    _ ≤ finiteMean (fun X : SwitchIndex ((s+1)+r) → Bool =>
        Real.exp (denseLevelCoefficient s t * sharedLevel (s+1) ((s+1)+r) e X)) := by
      apply finiteMean_mono
      intro X
      exact palindrome_level_dense_conditional s ((s+1)+r) e X t ht
    _ = finiteMean (fun hi : Card (s+1) × SwitchIndex r → Bool =>
        Real.exp (denseLevelCoefficient s t *
          gridShared r s (inverseButterflyMarks ((s+1)+r) (Finset.univ.image e)
            (assembleBits r (s+1) (fun _ => false) hi)))) := by
      rw [finiteMean_split]
      simp_rw [sharedLevel_partial_marks]
      rw [finiteMean_const]
    _ ≤ _ := partial_grid_mgf r s (Finset.univ.image e) _
        (denseLevelCoefficient_nonneg s ht)


lemma cardSplit_snd_apply (r s : ℕ) (x : Card (s+r)) (i : Fin s) :
    (cardSplit r s x).2 i = x ⟨r+i,by omega⟩ := by
  induction r with
  | zero => simp [cardSplit]
  | succ r ih =>
    change (cardSplit r s (Fin.tail x)).2 i = _
    rw [ih]
    simp only [Fin.tail]
    congr 1
    apply Fin.ext
    simp only [Fin.val_succ]
    omega

def PairSeparated {d : ℕ} (i : Fin d) (x y : Card d) : Prop :=
  x i = false ∧ y i = true ∧ ∀ j : Fin d, i < j → x j = y j

lemma PairSeparated.unique {d : ℕ} {i j : Fin d} {x y : Card d}
    (hi : PairSeparated i x y) (hj : PairSeparated j x y) : i = j := by
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · have hh := hi.2.2 j h
    rw [hj.1,hj.2.1] at hh
    exact Bool.false_ne_true hh
  · have hh := hj.2.2 i h
    rw [hi.1,hi.2.1] at hh
    exact Bool.false_ne_true hh

lemma PairSeparated.not_reverse {d : ℕ} {i j : Fin d} {x y : Card d}
    (hi : PairSeparated i x y) : ¬ PairSeparated j y x := by
  intro hj
  rcases lt_trichotomy i j with h | h | h
  · have hh := hi.2.2 j h
    rw [hj.2.1,hj.1] at hh
    exact Bool.noConfusion hh
  · subst j
    exact Bool.false_ne_true (hi.1.symm.trans hj.2.1)
  · have hh := hj.2.2 i h
    rw [hi.1,hi.2.1] at hh
    exact Bool.noConfusion hh

lemma pairSeparated_split_iff (r s : ℕ) (x y : Card ((s+1)+r)) :
    PairSeparated ⟨r,by omega⟩ x y ↔
      ∃ z : Card s, (cardSplit r (s+1) x).2 = Fin.cons false z ∧
        (cardSplit r (s+1) y).2 = Fin.cons true z := by
  constructor
  · intro h
    refine ⟨Fin.tail (cardSplit r (s+1) x).2, ?_, ?_⟩
    · have h₀ : (cardSplit r (s+1) x).2 0 = false := by
        simpa only [cardSplit_snd_apply,Fin.val_zero,Nat.add_zero] using h.1
      rw [←h₀,Fin.cons_self_tail]
    · funext k
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa only [cardSplit_snd_apply,Fin.cons_zero,Fin.val_zero,Nat.add_zero] using h.2.1
      · simp only [Fin.cons_succ,Fin.tail,cardSplit_snd_apply]
        exact (h.2.2 _ (by change r < r + (k.val+1); omega)).symm
  · rintro ⟨z,hx,hy⟩
    refine ⟨?_,?_,?_⟩
    · have hh := congrFun hx 0
      simpa only [cardSplit_snd_apply,Fin.cons_zero,Fin.val_zero,Nat.add_zero] using hh
    · have hh := congrFun hy 0
      simpa only [cardSplit_snd_apply,Fin.cons_zero,Fin.val_zero,Nat.add_zero] using hh
    · intro j hj
      change r < j.val at hj
      have hbound : j.val-r-1 < s := by omega
      let k : Fin s := ⟨j.val-r-1,hbound⟩
      have hjk : j = ⟨r+(k.val+1),by omega⟩ := Fin.ext (by dsimp [k]; omega)
      rw [hjk]
      have hx' := congrFun hx k.succ
      have hy' := congrFun hy k.succ
      simp only [cardSplit_snd_apply,Fin.cons_succ] at hx' hy'
      exact hx'.trans hy'.symm


abbrev SeparatedPair {d : ℕ} (A : Finset (Card d)) (i : Fin d) :=
  {p : A × A // PairSeparated i p.1.val p.2.val}

noncomputable def separatedCount {d : ℕ} (A : Finset (Card d)) (i : Fin d) : ℕ := by
  classical
  exact Fintype.card (SeparatedPair A i)

lemma separated_budget_strong {d : ℕ} (A : Finset (Card d)) :
    2 * ∑ i : Fin d, separatedCount A i ≤ A.card * (A.card-1) := by
  classical
  let F : Bool × (Σ i : Fin d, SeparatedPair A i) → A × A :=
    fun ⟨b,i,p⟩ => if b then (p.val.2,p.val.1) else p.val
  have hF : Function.Injective F := by
    rintro ⟨b,i,p⟩ ⟨c,j,q⟩ h
    cases b <;> cases c
    · change p.val = q.val at h
      have hij : i = j := p.property.unique (by rw [h]; exact q.property)
      subst j
      have hpq : p = q := Subtype.ext h
      subst q
      rfl
    · change p.val = (q.val.2,q.val.1) at h
      have hp := p.property
      rw [h] at hp
      exact False.elim (hp.not_reverse q.property)
    · change (p.val.2,p.val.1) = q.val at h
      have hq := q.property
      rw [←h] at hq
      exact False.elim (hq.not_reverse p.property)
    · change (p.val.2,p.val.1) = (q.val.2,q.val.1) at h
      have hpq : p.val = q.val := Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      have hij : i = j := p.property.unique (by rw [hpq]; exact q.property)
      subst j
      have hpqq : p = q := Subtype.ext hpq
      subst q
      rfl
  have hneq (v : Bool × (Σ i : Fin d, SeparatedPair A i)) : (F v).1 ≠ (F v).2 := by
    obtain ⟨b,i,p⟩ := v
    have hp : p.val.1 ≠ p.val.2 := by
      intro he
      have hx := p.property.1
      have hy := p.property.2.1
      rw [he] at hx
      exact Bool.false_ne_true (hx.symm.trans hy)
    cases b <;> simp [F,hp,Ne.symm hp]
  let G : Bool × (Σ i : Fin d, SeparatedPair A i) → ↥((Finset.univ : Finset A).offDiag) :=
    fun v => ⟨F v,Finset.mem_offDiag.mpr ⟨Finset.mem_univ _,Finset.mem_univ _,hneq v⟩⟩
  have hG : Function.Injective G := fun _ _ he => hF (congrArg Subtype.val he)
  have hh := Fintype.card_le_of_injective G hG
  simpa only [Fintype.card_prod,Fintype.card_bool,Fintype.card_sigma,
    Fintype.card_coe,separatedCount,Finset.offDiag_card,Finset.card_univ,
    Nat.mul_sub_left_distrib,mul_one] using hh

lemma separated_budget {d : ℕ} (A : Finset (Card d)) :
    2 * ∑ i : Fin d, separatedCount A i ≤ A.card * A.card :=
  (separated_budget_strong A).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

lemma mem_suffixMarks (r s : ℕ) (A : Finset (Card (s+r))) (y : Card s) (x : Card r) :
    x ∈ suffixMarks r s A y ↔ (cardSplit r s).symm (x,y) ∈ A := by
  exact mem_blockMarks _ _ _ _

lemma separatedCount_eq (r s : ℕ) (A : Finset (Card ((s+1)+r))) :
    separatedCount A ⟨r,by omega⟩ =
      ∑ y : Card s, (suffixMarks r (s+1) A (Fin.cons false y)).card *
        (suffixMarks r (s+1) A (Fin.cons true y)).card := by
  classical
  let D := Σ y : Card s, ↥(suffixMarks r (s+1) A (Fin.cons false y)) ×
    ↥(suffixMarks r (s+1) A (Fin.cons true y))
  let F : D → SeparatedPair A ⟨r,by omega⟩ := fun ⟨y,u,v⟩ =>
    ⟨(⟨(cardSplit r (s+1)).symm (u.val,Fin.cons false y),
          (mem_suffixMarks _ _ _ _ _).mp u.property⟩,
        ⟨(cardSplit r (s+1)).symm (v.val,Fin.cons true y),
          (mem_suffixMarks _ _ _ _ _).mp v.property⟩),
      (pairSeparated_split_iff r s _ _).mpr
        ⟨y,by simp only [Equiv.apply_symm_apply],by simp only [Equiv.apply_symm_apply]⟩⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨y,u,v⟩ ⟨z,u',v'⟩ he
      have h₀ := congrArg (fun p => cardSplit r (s+1) p.val.1.val) he
      have h₁ := congrArg (fun p => cardSplit r (s+1) p.val.2.val) he
      change cardSplit r (s+1) ((cardSplit r (s+1)).symm (u.val,Fin.cons false y)) =
        cardSplit r (s+1) ((cardSplit r (s+1)).symm (u'.val,Fin.cons false z)) at h₀
      change cardSplit r (s+1) ((cardSplit r (s+1)).symm (v.val,Fin.cons true y)) =
        cardSplit r (s+1) ((cardSplit r (s+1)).symm (v'.val,Fin.cons true z)) at h₁
      simp only [Equiv.apply_symm_apply] at h₀ h₁
      have hyz : y = z := by
        have hh := congrArg (fun p => Fin.tail p.2) h₀
        simpa only [Fin.tail_cons] using hh
      subst z
      have hu : u = u' := Subtype.ext (congrArg Prod.fst h₀)
      have hv : v = v' := Subtype.ext (congrArg Prod.fst h₁)
      subst u'; subst v'; rfl
    · intro p
      obtain ⟨y,hx,hy⟩ := (pairSeparated_split_iff r s p.val.1.val p.val.2.val).mp p.property
      have hx' : (cardSplit r (s+1)).symm ((cardSplit r (s+1) p.val.1.val).1,Fin.cons false y) =
          p.val.1.val := by rw [←hx,Prod.mk.eta,Equiv.symm_apply_apply]
      have hy' : (cardSplit r (s+1)).symm ((cardSplit r (s+1) p.val.2.val).1,Fin.cons true y) =
          p.val.2.val := by rw [←hy,Prod.mk.eta,Equiv.symm_apply_apply]
      refine ⟨⟨y,⟨(cardSplit r (s+1) p.val.1.val).1,?_⟩,
          ⟨(cardSplit r (s+1) p.val.2.val).1,?_⟩⟩,?_⟩
      · rw [mem_suffixMarks,hx']; exact p.val.1.property
      · rw [mem_suffixMarks,hy']; exact p.val.2.property
      · apply Subtype.ext
        exact Prod.ext (Subtype.ext hx') (Subtype.ext hy')
  have hh := Fintype.card_congr (Equiv.ofBijective F hF)
  simpa only [D,Fintype.card_sigma,Fintype.card_prod,Fintype.card_coe,separatedCount] using hh.symm


noncomputable def partnerMean (d : ℕ) (A : Finset (Card d)) (j : ℕ) : ℝ :=
  if hj : j < d then (separatedCount A ⟨d-j-1,by omega⟩ : ℝ) / (2:ℝ)^(d-j-1) else 0

lemma partnerMean_nonneg (d : ℕ) (A : Finset (Card d)) (j : ℕ) :
    0 ≤ partnerMean d A j := by
  unfold partnerMean
  split <;> positivity

lemma partnerMean_eq (r s : ℕ) (A : Finset (Card ((s+1)+r))) :
    partnerMean ((s+1)+r) A s = sharedPartnerMean r s A := by
  classical
  have hs : s < (s+1)+r := by omega
  have hr : (s+1+r)-s-1 = r := by omega
  simp only [partnerMean,dite_eq_left hs,hr,separatedCount_eq,sharedPartnerMean,
    Nat.cast_sum,Nat.cast_mul]

lemma partnerMean_twice_le (d : ℕ) (A : Finset (Card d)) (j : ℕ) :
    2*partnerMean d A j ≤ A.card := by
  by_cases hj : j < d
  · obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hj)
    rw [partnerMean_eq]
    exact sharedPartnerMean_twice_le r j A
  · simp only [partnerMean,dite_eq_right hj,mul_zero,Nat.cast_nonneg]

lemma partnerMean_rate (d : ℕ) (A : Finset (Card d)) (j : Fin d) :
    partnerMean d A j / (2:ℝ)^(j.val+1) =
      (separatedCount A j.rev : ℝ) / (2:ℝ)^d := by
  have hj : j.val < d := j.isLt
  have hd : (d-j.val-1)+(j.val+1) = d := by omega
  simp only [partnerMean,dite_eq_left hj,div_div,←pow_add,hd]
  rfl

lemma partnerMean_budget (d : ℕ) (A : Finset (Card d)) :
    2 * (∑ j ∈ Finset.range d, partnerMean d A j / (2:ℝ)^(j+1)) ≤
      (A.card:ℝ)^2/(2:ℝ)^d := by
  classical
  rw [←Fin.sum_univ_eq_sum_range]
  simp_rw [partnerMean_rate]
  rw [←Finset.sum_div]
  have he : (∑ j : Fin d, (separatedCount A j.rev:ℝ)) = ∑ j : Fin d, (separatedCount A j:ℝ) := by
    exact Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin d)) (fun j : Fin d => (separatedCount A j : ℝ))
  rw [he,←mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (by simpa only [pow_two] using separated_budget A)

noncomputable def partnerAllocation (d : ℕ) (A : Finset (Card d)) (j : ℕ) : ℝ :=
  2*partnerMean d A j/A.card

lemma partnerAllocation_admissible (d : ℕ) (A : Finset (Card d)) (hA : 0 < A.card) :
    DenseTruncation.AdmissibleAllocation ((A.card:ℝ)/(2:ℝ)^d) (partnerAllocation d A) := by
  classical
  have hA' : (0:ℝ) < A.card := by exact_mod_cast hA
  constructor
  · intro j
    constructor
    · exact div_nonneg (mul_nonneg (by norm_num) (partnerMean_nonneg d A j)) hA'.le
    · rw [partnerAllocation,div_le_one hA']
      exact partnerMean_twice_le d A j
  · have hz (j : ℕ) (hj : j ∉ Finset.range d) :
        partnerAllocation d A j/(2:ℝ)^(j+1) = 0 := by
      have h : ¬ j < d := by simpa only [Finset.mem_range] using hj
      simp only [partnerAllocation,partnerMean,dite_eq_right h,mul_zero,zero_div]
    rw [tsum_eq_sum (s := Finset.range d) hz]
    have he (j : ℕ) : partnerAllocation d A j/(2:ℝ)^(j+1) =
        2/A.card * (partnerMean d A j/(2:ℝ)^(j+1)) := by
      unfold partnerAllocation
      ring
    simp_rw [he]
    rw [←Finset.mul_sum]
    have hh := partnerMean_budget d A
    apply (show 2/(A.card:ℝ) * ∑ j ∈ Finset.range d, partnerMean d A j/(2:ℝ)^(j+1) =
      (2*(∑ j ∈ Finset.range d,partnerMean d A j/(2:ℝ)^(j+1)))/A.card by ring).le.trans
    apply (div_le_div_of_nonneg_right hh hA'.le).trans
    have hne : (A.card:ℝ) ≠ 0 := ne_of_gt hA'
    exact le_of_eq (by field_simp)


lemma partner_weighted_sum_le (d H : ℕ) (A : Finset (Card d)) (hA : 0 < A.card) :
    (∑ j ∈ Finset.range H, DenseTruncation.h (j+1)*partnerMean d A j) ≤
      A.card * DenseTruncation.H ((A.card:ℝ)/(2:ℝ)^d) := by
  have ha := partnerAllocation_admissible d A hA
  have hh := DenseTruncation.allocation_le_H ha
  have hA' : (0:ℝ) < A.card := by exact_mod_cast hA
  have he (j : ℕ) : DenseTruncation.h (j+1)*partnerMean d A j =
      (A.card:ℝ)/2*(DenseTruncation.h (j+1)*partnerAllocation d A j) := by
    unfold partnerAllocation
    field_simp
  simp_rw [he]
  rw [←Finset.mul_sum]
  calc
    _ ≤ (A.card:ℝ)/2 * ∑' j, DenseTruncation.h (j+1)*partnerAllocation d A j := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (DenseTruncation.allocation_value_summable ha).sum_le_tsum _
        (fun j _ => mul_nonneg (DenseTruncation.h_nonneg _) (ha.1 j).1)
    _ = (A.card:ℝ)*((1/2:ℝ)*∑' j, DenseTruncation.h (j+1)*partnerAllocation d A j) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)

lemma finiteMean_rpow_le {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    finiteMean (fun ω => (f ω)^p) ≤ (finiteMean f)^p := by
  have hN : (0:ℝ) < Fintype.card Ω := Nat.cast_pos.mpr Fintype.card_pos
  have hh := (Real.concaveOn_rpow hp hp1).le_map_sum
    (t := Finset.univ) (w := fun _ : Ω => 1/(Fintype.card Ω:ℝ))
    (p := f) (fun _ _ => by positivity)
    (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; field_simp)
    (fun ω _ => hf ω)
  simpa only [smul_eq_mul,one_div,←Finset.mul_sum,mul_comm _ (∑ _ : Ω,_),
    ←div_eq_mul_inv,finiteMean] using hh

lemma finiteMean_exp_scale {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (a b t : ℝ) (hb : 0 < b) (ht : 0 ≤ t) (htb : t ≤ b)
    (h : finiteMean (fun ω => Real.exp (b*f ω)) ≤ Real.exp (b*a)) :
    finiteMean (fun ω => Real.exp (t*f ω)) ≤ Real.exp (t*a) := by
  have hp : 0 ≤ t/b := div_nonneg ht hb.le
  have hp1 : t/b ≤ 1 := (div_le_one hb).mpr htb
  have hh := (finiteMean_rpow_le (fun ω => Real.exp (b*f ω))
    (fun _ => (Real.exp_pos _).le) hp hp1).trans
      (Real.rpow_le_rpow (finiteMean_nonneg (fun _ => (Real.exp_pos _).le)) h hp)
  have he (x : ℝ) : (Real.exp (b*x))^(t/b) = Real.exp (t*x) := by
    rw [←Real.exp_mul]
    congr 1
    field_simp
  simpa only [he] using hh

lemma finiteMean_exp_sum_le {Ω I : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype I] [Nonempty I] (f : I → Ω → ℝ) (a : I → ℝ) (t : ℝ)
    (h : ∀ i, finiteMean (fun ω => Real.exp ((Fintype.card I:ℝ)*t*f i ω)) ≤
      Real.exp ((Fintype.card I:ℝ)*t*a i)) :
    finiteMean (fun ω => Real.exp (t*∑ i, f i ω)) ≤ Real.exp (t*∑ i, a i) := by
  have hN : (0:ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  let N : ℝ := Fintype.card I
  have hc (i : I) : finiteMean (fun ω => Real.exp (N*t*(f i ω-a i))) ≤ 1 := by
    have he (ω : Ω) : Real.exp (N*t*(f i ω-a i)) =
        Real.exp (N*t*f i ω) * Real.exp (-(N*t*a i)) := by
      rw [←Real.exp_add]; congr 1; ring
    simp_rw [he]
    rw [finiteMean_mul_const]
    calc
      _ ≤ Real.exp (N*t*a i)*Real.exp (-(N*t*a i)) :=
          mul_le_mul_of_nonneg_right (h i) (Real.exp_pos _).le
      _ = 1 := by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]
  have hj (ω : Ω) : Real.exp (t*(∑ i, (f i ω-a i))) ≤
      ∑ i, (1/N)*Real.exp (N*t*(f i ω-a i)) := by
    have hh := convexOn_exp.map_sum_le
      (t := Finset.univ) (w := fun _ : I => 1/N)
      (p := fun i => N*t*(f i ω-a i))
      (fun _ _ => by dsimp [N]; positivity)
      (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; dsimp [N]; field_simp)
      (fun _ _ => Set.mem_univ _)
    have he (i : I) : (1/N)*(N*t*(f i ω-a i)) = t*(f i ω-a i) := by
      dsimp [N]; field_simp
    simpa only [smul_eq_mul,he,←Finset.mul_sum] using hh
  have hm : finiteMean (fun ω => Real.exp (t*(∑ i, (f i ω-a i)))) ≤ 1 := by
    apply (finiteMean_mono hj).trans
    rw [finiteMean_sum]
    calc
      _ ≤ ∑ _ : I, 1/N := by
        apply Finset.sum_le_sum
        intro i _
        have he (ω : Ω) : 1/N*Real.exp (N*t*(f i ω-a i)) =
          Real.exp (N*t*(f i ω-a i))*(1/N) := mul_comm _ _
        simp_rw [he]
        rw [finiteMean_mul_const]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hc i)
          (by dsimp [N]; positivity : 0 ≤ 1/N)
      _ = 1 := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; dsimp [N]; field_simp
  have he (ω : Ω) : Real.exp (t*∑ i,f i ω) =
      Real.exp (t*(∑ i, (f i ω-a i)))*Real.exp (t*∑ i,a i) := by
    rw [←Real.exp_add,Finset.sum_sub_distrib]
    congr 1; ring
  simp_rw [he]
  rw [finiteMean_mul_const]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le


open Filter Topology

lemma dense_coefficient_hasDerivAt (j : ℕ) :
    HasDerivAt (fun t : ℝ => Real.exp (denseLevelCoefficient j t)-1)
      (DenseTruncation.h (j+1)) 0 := by
  have hp : (2:ℝ)^j ≠ 0 := by positivity
  have h₀ := (hasDerivAt_id (0:ℝ)).mul_const ((2:ℝ)^j)
  have h₁ := h₀.exp.sub_const 1
  have h₂ := h₁.div_const ((2:ℝ)^j)
  have hh := h₂.const_mul (DenseTruncation.h (j+1))
  simpa [denseLevelCoefficient, hp] using hh.exp.sub_const 1

lemma dense_coefficient_small (H : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1/500 ∧ ∀ j < H,
      Real.exp (denseLevelCoefficient j τ)-1 ≤ τ*(DenseTruncation.h (j+1)+δ) := by
  have hj (j : Fin H) : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (Real.exp (denseLevelCoefficient j t)-1)/t < DenseTruncation.h (j+1)+δ := by
    have hh := (dense_coefficient_hasDerivAt j).tendsto_slope_zero_right
    simp only [zero_add,denseLevelCoefficient,zero_mul,Real.exp_zero,sub_self,zero_div,
      mul_zero,smul_eq_mul,sub_zero] at hh
    have hh' : Tendsto (fun t : ℝ => (Real.exp (denseLevelCoefficient j t)-1)/t)
        (𝓝[>] 0) (𝓝 (DenseTruncation.h (j+1))) := by
      simpa only [denseLevelCoefficient,div_eq_mul_inv,mul_comm] using hh
    exact (tendsto_order.mp hh').2 _ (by linarith)
  have ha : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ j : Fin H,
      (Real.exp (denseLevelCoefficient j t)-1)/t < DenseTruncation.h (j+1)+δ :=
    Filter.eventually_all.mpr hj
  have hb : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1/500 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ) < 1/500)).filter_mono nhdsWithin_le_nhds
  have hc : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨τ,ht,hb,ha⟩ := (hc.and (hb.and ha)).exists
  refine ⟨τ,ht,hb.le,fun j hj => ?_⟩
  exact ((div_lt_iff₀ ht).mp (ha ⟨j,hj⟩)).le.trans_eq (mul_comm _ _)

lemma palindrome_level_dense_mgf_all (d j : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (t : ℝ) (ht : 0 ≤ t) :
    finiteMean (fun ω : BenesCoins d => Real.exp (t*palindromeLevelCost (j+1) d e ω)) ≤
      Real.exp ((Real.exp (denseLevelCoefficient j t)-1)*partnerMean d (Finset.univ.image e) j) := by
  classical
  by_cases hj : j < d
  · obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hj)
    rw [partnerMean_eq]
    exact palindrome_level_dense_mgf r j e t ht
  · simp only [palindromeLevelCost_gt (j+1) d (by omega) e, Nat.cast_zero,mul_zero,
      Real.exp_zero,finiteMean_const,partnerMean,dite_eq_right hj,le_refl]

lemma palindrome_low_dense_mgf (H : ℕ) (hH : 0 < H) (δ τ : ℝ) (hδ : 0 ≤ δ) (ht : 0 ≤ τ)
    (hτ : ∀ j < H, Real.exp (denseLevelCoefficient j τ)-1 ≤ τ*(DenseTruncation.h (j+1)+δ))
    (d : ℕ) {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (hι : 0 < Fintype.card ι) :
    finiteMean (fun ω : BenesCoins d => Real.exp ((τ/H)*palindromeLowCost H d e ω)) ≤
      Real.exp ((τ/H)*Fintype.card ι*
        (DenseTruncation.H ((Fintype.card ι:ℝ)/(2:ℝ)^d)+H*δ/2)) := by
  classical
  let A := Finset.univ.image e
  have hA : A.card = Fintype.card ι := by simp [A, Finset.card_image_of_injective _ e.injective]
  have hn : (H:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hH)
  have he : (H:ℝ)*(τ/H) = τ := by field_simp
  let : Nonempty (Fin H) := Fin.pos_iff_nonempty.mp hH
  have hh := finiteMean_exp_sum_le
    (fun j : Fin H => fun ω : BenesCoins d => (palindromeLevelCost (j+1) d e ω:ℝ))
    (fun j : Fin H => (DenseTruncation.h (j+1)+δ)*partnerMean d A j) (τ/H) (by
      intro j
      simp only [Fintype.card_fin,he]
      apply (palindrome_level_dense_mgf_all d j e τ ht).trans
      apply Real.exp_le_exp.mpr
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hτ j j.isLt)
        (partnerMean_nonneg d A j))
  have hsum : (∑ j : Fin H, (DenseTruncation.h (j+1)+δ)*partnerMean d A j) ≤
      Fintype.card ι*(DenseTruncation.H ((Fintype.card ι:ℝ)/(2:ℝ)^d)+H*δ/2) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => (DenseTruncation.h (j+1)+δ)*partnerMean d A j)]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    have hm := partner_weighted_sum_le d H A (by omega)
    rw [hA] at hm
    have hs : (∑ j ∈ Finset.range H, δ*partnerMean d A j) ≤ (H:ℝ)*δ*(Fintype.card ι)/2 := by
      calc
        _ ≤ ∑ _j ∈ Finset.range H, δ*((Fintype.card ι:ℝ)/2) := by
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_left _ hδ
          have hg := partnerMean_twice_le d A j
          rw [hA] at hg
          linarith
        _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring
    nlinarith
  have hh' := hh.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum (by positivity)))
  have hl (ω : BenesCoins d) :
      (∑ j : Fin H, (palindromeLevelCost (j+1) d e ω : ℝ)) =
        ∑ j ∈ Finset.range H, (palindromeLevelCost (j+1) d e ω : ℝ) :=
    Fin.sum_univ_eq_sum_range (fun j => (palindromeLevelCost (j+1) d e ω : ℝ)) H
  simpa only [palindromeLowCost_sum,Nat.cast_sum,hl,mul_assoc] using hh'


lemma heightDecay_tendsto : Tendsto heightDecay atTop (𝓝 0) := by
  have hr : 0 ≤ Real.exp (-(1:ℝ)/64) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(1:ℝ)/64) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hh := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).const_mul 68).div_const
    (1-Real.exp (-(1:ℝ)/64))
  have he (H : ℕ) : (Real.exp (-(1:ℝ)/64))^H = Real.exp (-(H:ℝ)/64) := by
    rw [←Real.exp_nat_mul]
    congr 1; ring
  change Tendsto (fun H : ℕ => 68*Real.exp (-(H:ℝ)/64)/(1-Real.exp (-(1:ℝ)/64))) _ _
  simpa only [he,mul_zero,zero_div] using hh

lemma heightDecay_exists {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℕ, 0 < H ∧ 500*heightDecay H < ε := by
  have hh := heightDecay_tendsto.const_mul 500
  simp only [mul_zero] at hh
  have he := (tendsto_order.mp hh).2 ε hε
  exact ((eventually_gt_atTop 0).and he).exists

lemma palindrome_high_exp_mgf (H n d : ℕ) (hH : 0 < H) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (t : ℝ) (ht : 0 ≤ t) (htb : t ≤ 1/500) :
    finiteMean (fun ω : BenesCoins d => Real.exp (t*
      (palindromeFamilyCost H n d e ω+palindromeFamilyCost (2*H) n d e ω))) ≤
      Real.exp (t*Fintype.card ι*(500*heightDecay H)) := by
  have hh := palindrome_high_full_mgf H n d hH e (Real.exp (1/500))
    (Real.one_le_exp_iff.mpr (by norm_num)) (by rw [Real.log_exp])
  have hp : finiteMean (fun ω : BenesCoins d => Real.exp ((1/500:ℝ)*
      (palindromeFamilyCost H n d e ω+palindromeFamilyCost (2*H) n d e ω))) ≤
      Real.exp ((1/500:ℝ)*(Fintype.card ι*(500*heightDecay H))) := by
    have he (k : ℕ) : (Real.exp (1/500:ℝ))^k = Real.exp ((1/500:ℝ)*k) := by
      rw [←Real.exp_nat_mul]; congr 1; ring
    simpa only [he,Nat.cast_add,show (1/500:ℝ)*(Fintype.card ι*(500*heightDecay H)) =
      Fintype.card ι*heightDecay H by ring] using hh
  have hs := finiteMean_exp_scale
    (fun ω : BenesCoins d => ((palindromeFamilyCost H n d e ω+
      palindromeFamilyCost (2*H) n d e ω):ℝ))
    (Fintype.card ι*(500*heightDecay H)) (1/500) t (by norm_num) ht htb
    (by simpa only [Nat.cast_add] using hp)
  simpa only [Nat.cast_add,mul_assoc] using hs

end Thorp

namespace Thorp.DenseTruncation

lemma harmonic_le_h (j : ℕ) :
    (harmonic (2^j):ℝ)/(2:ℝ)^j ≤ h (j+1) := by
  classical
  let M := 2^j
  have hM : 0 < M := by dsimp [M]; positivity
  have hM' : (0:ℝ) < M := Nat.cast_pos.mpr hM
  have hMc : (M:ℝ) = (2:ℝ)^j := by simp [M]
  let p : ℕ → ℝ := fun l => if l < M then 1/M else 0
  have hp : AdmissibleCycleLaw (j+1) p := by
    refine ⟨fun l => by dsimp [p]; split_ifs <;> positivity, ?_, ?_⟩
    · have hs : HasSum p (∑ l ∈ Finset.range M,p l) :=
        hasSum_sum_of_ne_finset_zero (s := Finset.range M) (f := p)
        (fun l hl => by simp only [Finset.mem_range] at hl; simp [p,hl])
      have he : (∑ l ∈ Finset.range M,p l) = 1 := by
        simp only [p]
        rw [Finset.sum_congr rfl (fun l hl => ite_eq_left (Finset.mem_range.mp hl))]
        simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
        field_simp
      exact he ▸ hs
    · intro l
      simp only [Nat.add_sub_cancel]
      by_cases hl : l < M
      · simp only [p,ite_eq_left hl,←hMc]
        apply div_le_div_of_nonneg_right _ hM'.le
        exact_mod_cast Nat.succ_pos l
      · simp only [p,ite_eq_right hl]
        positivity
  have he : (∑' l, p l / ((l+1:ℕ):ℝ)) = (harmonic M:ℝ)/(M:ℝ) := by
    rw [tsum_eq_sum (s := Finset.range M) (fun l hl => by
      simp only [Finset.mem_range] at hl; simp [p,hl])]
    simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l hl
    simp only [p,ite_eq_left (Finset.mem_range.mp hl)]
    ring
  have hh := reciprocal_le_h hp
  rw [he,hMc] at hh
  exact hh

lemma harmonic_lower (m : ℕ) (hm : 0 < m) :
    Real.log m+1/2 ≤ (harmonic m:ℝ) := by
  have hh := Real.one_half_lt_eulerMascheroniConstant.trans
    (Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' m)
  simp only [Real.eulerMascheroniSeq',ite_eq_right (ne_of_gt hm)] at hh
  linarith

lemma h_log_lower (j : ℕ) :
    ((j:ℝ)*Real.log 2+1/2)/(2:ℝ)^j ≤ h (j+1) := by
  have hh := harmonic_lower (2^j) (by positivity)
  rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] at hh
  exact (div_le_div_of_nonneg_right hh (by positivity)).trans (harmonic_le_h j)

noncomputable def unusedTail (d : ℕ) : ℝ :=
  (1/2:ℝ)*∑' j : ℕ, h (d+j+1)

lemma unusedTail_nonneg (d : ℕ) : 0 ≤ unusedTail d := by
  apply mul_nonneg (by norm_num)
  exact tsum_nonneg (fun j => h_nonneg _)

lemma unusedTail_lower (d : ℕ) :
    ((d+1:ℝ)*Real.log 2+1/2)/(2:ℝ)^d ≤ unusedTail d := by
  have hg := hasSum_geometric_of_norm_lt_one (show ‖(1/2:ℝ)‖ < 1 by norm_num)
  have hj := hasSum_coe_mul_geometric_of_norm_lt_one (show ‖(1/2:ℝ)‖ < 1 by norm_num)
  norm_num at hg hj
  have hs : HasSum (fun j : ℕ => (((d+j:ℕ):ℝ)*Real.log 2+1/2)/(2:ℝ)^(d+j))
      (2*((d+1:ℝ)*Real.log 2+1/2)/(2:ℝ)^d) := by
    convert! ((hg.mul_left ((d:ℝ)*Real.log 2+1/2)).add
      (hj.mul_left (Real.log 2))).div_const ((2:ℝ)^d) using 1
    · funext j
      simp only [Nat.cast_add,pow_add,div_pow,one_pow]
      ring
    · ring
  have hsum : Summable (fun j : ℕ => h (d+j+1)) := by
    simpa only [Nat.add_comm d] using (summable_nat_add_iff d).mpr h_summable
  have hh := hs.summable.tsum_le_tsum (fun j => h_log_lower (d+j)) hsum
  rw [hs.tsum_eq] at hh
  unfold unusedTail
  calc
    _ = (1/2:ℝ)*(2*((d+1:ℝ)*Real.log 2+1/2)/(2:ℝ)^d) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (by norm_num)

end Thorp.DenseTruncation

namespace Thorp

lemma partnerMean_budget_strong (d : ℕ) (A : Finset (Card d)) (hA : 0 < A.card) :
    2 * (∑ j ∈ Finset.range d, partnerMean d A j / (2:ℝ)^(j+1)) ≤
      (A.card:ℝ)*(A.card-1)/(2:ℝ)^d := by
  classical
  rw [←Fin.sum_univ_eq_sum_range]
  simp_rw [partnerMean_rate]
  rw [←Finset.sum_div]
  have he : (∑ j : Fin d, (separatedCount A j.rev:ℝ)) = ∑ j : Fin d, (separatedCount A j:ℝ) := by
    exact Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin d)) (fun j : Fin d => (separatedCount A j : ℝ))
  rw [he,←mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hh : (2:ℝ)*(∑ i : Fin d,(separatedCount A i:ℝ)) ≤
      (A.card:ℝ)*((A.card-1:ℕ):ℝ) := by exact_mod_cast separated_budget_strong A
  simpa only [Nat.cast_sub (show 1 ≤ A.card by omega),Nat.cast_one] using hh

lemma partnerAllocation_range_budget (d : ℕ) (A : Finset (Card d)) (hA : 0 < A.card) :
    (∑ j ∈ Finset.range d, partnerAllocation d A j/(2:ℝ)^(j+1)) ≤
      ((A.card:ℝ)-1)/(2:ℝ)^d := by
  have hp : (0:ℝ) < A.card := Nat.cast_pos.mpr hA
  have he (j : ℕ) : partnerAllocation d A j/(2:ℝ)^(j+1) =
      (2*partnerMean d A j/(2:ℝ)^(j+1))/A.card := by unfold partnerAllocation; ring
  simp_rw [he]
  rw [←Finset.sum_div]
  simp_rw [mul_div_assoc]
  rw [←Finset.mul_sum]
  apply (div_le_div_of_nonneg_right (partnerMean_budget_strong d A hA) hp.le).trans
  exact le_of_eq (by field_simp)

lemma dyadic_weights_hasSum (d : ℕ) :
    HasSum (fun j : ℕ => 1/(2:ℝ)^(d+j+1)) (1/(2:ℝ)^d) := by
  have hg := hasSum_geometric_of_norm_lt_one (show ‖(1/2:ℝ)‖ < 1 by norm_num)
  norm_num at hg
  convert! hg.div_const ((2:ℝ)^(d+1)) using 1
  · funext j
    simp only [pow_add,div_pow,one_pow,pow_one]
    ring
  · simp only [pow_succ]
    field_simp

noncomputable def augmentedAllocation (d : ℕ) (A : Finset (Card d)) (j : ℕ) : ℝ :=
  if j < d then partnerAllocation d A j else 1

lemma augmentedAllocation_bounds (d : ℕ) (A : Finset (Card d)) (hA : 0 < A.card) (j : ℕ) :
    0 ≤ augmentedAllocation d A j ∧ augmentedAllocation d A j ≤ 1 := by
  unfold augmentedAllocation
  split_ifs
  · exact (partnerAllocation_admissible d A hA).1 j
  · norm_num

lemma augmentedAllocation_admissible (d : ℕ) (A : Finset (Card d)) (hA : 0 < A.card) :
    DenseTruncation.AdmissibleAllocation ((A.card:ℝ)/(2:ℝ)^d) (augmentedAllocation d A) := by
  classical
  refine ⟨augmentedAllocation_bounds d A hA,?_⟩
  have hs : Summable (fun j => augmentedAllocation d A j/(2:ℝ)^(j+1)) := by
    apply Summable.of_nonneg_of_le (fun j => div_nonneg (augmentedAllocation_bounds d A hA j).1
      (by positivity)) (fun j => div_le_div_of_nonneg_right (augmentedAllocation_bounds d A hA j).2
      (by positivity))
    simpa only [Nat.zero_add] using (dyadic_weights_hasSum 0).summable
  have hh := hs.sum_add_tsum_nat_add d
  have ht : (∑' j, augmentedAllocation d A (j+d)/(2:ℝ)^(j+d+1)) = 1/(2:ℝ)^d := by
    have he (j : ℕ) : augmentedAllocation d A (j+d)/(2:ℝ)^(j+d+1) = 1/(2:ℝ)^(d+j+1) := by
      rw [augmentedAllocation,ite_eq_right (show ¬j+d<d by omega)]
      simp only [Nat.add_comm j d]
    simp_rw [he]
    exact (dyadic_weights_hasSum d).tsum_eq
  have hf : (∑ j ∈ Finset.range d, augmentedAllocation d A j/(2:ℝ)^(j+1)) =
      ∑ j ∈ Finset.range d, partnerAllocation d A j/(2:ℝ)^(j+1) := by
    exact Finset.sum_congr rfl (fun j hj => by rw [augmentedAllocation,ite_eq_left (Finset.mem_range.mp hj)])
  rw [←hh,ht,hf]
  apply (add_le_add (partnerAllocation_range_budget d A hA) (le_refl ((1:ℝ)/2^d))).trans
  exact le_of_eq (by ring)

lemma partner_weighted_sum_gap (d H : ℕ) (A : Finset (Card d)) (hA : 0 < A.card) :
    (∑ j ∈ Finset.range H, DenseTruncation.h (j+1)*partnerMean d A j) ≤
      A.card * (DenseTruncation.H ((A.card:ℝ)/(2:ℝ)^d)-DenseTruncation.unusedTail d) := by
  classical
  have ha := augmentedAllocation_admissible d A hA
  have hs := DenseTruncation.allocation_value_summable ha
  have HH := DenseTruncation.allocation_le_H ha
  have he := hs.sum_add_tsum_nat_add d
  have ht : (∑' j, DenseTruncation.h (j+d+1)*augmentedAllocation d A (j+d)) =
      ∑' j, DenseTruncation.h (d+j+1) := by
    congr 1
    funext j
    rw [augmentedAllocation,ite_eq_right (show ¬j+d<d by omega)]
    simp only [mul_one,Nat.add_comm j d]
  rw [←he,ht] at HH
  have hf : (∑ j ∈ Finset.range d, DenseTruncation.h (j+1)*augmentedAllocation d A j) =
      (2/(A.card:ℝ)) * ∑ j ∈ Finset.range d, DenseTruncation.h (j+1)*partnerMean d A j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [augmentedAllocation,ite_eq_left (Finset.mem_range.mp hj),partnerAllocation]
    ring
  rw [hf] at HH
  have hz (j : ℕ) (hj : j ∉ Finset.range d) :
      DenseTruncation.h (j+1)*partnerMean d A j = 0 := by
    have hj' : ¬j<d := by simpa only [Finset.mem_range] using hj
    simp only [partnerMean,dite_eq_right hj',mul_zero]
  have hsum : Summable (fun j => DenseTruncation.h (j+1)*partnerMean d A j) :=
    (hasSum_sum_of_ne_finset_zero hz : HasSum _
      (∑ j ∈ Finset.range d, DenseTruncation.h (j+1)*partnerMean d A j)).summable
  have hlow : (∑ j ∈ Finset.range H, DenseTruncation.h (j+1)*partnerMean d A j) ≤
      ∑ j ∈ Finset.range d, DenseTruncation.h (j+1)*partnerMean d A j := by
    calc
      _ ≤ ∑' j, DenseTruncation.h (j+1)*partnerMean d A j :=
        hsum.sum_le_tsum _ (fun j _ => mul_nonneg (DenseTruncation.h_nonneg _)
          (partnerMean_nonneg _ _ _))
      _ = _ := tsum_eq_sum hz
  have hp : (0:ℝ) < A.card := Nat.cast_pos.mpr hA
  have HH' := mul_le_mul_of_nonneg_left HH hp.le
  have HE : (A.card:ℝ)*((1/2:ℝ)*((2/(A.card:ℝ))*
      (∑ j ∈ Finset.range d, DenseTruncation.h (j+1)*partnerMean d A j)+
      ∑' j, DenseTruncation.h (d+j+1))) =
      (∑ j ∈ Finset.range d, DenseTruncation.h (j+1)*partnerMean d A j)+
      (A.card:ℝ)*((1/2:ℝ)*∑' j, DenseTruncation.h (d+j+1)) := by
    field_simp
  rw [HE] at HH'
  unfold DenseTruncation.unusedTail
  exact hlow.trans (by nlinarith [HH'])


lemma palindrome_low_dense_mgf_gap (H : ℕ) (hH : 0 < H) (δ τ : ℝ) (hδ : 0 ≤ δ) (ht : 0 ≤ τ)
    (hτ : ∀ j < H, Real.exp (denseLevelCoefficient j τ)-1 ≤ τ*(DenseTruncation.h (j+1)+δ))
    (d : ℕ) {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (hι : 0 < Fintype.card ι) :
    finiteMean (fun ω : BenesCoins d => Real.exp ((τ/H)*palindromeLowCost H d e ω)) ≤
      Real.exp ((τ/H)*Fintype.card ι*
        (DenseTruncation.H ((Fintype.card ι:ℝ)/(2:ℝ)^d)-DenseTruncation.unusedTail d+H*δ/2)) := by
  classical
  let A := Finset.univ.image e
  have hA : A.card = Fintype.card ι := by simp [A, Finset.card_image_of_injective _ e.injective]
  have hn : (H:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hH)
  have he : (H:ℝ)*(τ/H) = τ := by field_simp
  let : Nonempty (Fin H) := Fin.pos_iff_nonempty.mp hH
  have hh := finiteMean_exp_sum_le
    (fun j : Fin H => fun ω : BenesCoins d => (palindromeLevelCost (j+1) d e ω:ℝ))
    (fun j : Fin H => (DenseTruncation.h (j+1)+δ)*partnerMean d A j) (τ/H) (by
      intro j
      simp only [Fintype.card_fin,he]
      apply (palindrome_level_dense_mgf_all d j e τ ht).trans
      apply Real.exp_le_exp.mpr
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hτ j j.isLt)
        (partnerMean_nonneg d A j))
  have hsum : (∑ j : Fin H, (DenseTruncation.h (j+1)+δ)*partnerMean d A j) ≤
      Fintype.card ι*(DenseTruncation.H ((Fintype.card ι:ℝ)/(2:ℝ)^d)-DenseTruncation.unusedTail d+H*δ/2) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => (DenseTruncation.h (j+1)+δ)*partnerMean d A j)]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    have hm := partner_weighted_sum_gap d H A (by omega)
    rw [hA] at hm
    have hs : (∑ j ∈ Finset.range H, δ*partnerMean d A j) ≤ (H:ℝ)*δ*(Fintype.card ι)/2 := by
      calc
        _ ≤ ∑ _j ∈ Finset.range H, δ*((Fintype.card ι:ℝ)/2) := by
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_left _ hδ
          have hg := partnerMean_twice_le d A j
          rw [hA] at hg
          linarith
        _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring
    nlinarith
  have hh' := hh.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum (by positivity)))
  have hl (ω : BenesCoins d) :
      (∑ j : Fin H, (palindromeLevelCost (j+1) d e ω : ℝ)) =
        ∑ j ∈ Finset.range H, (palindromeLevelCost (j+1) d e ω : ℝ) :=
    Fin.sum_univ_eq_sum_range (fun j => (palindromeLevelCost (j+1) d e ω : ℝ)) H
  simpa only [palindromeLowCost_sum,Nat.cast_sum,hl,mul_assoc] using hh'


lemma palindrome_dense_mgf (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ ∀ d : ℕ, ∀ {ι : Type} [Fintype ι],
      ∀ e : ι ↪ Card d, 0 < Fintype.card ι →
      finiteMean (fun ω : BenesCoins d => Real.exp (t*palindromeCost d e ω)) ≤
        Real.exp (t*Fintype.card ι*(DenseTruncation.H ((Fintype.card ι:ℝ)/(2:ℝ)^d)-
          DenseTruncation.unusedTail d+ε)) := by
  obtain ⟨H,hH,hdecay⟩ := heightDecay_exists (show 0 < ε/2 by positivity)
  have hHr : (0:ℝ) < H := Nat.cast_pos.mpr hH
  let δ := ε/H
  have hδ : 0 < δ := div_pos hε hHr
  obtain ⟨τ,ht,hτb,hτ⟩ := dense_coefficient_small H δ hδ
  let t := (τ/H)/2
  have htp : 0 < t := by dsimp [t]; positivity
  have hσb : τ/H ≤ 1/500 := by
    apply (div_le_self ht.le (by exact_mod_cast hH)).trans hτb
  refine ⟨t,htp,?_⟩
  intro d ι _ e he
  have hlow := palindrome_low_dense_mgf_gap H hH δ τ hδ.le ht.le hτ d e he
  have hhigh := palindrome_high_exp_mgf H d d hH e (τ/H) (by positivity) hσb
  have hex (k : ℝ) : (Real.exp (t*k))^2 = Real.exp ((τ/H)*k) := by
    rw [←Real.exp_nat_mul]
    congr 1
    dsimp [t]
    ring
  have hh := finiteMean_mul_exp_le
    (fun ω : BenesCoins d => Real.exp (t*palindromeLowCost H d e ω))
    (fun ω : BenesCoins d => Real.exp (t*(palindromeFamilyCost H d d e ω+
      palindromeFamilyCost (2*H) d d e ω)))
    ((τ/H)*Fintype.card ι*(DenseTruncation.H ((Fintype.card ι:ℝ)/(2:ℝ)^d)-
      DenseTruncation.unusedTail d+H*δ/2))
    ((τ/H)*Fintype.card ι*(500*heightDecay H))
    (by simpa only [hex] using hlow)
    (by simpa only [hex,Nat.cast_add] using hhigh)
  have hd : d ≤ H*4^d := by
    have hg := pow_four_ge d
    nlinarith
  have hcost (ω : BenesCoins d) : palindromeCost d e ω = palindromeLowCost H d e ω+
      (palindromeFamilyCost H d d e ω+palindromeFamilyCost (2*H) d d e ω) := by
    have hc := palindromeCost_family H d d e ω
    rw [palindromeLowCost_eq _ _ hd] at hc
    simpa only [Nat.add_assoc] using hc.symm
  have hf (ω : BenesCoins d) : Real.exp (t*palindromeCost d e ω) =
      Real.exp (t*palindromeLowCost H d e ω)*
        Real.exp (t*(palindromeFamilyCost H d d e ω+palindromeFamilyCost (2*H) d d e ω)) := by
    rw [hcost,Nat.cast_add,Nat.cast_add,mul_add,Real.exp_add]
  simp_rw [←hf] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have heδ : (H:ℝ)*δ/2=ε/2 := by dsimp [δ]; field_simp
  rw [heδ]
  have hc : (ε/2+500*heightDecay H) ≤ ε := by linarith
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ t*(Fintype.card ι) by positivity)
  dsimp [t] at hm ⊢
  nlinarith [hm]

end Thorp

open scoped BigOperators
namespace Thorp.DenseTruncation

noncomputable def stirlingRemainder (n : ℕ) : ℝ :=
  Real.log (n.factorial:ℝ) - n*Real.log n+n

lemma stirlingRemainder_zero : stirlingRemainder 0 = 0 := by
  simp [stirlingRemainder]

lemma stirlingRemainder_step (n : ℕ) :
    stirlingRemainder (n+1)-stirlingRemainder n =
      1-(n:ℝ)*(Real.log (n+1)-Real.log n) := by
  have hn : (0:ℝ) < n+1 := by positivity
  have hf : (0:ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  rw [stirlingRemainder,stirlingRemainder,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
    Real.log_mul (ne_of_gt hn) (ne_of_gt hf)]
  ring

lemma log_increment_mul_monotone :
    Monotone (fun n : ℕ => (n:ℝ)*(Real.log (n+1)-Real.log n)) := by
  intro m n hmn
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hmn' : (m:ℝ) ≤ n := by exact_mod_cast hmn
  by_cases hm0 : m = 0
  · subst m
    simp only [Nat.cast_zero,zero_mul]
    by_cases hn0 : n = 0
    · simp [hn0]
    · have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
      exact mul_nonneg hn (sub_nonneg.mpr (Real.log_le_log hnpos (by linarith)))
  have hmpos : (0:ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hnpos : (0:ℝ) < n := lt_of_lt_of_le hmpos hmn'
  have ha : 0 ≤ (m:ℝ)/n := div_nonneg hm hn
  have hb : 0 ≤ 1-(m:ℝ)/n := by rw [sub_nonneg,div_le_one hnpos]; exact hmn'
  have hc := strictConcaveOn_log_Ioi.concaveOn.2
    (show (m+1:ℝ)/m ∈ Set.Ioi 0 by exact div_pos (by positivity) hmpos)
    (show (1:ℝ) ∈ Set.Ioi 0 by norm_num) ha hb
    (show (m:ℝ)/n+(1-(m:ℝ)/n) = 1 by ring)
  have he : (m:ℝ)/n*((m+1)/m)+(1-(m:ℝ)/n)*1 = (n+1)/n := by
    field_simp
    ring
  simp only [smul_eq_mul,Real.log_one,mul_zero,add_zero,he] at hc
  rw [Real.log_div (by positivity : (m+1:ℝ) ≠ 0) (ne_of_gt hmpos),
    Real.log_div (by positivity : (n+1:ℝ) ≠ 0) (ne_of_gt hnpos)] at hc
  have hc' := mul_le_mul_of_nonneg_left hc hn
  have he' : (n:ℝ)*((m:ℝ)/n*(Real.log (m+1)-Real.log m)) =
      m*(Real.log (m+1)-Real.log m) := by field_simp
  simpa only [he'] using hc'

lemma stirlingRemainder_increment_antitone :
    Antitone (fun n : ℕ => stirlingRemainder (n+1)-stirlingRemainder n) := by
  intro m n hmn
  simp only [stirlingRemainder_step]
  linarith [log_increment_mul_monotone hmn]

lemma stirlingRemainder_upper {n : ℕ} (hn : 0 < n) :
    stirlingRemainder n ≤ 1+Real.log n/2 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
  have hm : (0:ℝ) < m+1 := by positivity
  have he : Real.log (2*((m+1):ℝ)) = Real.log 2+Real.log (m+1) :=
    Real.log_mul (by norm_num) (ne_of_gt hm)
  have hh := Stirling.log_stirlingSeq'_antitone (show 0 ≤ m by omega)
  change Real.log (Stirling.stirlingSeq (m+1)) ≤ Real.log (Stirling.stirlingSeq 1) at hh
  rw [Stirling.log_stirlingSeq_formula,Stirling.log_stirlingSeq_formula] at hh
  simp only [Nat.cast_add,Nat.cast_one,he,Nat.factorial_one,Real.log_one,mul_one,
    Real.log_div (ne_of_gt hm) (ne_of_gt (Real.exp_pos 1)),Real.log_exp,
    Real.log_div (by norm_num : (1:ℝ) ≠ 0) (ne_of_gt (Real.exp_pos 1))] at hh
  dsimp [stirlingRemainder]
  push_cast
  linarith

lemma stirlingRemainder_sum (n : ℕ) :
    (∑ i ∈ Finset.range n, (stirlingRemainder (i+1)-stirlingRemainder i)) =
      stirlingRemainder n := by
  induction n with
  | zero => simp [stirlingRemainder_zero]
  | succ n ih => rw [Finset.sum_range_succ,ih]; ring

lemma stirlingRemainder_step_bound (n : ℕ) :
    (n:ℝ)*(stirlingRemainder (n+1)-stirlingRemainder n) ≤ stirlingRemainder n := by
  calc
    _ = ∑ _i ∈ Finset.range n, (stirlingRemainder (n+1)-stirlingRemainder n) := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    _ ≤ ∑ i ∈ Finset.range n, (stirlingRemainder (i+1)-stirlingRemainder i) := by
      exact Finset.sum_le_sum fun i hi => stirlingRemainder_increment_antitone
        (Nat.le_of_lt (Finset.mem_range.mp hi))
    _ = _ := stirlingRemainder_sum n

lemma stirlingRemainder_average_antitone :
    Antitone (fun n : ℕ => stirlingRemainder (n+1)/(n+1)) := by
  apply antitone_nat_of_succ_le
  intro n
  have h₁ : (0:ℝ) < n+1 := by positivity
  have h₂ : (0:ℝ) < n+1+1 := by positivity
  push_cast
  rw [div_le_div_iff₀ h₂ h₁]
  have hh := stirlingRemainder_step_bound (n+1)
  push_cast at hh ⊢
  nlinarith

lemma stirlingRemainder_difference_bound {n r : ℕ} (hn : 0 < n) (hr : r ≤ n) :
    stirlingRemainder n-stirlingRemainder (n-r) ≤ (r:ℝ)/n*stirlingRemainder n := by
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have he : (n-r:ℕ)+r=n := Nat.sub_add_cancel hr
  by_cases hm : n-r=0
  · have hn_eq : n=r := by omega
    subst n
    simp [stirlingRemainder_zero,div_self (ne_of_gt hn')]
  · obtain ⟨m,hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm
    obtain ⟨q,hq⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
    have hmq : m ≤ q := by omega
    have hh := stirlingRemainder_average_antitone hmq
    have hposm : (0:ℝ) < m+1 := by positivity
    have hposq : (0:ℝ) < q+1 := by positivity
    rw [div_le_div_iff₀ hposq hposm] at hh
    have he' : (m:ℝ)+1+r=q+1 := by exact_mod_cast (show m+1+r=q+1 by omega)
    rw [hm',hq]
    push_cast
    rw [div_mul_eq_mul_div,le_div_iff₀ hposq]
    simp only [Nat.succ_eq_add_one] at *
    have heq : (m:ℝ)+1 = (q+1:ℝ)-r := by linarith
    rw [heq] at hh
    nlinarith

lemma stirlingRemainder_dyadic (d : ℕ) (hd : 1 ≤ d) :
    stirlingRemainder (2^d)/Real.log 2 ≤ (d+1:ℝ)*Real.log 2+1/2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : (6931/10000:ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  rw [div_le_iff₀ hl]
  by_cases hd1 : d=1
  · subst d
    norm_num [stirlingRemainder]
    nlinarith [sq_nonneg (Real.log 2-6931/10000)]
  · have hd2 : (2:ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by omega)
    have hh := stirlingRemainder_upper (n := 2^d) (by positivity)
    rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] at hh
    have hq : 0 ≤ Real.log 2*Real.log 2-Real.log 2/2 := by
      nlinarith [sq_nonneg (Real.log 2-6931/10000)]
    have hprod := mul_nonneg (sub_nonneg.mpr hd2) hq
    nlinarith [sq_nonneg (Real.log 2-6931/10000)]

lemma factorial_error_identity {n r : ℕ} (hn : 0 < n) (hr : r ≤ n) :
    Real.log ((n.descFactorial r:ℝ)/(n:ℝ)^r) =
      stirlingRemainder n-stirlingRemainder (n-r)-(r:ℝ)-
        (n-r:ℕ)*Real.log (1-(r:ℝ)/n) := by
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hm : (0:ℝ) < (n-r).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hd : (0:ℝ) < n.descFactorial r := Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr hr)
  have hf : ((n-r).factorial:ℝ)*(n.descFactorial r:ℝ) = n.factorial :=
    by exact_mod_cast Nat.factorial_mul_descFactorial hr
  have hh := congrArg Real.log hf
  rw [Real.log_mul (ne_of_gt hm) (ne_of_gt hd)] at hh
  rw [Real.log_div (ne_of_gt hd) (ne_of_gt (pow_pos hn' r)),Real.log_pow]
  unfold stirlingRemainder
  by_cases hz : n-r=0
  · have hrn : r=n := by omega
    subst r
    simp only [Nat.sub_self,Nat.factorial_zero,Nat.cast_one,Real.log_one,Nat.cast_zero,
      zero_mul,add_zero,sub_zero,Nat.descFactorial_self]
    ring
  · have hm' : (0:ℝ) < (n-r:ℕ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)
    have he : ((n-r:ℕ):ℝ) = (n:ℝ)*(1-(r:ℝ)/n) := by
      rw [Nat.cast_sub hr]
      field_simp
    have hρ : 0 < 1-(r:ℝ)/n := by
      rw [←mul_pos_iff_of_pos_left hn',←he]
      exact hm'
    have hl : Real.log ((n-r:ℕ):ℝ) = Real.log n+Real.log (1-(r:ℝ)/n) := by
      rw [he, Real.log_mul (ne_of_gt hn') (ne_of_gt hρ)]
    rw [hl,Nat.cast_sub hr]
    nlinarith [hh]


lemma normalization_le (d r : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r) (hrn : r ≤ 2^d) :
    Real.log (((2^d).descFactorial r:ℝ)/((2:ℝ)^d)^r)/Real.log 2 ≤
      (r:ℝ)*(entropyCorrection ((r:ℝ)/(2:ℝ)^d)+unusedTail d) := by
  have hnp : 0 < (2:ℕ)^d := by positivity
  have hnr : (0:ℝ) < (2:ℝ)^d := by positivity
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh := stirlingRemainder_difference_bound hnp hrn
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hh
  have hg := (stirlingRemainder_dyadic d hd).trans
    ((div_le_iff₀ hnr).mp (unusedTail_lower d))
  have he : (stirlingRemainder (2^d)-stirlingRemainder (2^d-r))/Real.log 2 ≤
      (r:ℝ)*unusedTail d := by
    calc
      _ ≤ ((r:ℝ)/(2:ℝ)^d*stirlingRemainder (2^d))/Real.log 2 :=
        div_le_div_of_nonneg_right hh hl.le
      _ = ((r:ℝ)/(2:ℝ)^d)*(stirlingRemainder (2^d)/Real.log 2) := by ring
      _ ≤ ((r:ℝ)/(2:ℝ)^d)*(unusedTail d*(2:ℝ)^d) :=
        mul_le_mul_of_nonneg_left hg (by positivity)
      _ = _ := by field_simp
  have hid := factorial_error_identity hnp hrn
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hid
  have heq : Real.log (((2^d).descFactorial r:ℝ)/((2:ℝ)^d)^r)/Real.log 2 =
      (r:ℝ)*entropyCorrection ((r:ℝ)/(2:ℝ)^d)+
      (stirlingRemainder (2^d)-stirlingRemainder (2^d-r))/Real.log 2 := by
    rw [hid,entropyCorrection,Nat.cast_sub hrn]
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    field_simp
    ring
  rw [heq]
  nlinarith


theorem dense_truncation : MainStatement := by
  classical
  intro ρ hρ ε hε
  obtain ⟨t,ht,hm⟩ := palindrome_dense_mgf (ε/2) (by positivity)
  refine ⟨t*ε/2, by positivity, ?_⟩
  intro d r hd hr hρr x
  have hrn : r ≤ 2^d := by
    have hh := Fintype.card_le_of_injective x x.injective
    simpa only [Fintype.card_fin,card_positions] using hh
  have hm' := hm d x (by simpa only [Fintype.card_fin] using (show 0 < r by omega))
  simp only [Fintype.card_fin,hρr] at hm'
  have hn := normalization_le d r hd hr hrn
  rw [hρr] at hn
  let a : ℝ := r*(H ρ+entropyCorrection ρ+ε)
  let b : ℝ := Real.log (((2^d).descFactorial r:ℝ)/((2:ℝ)^d)^r)/Real.log 2
  have hp (ω : BenesCoins d) :
      (if a < densityExponent d r x ω then (1:ℝ) else 0) ≤
      Real.exp (t*palindromeCost d x ω)*Real.exp (t*(b-a)) := by
    split_ifs with h
    · rw [←Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      have hh : 0 ≤ t*((palindromeCost d x ω:ℝ)+b-a) := by
        apply mul_nonneg ht.le
        exact sub_nonneg.mpr (le_of_lt h)
      nlinarith
    · positivity
  have he : t*(r:ℝ)*(H ρ-unusedTail d+ε/2)+t*(b-a) ≤ -(t*ε/2)*r := by
    have hh := mul_le_mul_of_nonneg_left hn ht.le
    dsimp [b,a]
    nlinarith [hh]
  calc
    _ ≤ finiteMean (fun ω : BenesCoins d =>
        Real.exp (t*palindromeCost d x ω)*Real.exp (t*(b-a))) := finiteMean_mono hp
    _ = finiteMean (fun ω : BenesCoins d => Real.exp (t*palindromeCost d x ω))*
        Real.exp (t*(b-a)) := finiteMean_mul_const _ _
    _ ≤ Real.exp (t*(r:ℝ)*(H ρ-unusedTail d+ε/2))*Real.exp (t*(b-a)) :=
      mul_le_mul_of_nonneg_right hm' (Real.exp_nonneg _)
    _ ≤ Real.exp (-(t*ε/2)*r) := by rw [←Real.exp_add]; exact Real.exp_le_exp.mpr he

end Thorp.DenseTruncation

end ThorpNine.Dense

end OAI
