import OAI.NumberTheory.Ostmann.Arithmetic.PrimeSquareLiftFamilies

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryPairSquareProbability

def probability {α : Type*} [Fintype α] (P : α→Prop) : ℝ :=
  ((Finset.univ.filter P).card:ℝ)/Fintype.card α

def Base {ι : Type*} (p : ℕ) (s : Finset ι) (A B : ι→ℤ) (X Y : ℤ) : Prop :=
  ∀i∈s,(p:ℤ)∣A i*X+B i*Y

def Good {ι : Type*} (p : ℕ) (s : Finset ι) (A B : ι→ℤ) (X Y : ℤ) : Prop :=
  Base p s A B X Y ∧ ∀i∈s,¬(p:ℤ)^2∣A i*X+B i*Y

lemma base_lift_iff {ι : Type*} (p : ℕ) (s : Finset ι) (A B : ι→ℤ)
    (X Y u v : ℤ) :
    Base p s A B (X+(p:ℤ)*u) (Y+(p:ℤ)*v)↔Base p s A B X Y := by
  unfold Base
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  have he : A i*(X+(p:ℤ)*u)+B i*(Y+(p:ℤ)*v)=
      (A i*X+B i*Y)+(p:ℤ)*(A i*u+B i*v) := by ring
  rw [he]
  have hd := dvd_mul_right (p:ℤ) (A i*u+B i*v)
  constructor
  · intro hh
    simpa only [add_sub_cancel_right] using dvd_sub hh hd
  · intro hh
    exact dvd_add hh hd

lemma good_lift_iff {ι : Type*} (p : ℕ) [Fact p.Prime] (s : Finset ι) (A B : ι→ℤ)
    (X Y : ℤ) (z : ZMod p×ZMod p) :
    Good p s A B (X+(p:ℤ)*(z.1.val:ℤ)) (Y+(p:ℤ)*(z.2.val:ℤ))↔
      Base p s A B X Y ∧ z∉PrimeSquareLiftFamilies.integerBadLifts p s A B X Y := by
  simp only [Good,base_lift_iff,PrimeSquareLiftFamilies.integerBadLifts,
    Finset.mem_filter,Finset.mem_univ,true_and,not_exists,not_and,pow_two]

theorem conditional_lift_loss {ι : Type*} (p : ℕ) [Fact p.Prime]
    (s : Finset ι) (A B : ι→ℤ) (X Y : ℤ)
    (hrow : ∀i∈s,(A i:ZMod p)≠0 ∨ (B i:ZMod p)≠0) :
    0≤(if Base p s A B X Y then (1:ℝ) else 0)-
      probability (fun z : ZMod p×ZMod p =>
        Good p s A B (X+(p:ℤ)*(z.1.val:ℤ)) (Y+(p:ℤ)*(z.2.val:ℤ))) ∧
    (if Base p s A B X Y then (1:ℝ) else 0)-
      probability (fun z : ZMod p×ZMod p =>
        Good p s A B (X+(p:ℤ)*(z.1.val:ℤ)) (Y+(p:ℤ)*(z.2.val:ℤ)))≤
      ((s.card:ℝ)/p)*(if Base p s A B X Y then (1:ℝ) else 0) := by
  by_cases hb : Base p s A B X Y
  · let bad := PrimeSquareLiftFamilies.integerBadLifts p s A B X Y
    have he : Finset.univ.filter (fun z : ZMod p×ZMod p =>
        Good p s A B (X+(p:ℤ)*(z.1.val:ℤ)) (Y+(p:ℤ)*(z.2.val:ℤ)))=badᶜ := by
      ext z
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,good_lift_iff,hb,true_and,
        Finset.mem_compl,bad]
    have ht : (0:ℝ)<Fintype.card (ZMod p×ZMod p) := by positivity
    have hc : ((badᶜ).card:ℝ)+(bad.card:ℝ)=Fintype.card (ZMod p×ZMod p) := by
      exact_mod_cast Finset.card_compl_add_card bad
    have hprob : ((badᶜ).card:ℝ)/Fintype.card (ZMod p×ZMod p)+
        (bad.card:ℝ)/Fintype.card (ZMod p×ZMod p)=1 := by
      rw [←add_div,hc,div_self ht.ne']
    have hcarry : ∀i∈s,A i*X+B i*Y=(p:ℤ)*((A i*X+B i*Y)/(p:ℤ)) := by
      intro i hi
      exact (Int.mul_ediv_cancel' (hb i hi)).symm
    have hbad := PrimeSquareLiftFamilies.integer_bad_lift_probability_le p s A B
      (fun i => (A i*X+B i*Y)/(p:ℤ)) X Y hcarry hrow
    have hn : (0:ℝ)≤(bad.card:ℝ)/Fintype.card (ZMod p×ZMod p) := by positivity
    simp only [hb,ite_true,probability,he,mul_one]
    constructor <;> dsimp only [bad] at * <;> linarith
  · have he : ∀z : ZMod p×ZMod p,
        ¬Good p s A B (X+(p:ℤ)*(z.1.val:ℤ)) (Y+(p:ℤ)*(z.2.val:ℤ)) := by
      intro z hz
      exact hb ((good_lift_iff p s A B X Y z).mp hz).1
    have hf : Finset.univ.filter (fun z : ZMod p×ZMod p =>
        Good p s A B (X+(p:ℤ)*(z.1.val:ℤ)) (Y+(p:ℤ)*(z.2.val:ℤ)))=∅ :=
      Finset.filter_eq_empty_iff.mpr (fun z _ => he z)
    simp only [ite_eq_right hb,probability,hf,Finset.card_empty,Nat.cast_zero,zero_div,
      sub_self,mul_zero,le_refl,and_self]

end Ostmann.Arithmetic.HistoryPairSquareProbability

end

end OAI
