import OAI.Combinatorics.HadwigerCounterexample.ConditionalFlags

namespace OAI

/-! # Restricted Comparison Laws -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]

def hung (Q : Wgt B→Prop) (P : B→Prop) (w : Wgt B) :=
  ∃ v : Wgt B, Q v ∧ w=subW v P
def smallSet (Q : Wgt B→Prop) (q : Wgt B) (δ η : ℝ) :=
  ∀ p,Q p → ∀ P : B→ Prop, pr q P ≤ δ → pr p P ≤ η
def rosterTail (Q : Wgt B→Prop) (q : Wgt B) (R η : ℝ) :=
  ∀ p,Q p → pr p (fun x => R≤density q p x)≤η

theorem hung_roster (Q : Wgt B → Prop) (P : B→Prop) (r : ℕ) (ε : ℝ) :
    roster Q r ε → roster (hung Q P) r ε := by
  classical
  rintro ⟨t,ht,w,hw⟩
  refine ⟨t,ht,fun i => subW (w i) P,?_⟩
  rintro p ⟨v,h,rfl⟩
  obtain ⟨i,hi⟩ := hw v h
  refine ⟨i,le_trans ?_ hi⟩
  unfold varOne subW
  refine sum_le_sum fun x _ => ?_
  by_cases h : P x <;> simp [ind,h]

variable [Nonempty B]

theorem hung_small (Q : Wgt B→Prop) (P : B→Prop) (δ η : ℝ)
    (hq : smallSet Q unif δ η) : smallSet (hung Q P) (unifOn P) δ η := by
  classical
  rintro p ⟨v,hv,rfl⟩ S hs
  rw [pr_sub]
  refine hq v hv (fun x => P x∧ S x) ?_
  rw [pr_of_on unif_law.nz,on_unif]
  refine le_trans ?_ hs
  have ht := (pr_le_tot (α:=B) (p:=P) unif_law.nz).trans unif_law.total.le
  exact (mul_le_mul_of_nonneg_right ht (pr_nonneg (unifOn_sub _).nz)).trans_eq (one_mul _)

omit [Nonempty B] in
theorem density_hung (P : B→Prop) (w : Wgt B) (hw : carried w P) :
    ∀ i, unifOn P i * density (unifOn P) w i=w i := by
  classical
  intro i
  by_cases h : w i =0
  · simp only [density,h,zero_div,mul_zero]
  have ht : P i := not_not.mp fun hi => h (hw i hi)
  have hn := unifOn_law (p:=P) ⟨i,ht⟩
  have he : unifOn P i≠0 := by
    rw [unifOn_val,ind_one ht]
    have hh : nbr P ≠0 := by
      have he := weight_le_tot (fun j => ind_nonneg (P j)) i
      rw [ind_one ht] at he
      exact (lt_of_lt_of_le zero_lt_one he).ne'
    exact div_ne_zero one_ne_zero hh
  unfold density; field_simp

theorem hung_tail (Q : Wgt B→Prop) (P : B→ Prop)
    (h : ∀ p,Q p → SubLaw p) (δ η : ℝ)
    (hδ : 0<δ) (hh : smallSet Q unif δ η) :
    rosterTail (hung Q P) (unifOn P) δ⁻¹ η := by
  intro p hp
  apply hung_small Q P δ η hh p hp
  obtain ⟨w,hw,rfl⟩ := hp
  let q := unifOn P
  let v := subW w P
  let f := density q v
  have hq := unifOn_sub P
  have hv := subLaw_sub (h w hw) P
  have hh :
      avg q f = tot v := Finset.sum_congr rfl fun i _ => density_hung P v
        (subW_carried w P) i
  have hz := le_avg_markov hq.nz (fun i => div_nonneg (hv.nz i) (hq.nz i)) δ⁻¹
  change δ⁻¹*pr q _≤avg q f at hz
  apply le_of_mul_le_mul_left _ (inv_pos_of_pos hδ)
  rw [inv_mul_cancel₀ hδ.ne']
  exact (hz.trans_eq hh).trans hv.total

omit [Nonempty B] in
theorem hung_var (P : B→Prop) (p q : Wgt B) (hp : carried p P) (hq : carried q P) :
    avg (unifOn P) (fun i => |density (unifOn P) p i-density (unifOn P) q i|)=varOne p q := by
  classical
  unfold avg varOne
  refine sum_congr rfl fun i _ => ?_
  rw [←abs_of_nonneg ((unifOn_sub P).nz i)]
  have he := density_hung P p hp i

  simp_rw [abs_of_nonneg ((unifOn_sub P).nz i)]
  calc _ = |unifOn P i * (density (unifOn P) p i - density (unifOn P) q i)| :=
                 by rw [abs_mul,abs_of_nonneg ((unifOn_sub P).nz i)]
       _ = _ := by rw [mul_sub,he,density_hung P q hq i]
end HadwigerCounterexample

end

end OAI
