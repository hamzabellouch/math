import OAI.Combinatorics.HadwigerCounterexample.InformationSmallSetBounds

namespace OAI

/-! # Refinement Energy -/

noncomputable section
namespace HadwigerCounterexample
open Finset Filter Real
open scoped BigOperators
variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

theorem var_nonneg (p q : Wgt A) : 0≤ varOne p q := Finset.sum_nonneg fun _ _ => abs_nonneg _
theorem var_tri (p q r : Wgt A) :
    varOne p q≤varOne p r+varOne r q := by
  unfold varOne; rw [← Finset.sum_add_distrib]; exact sum_le_sum fun i _ => abs_sub_le _ _ _

theorem var_pr (p q : Wgt A) (P : A→Prop) :
    pr p P-pr q P ≤ varOne p q := by
  unfold pr avg varOne
  rw [← Finset.sum_sub_distrib]
  refine sum_le_sum fun i _ => ?_
  by_cases h : P i
  · simp only [ind_one h,mul_one]; exact le_abs_self _
  simp only [ind_zero h,mul_zero,sub_zero]; exact abs_nonneg _

theorem var_event (p q : Wgt A) (h : tot p=tot q) :
    let P := fun i => q i<p i
    varOne p q=2*(pr p P-pr q P) := by
  intro P
  have hi (i:A) : |p i-q i|=
      2*(p i*ind (P i)-q i*ind (P i))+q i-p i := by
    by_cases h : P i
    · rw [ind_one h,abs_of_pos (sub_pos.mpr h)]; ring
    rw [ind_zero h,abs_of_nonpos (sub_nonpos.mpr (le_of_not_gt h))]; ring
  unfold varOne pr avg
  simp_rw [hi,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    Finset.sum_sub_distrib]
  rw [show ∑ i,q i=∑ i,p i from h.symm]; ring

theorem var_mix {μ : Wgt A} (p q : A→Wgt B) (hμ : ∀ i,0≤μ i) :
    varOne (mixW μ p) (mixW μ q) ≤ avg μ (fun i => varOne (p i) (q i)) := by
  unfold varOne mixW
  rw [avg_sum]
  simp_rw [←avg_sub]; exact sum_le_sum fun i _ => abs_avg_le hμ

omit [Fintype D] in
theorem bucket_m (μ : Wgt A) (p : A → Wgt B) (f : B→C) (g : C→D) :
    mapW (bucket unif (g∘f) (mixW μ p)) f =
      mixW μ (fun x => bucket (mapW unif f) g (mapW (p x) f)) := by
  rw [bucket_mix,map_mix]
  simp only [bucket_nested]

variable {μ : Wgt A} {p : A→Wgt B}

theorem tariffs_monotone {r s : ℕ} {a b V : ℝ} (h : tariffs μ p r a V)
    (hrs : s≤r) (hb : a ≤ b) : tariffs μ p s b V :=
  fun C _ hC f hf => h C (hC.trans hrs) f (fun _ hi => hb.trans (hf _ hi))

theorem budget_nonneg [Nonempty B] (h : Ultra μ p) (f : B→ C) :
    0≤budget μ p f := by
  have h0 {p : Wgt B} : lsupp p unif := fun i _ => by rw [unif_apply]; positivity
  have hv : IsLaw (mapW unif f) := mapW_law unif_law f
  exact avg_nonneg h.law.nz (fun i => tension_nonneg (mapW_law (h.labs i) f) hv
    (lsupp.map h0 unif_law.nz f))

set_option maxHeartbeats 800000 in
theorem budget_progress [Nonempty B] (h : Ultra μ p) (w : Wgt B)
    (hw : catalog μ p w) (f : B→C) (g : C→D) :
    varOne (mapW w f) (mapW (bucket unif (g∘f) w) f) ^ 2 ≤
      (budget μ p f-budget μ p (g∘f))*4 := by
  classical
  let q := mapW unif f
  let Q (i : A) := mapW (p i) f
  let R (i : A) := bucket q g (Q i)
  have hu : IsLaw q := mapW_law unif_law f
  have hQ (i) : IsLaw (Q i) := mapW_law (h.labs i) f
  have he (i) : lsupp (Q i) q := lsupp.map
    (p:=p i) (q:=unif) (fun i _ => by rw [unif_apply]; positivity) unif_law.nz f
  have hp (i : A) :
      varOne (Q i) (R i) ^ 2 ≤ tension (Q i) (R i) *4 :=
    var_tension _ _ (hQ i) (bucket_law (hQ i) g hu.nz (he i))
      (lsupp_bucket g (hQ i).nz hu.nz (he i))
  have hn :
      budget μ p f=avg μ (fun i => tension (Q i) (R i))+budget μ p (g∘f) := by
    unfold budget
    have hi := fun i : A => tension_stage (Q i) q (hQ i).nz hu.nz (he i) g
    unfold Q q at hi
    simp_rw [map_nested] at hi
    rw [← avg_add]; exact avg_congr fun i _ => hi i
  let Z (i : A) := varOne (Q i) (R i)
  have hs : avg μ Z ^ 2 ≤ avg μ (fun i => Z i ^ 2) := by
    have hh := avg_CS h.law.nz Z (fun _ => 1)
    simp only [mul_one,one_pow,h.law.avg_const] at hh; exact hh
  obtain ⟨s,hs',ht,rfl⟩ := hw
  rw [bucket_m,map_mix]
  have h' := (var_mix Q R hs').trans (avg_mono_left (fun i => var_nonneg ..) ht)
  refine (pow_le_pow_left₀ (var_nonneg ..) h' 2).trans (hs.trans ?_)
  have hz := avg_mono h.law.nz hp; rw [avg_mul] at hz
  rw [hn]; exact hz.trans_eq (by ring)
end HadwigerCounterexample

end

end OAI
