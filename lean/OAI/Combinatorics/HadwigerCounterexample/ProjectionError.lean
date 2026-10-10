import OAI.Combinatorics.HadwigerCounterexample.ResidualRegularity

namespace OAI

/-! # Projection Error -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix LinearMap Module Filter Function
open scoped BigOperators
variable {A B I : Type} [Fintype A] [Fintype B] [Fintype I]

def rebate (u f g : Wgt A) (p : A→B) :=
  dip u f g - dip u (banner u p f) (banner u p g)
omit [Fintype B] in
theorem rebate_sym (u f g : Wgt A) (p : A→B) :
    rebate u f g p=rebate u g f p := by unfold rebate; rw [dip_sym u f,dip_sym u (banner u p f)]
theorem rebate_calc (u f g : Wgt A) (p : A→B) (hu : ∀ i,0≤u i) :
    rebate u f g p=dip u (fun i=>f i-banner u p f i) g := by
  unfold rebate
  rw [dip_sub,dip_sym u (banner u p f) (banner u p g)]
  exact congrArg (dip u f g - ·) ((show dip u (banner u p g) (banner u p f)=dip u g (banner u p f) from
    cash_orth u hu p g (cashbook u p f)).trans (dip_sym ..))
def lcost (u f g : Wgt A) := avg u (fun i=>|f i-g i|)

theorem rebate_cost (u f g f' : Wgt A) (p : A→B) (hu : ∀ i,0≤u i)
    (r : ℝ) (hr : 0 ≤ r) (h : ∀ i,|g i|≤r) :
    |rebate u f g p-rebate u f' g p| ≤ lcost u f f' * (2*r) := by
  rw [rebate_sym u f g,rebate_sym u f' g,rebate_calc u g f p hu,rebate_calc u g f' p hu]
  unfold dip; rw [←avg_sub]
  apply (abs_avg_le hu).trans
  have hz i : |g i-banner u p g i|≤2*r :=
    ((abs_sub ..).trans (add_le_add (h i) (cashbook_bound u hu p g r hr h (p i)))).trans_eq
      (two_mul _).symm
  unfold lcost; rw [←avg_mul]; apply avg_mono hu
  intro i
  dsimp only
  rw [←mul_sub,abs_mul,mul_comm]
  exact mul_le_mul_of_nonneg_left (hz _) (abs_nonneg _)

def syrup (r : ℝ) (x : ℝ) := min (max x 0) r
def mcut (r : ℝ) (u : Wgt A) (f : Wgt A) := syrup r ∘ density u f
theorem syrup_range (r x : ℝ) (h : 0≤r) :
    0≤ syrup r x∧ syrup r x ≤ r := ⟨le_min (le_max_right ..) h,min_le_right ..⟩
omit [Fintype A] in
theorem mcut_range (r : ℝ) (u f : Wgt A) (h : 0≤r) (x) :
    0≤mcut r u f x∧mcut r u f x ≤ r := syrup_range _ _ h

private theorem jelly (r x y : ℝ) :
    |syrup r x-syrup r y| ≤ |x-y| := by
  wlog hh : x≤y generalizing x y
  · rw [abs_sub_comm,abs_sub_comm x y]; exact this y x (le_of_not_ge hh)
  have hr : syrup r x ≤ syrup r y := min_le_min (max_le_max hh le_rfl) le_rfl
  rw [abs_of_nonpos (sub_nonpos.mpr hh),abs_of_nonpos (sub_nonpos.mpr hr)]
  unfold syrup
  rcases le_total x 0 with h|h <;> rcases le_total y 0 with he|he
  · rw [max_eq_right h,max_eq_right he]; linarith only [hh]
  · rw [max_eq_right h,max_eq_left he]; rcases le_total 0 r with h'|h'
    · rw [min_eq_left h']
      linarith only [h, min_le_left y r]
    rw [min_eq_right h',min_eq_right (by linarith)]
    linarith
  · obtain rfl : x=y := by linarith
    simp
  rw [max_eq_left h,max_eq_left he]
  rcases le_total x r with h'|h'
  · rw [min_eq_left h']; linarith only [min_le_left y r]
  rw [min_eq_right h',min_eq_right (by linarith)]; linarith

theorem mcut_cost (r : ℝ) (u f g : Wgt A) (hu : ∀ i,0≤u i) :
    lcost u (mcut r u f) (mcut r u g)≤ varOne f g := by
  unfold lcost avg varOne; refine sum_le_sum fun i _ => ?_
  apply (mul_le_mul_of_nonneg_left (jelly r (density u f i) (density u g i)) (hu i)).trans
  by_cases hx : u i=0
  · rw [hx,zero_mul]; exact abs_nonneg _
  unfold density; rw [←sub_div,abs_div,abs_of_nonneg (hu _)]
  exact le_of_eq (by field_simp)

set_option maxHeartbeats 500000 in
theorem roster_clip (r : ℝ) (u : Wgt A) (hu : IsLaw u) (hr : 0≤r) (Q : Wgt A→ Prop)
    (k : ℕ) (ε : ℝ) (h : roster Q k ε) :
    ∃ f : Fin (k+1)→Wgt A,(∀ i x,|f i x|≤r) ∧
      ∀ w,Q w→∃ i,lcost u (mcut r u w) (f i)≤ ε := by
  classical
  obtain ⟨t,ht,v,hv⟩:=h
  let W:= fun i : Fin (k+1)=> if h:i.val<t then mcut r u (v (⟨i.val,h⟩)) else (fun i:A => 0)
  refine ⟨W,fun i x=>?_,fun i hi=>?_⟩
  · unfold W; split
    next h =>
      obtain ⟨he,hy⟩:=mcut_range r u (v (⟨i.val,h⟩)) hr x
      rwa [abs_of_nonneg he]
    simpa only [abs_zero] using hr
  obtain ⟨j,hj⟩:=hv i hi
  exact ⟨⟨j.val,Nat.lt_succ_of_lt (j.isLt.trans_le ht)⟩,by
    unfold W; rw [dite_eq_left j.isLt]; exact (mcut_cost r u i _ hu.nz).trans hj⟩
end HadwigerCounterexample

end

end OAI
