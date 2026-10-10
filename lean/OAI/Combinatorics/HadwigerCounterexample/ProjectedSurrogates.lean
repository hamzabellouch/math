import OAI.Combinatorics.HadwigerCounterexample.CommonPartitions

namespace OAI

/-! # Projected Surrogates -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Function
open scoped BigOperators
variable {A B I J : Type} [Fintype A] [Fintype B] [Fintype I] [Fintype J]

def bower (f : Wgt A) := (∀ i,0≤ f i)∧ (∀ i,f i≤1)
omit [Fintype B] in
theorem book_order (w : Wgt A) (p : A→ B) (hw : IsLaw w)
    (f g : Wgt A) (h : ∀ i, f i≤ g i) (x) :
    cashbook w p f x ≤ cashbook w p g x := by
  apply div_le_div_of_nonneg_right _ (map_nz hw.nz p x)
  exact pr_mono_left (fun i=> mul_le_mul_of_nonneg_left (h i) (hw.nz i)) _
omit [Fintype B] in
theorem book_nonneg (w : Wgt A) (p : A→B) (hw : IsLaw w) (f : Wgt A) (hf : ∀ i,0 ≤ f i) (x) :
    0 ≤ cashbook w p f x := div_nonneg (pr_nonneg (fun i=>mul_nonneg (hw.nz i) (hf i))) (map_nz hw.nz p x)
omit [Fintype B] in
theorem garden (w f : Wgt A) (p : A→B) (hw : IsLaw w) (hf : bower f) :
    bower (banner w p f) := by
  refine ⟨fun i=> book_nonneg w p hw f hf.1 _,fun i=>?_⟩
  exact (le_abs_self _).trans (cashbook_bound w hw.nz p f 1 zero_le_one (fun i=>by
    rw [abs_of_nonneg (hf.1 _)]; exact hf.2 _) _)
theorem projected_min (w : Wgt A) (p : A→B) (hw : IsLaw w) (f g : Wgt A)
    (hf : bower f) (hg : bower g) :
    dip w f g ^2 ≤ dip w (banner w p f) (banner w p g) := by
  let h i := f i*g i
  let u := banner w p h
  have hi : dip w f g=avg w u := by
    have hh := cash_orth w hw.nz p h (fun _=>1)
    simpa only [dip,u,Function.comp_apply,mul_one,h] using hh.symm
  have hh (i) :
      u i^2 ≤ banner w p f i*banner w p g i := by
    have h0 : bower u := garden w h p hw ⟨fun i=>mul_nonneg (hf.1 _) (hg.1 _),fun i=>
      (mul_le_mul (hf.2 _) (hg.2 _) (hg.1 _) zero_le_one).trans_eq (one_mul _)⟩
    have h1 (i) : h i≤ f i :=
      ((mul_le_mul_of_nonneg_left (hg.2 _) (hf.1 _)).trans_eq (mul_one _))
    have h2 (i) : h i≤g i :=
      ((mul_le_mul_of_nonneg_right (hf.2 _) (hg.1 _)).trans_eq (one_mul _))
    rw [pow_two]; exact mul_le_mul (book_order w p hw h f h1 _) (book_order w p hw h g h2 _)
      (h0.1 i) ((garden w f p hw hf).1 i)
  rw [hi]; exact (mean_sq w hw u).trans (avg_mono hw.nz hh)

def trayLoss (R : ℝ) (u f : Wgt A) := pr f (fun i => R≤density u f i)
omit [Fintype A] in
theorem dresso (u f : Wgt A) (h : lsupp f u) : f = fun i => u i*density u f i := by
  funext i; unfold density
  by_cases he : f i=0
  · simp only [he,zero_div,mul_zero]
  have hh := h i he
  field_simp

theorem density_error (w : Wgt A) (p : A→B) (hw : IsLaw w) (f g : Wgt A) (hz : lsupp g w) :
    lcost w (banner w p f) (banner w p (density w g))≤
      varOne (mapW (fun i=>w i*f i) p) (mapW g p) := by
  classical
  let x i := |cashbook w p f i-cashbook w p (density w g) i|
  have he :
      lcost w (banner w p f) (banner w p (density w g))=avg (mapW w p) x :=
    (mapW_avg w p x).symm
  rw [he]; unfold avg varOne
  refine sum_le_sum fun i _=>?_
  let V:=mapW w p i; let A:= mapW (fun i=> w i*f i) p i; let B:= mapW g p i
  have hh : x i= |A-B|/V := by
    unfold x cashbook A B V
    rw [← dresso w g hz,←sub_div,abs_div,abs_of_nonneg (map_nz hw.nz ..)]
  rw [hh]
  by_cases h : V=0
  · change V*_ ≤_
    rw [h,zero_mul]; exact abs_nonneg _
  change V*(|A-B|/V)≤ |A-B|
  exact le_of_eq (by field_simp)

theorem density_trim (u f : Wgt A) (h : ∀ i,0≤f i) (hu : IsLaw u)
    (R : ℝ) (hR : 0≤R) :
    (∀ i,mcut R u f i ≤ density u f i) ∧ lcost u (density u f) (mcut R u f)≤trayLoss R u f := by
  have h1 (i:A) : 0≤density u f i := div_nonneg (h _) (hu.nz _)
  have h2 (i) :
      mcut R u f i=min (density u f i) R := congrArg (fun x=>min x R) (max_eq_left (h1 _))
  have h3 (i) := show mcut R u f i ≤ density u f i from le_trans (le_of_eq (h2 i)) (min_le_left ..)
  refine ⟨h3,Finset.sum_le_sum (fun i _=>?_)⟩
  change u i*|density u f i-mcut R u f i| ≤ f i* ind _
  rw [abs_of_nonneg (sub_nonneg.mpr (h3 _)),h2]
  by_cases hz : R≤density u f i
  · rw [ind_one hz,mul_one,min_eq_right hz]
    have hm := hu.nz i
    by_cases hg : u i=0
    · rw [hg,zero_mul]; exact h _
    apply le_trans (mul_le_mul_of_nonneg_left (sub_le_self _ hR) hm) (le_of_eq ?_)
    unfold density; field_simp
  rw [ind_zero hz,mul_zero,min_eq_left (le_of_not_ge hz),sub_self,mul_zero]

private theorem cost_gap (u : Wgt A) (p : A→B) (f g : Wgt A) (h : ∀ i,g i≤ f i)
    (hu : IsLaw u) :
    lcost u (banner u p f) (banner u p g)=lcost u f g := by
  have hf (i : A) : |banner u p f i-banner u p g i|=banner u p f i-banner u p g i :=
    abs_of_nonneg (sub_nonneg.mpr (book_order u p hu g f h _))
  have hg (f : Wgt A) : avg u f = avg u (banner u p f) := by
    have hh := cash_orth u hu.nz p f (fun _=>1); simpa only [dip,Function.comp_apply,mul_one] using hh.symm
  unfold lcost; simp_rw [hf, abs_of_nonneg (sub_nonneg.mpr (h _)), avg_sub]
  rw [← hg f, ← hg g]

set_option maxHeartbeats 800000 in
theorem density_mend (u : Wgt A) (hu : IsLaw u) (p : A→B) (R : ℝ) (hR : 0≤ R)
    (f g x y : Wgt A) (hf : bower f) (hg : bower g) (hx : SubLaw x)
    (hy : SubLaw y) (h1 : lsupp x u) (h2 : lsupp y u) :
    let V f g := varOne (mapW (fun i=>u i*f i) p) (mapW g p)+trayLoss R u g
    dip u f g ^ 2 ≤ overlap u x y + |rebate u (mcut R u x) (mcut R u y) p|+
      (V f x+V g y) := by
  classical
  intro V
  let F:=banner u p f; let G:=banner u p g
  let X:=banner u p (mcut R u x); let Y:=banner u p (mcut R u y)
  have he (f x : Wgt A) (hx : SubLaw x) (h : lsupp x u) :
      lcost u (banner u p f) (banner u p (mcut R u x)) ≤ V f x := by
    let F := banner u p f; let X:=banner u p (density u x); let Z:=banner u p (mcut R u x)
    obtain ⟨h1,h2⟩:=density_trim u x hx.nz hu R hR
    have hh : lcost u F Z≤lcost u F X+lcost u X Z := by
      unfold lcost; rw [← avg_add]; exact avg_mono hu.nz fun i=>abs_sub_le _ _ _
    exact hh.trans (add_le_add (density_error u p hu f x h)
      (le_trans (cost_gap u p (density u x) _ h1 hu).le h2))
  have hh i : F i*G i ≤ X i*Y i + (|F i-X i|+|G i-Y i|) := by
    have hA := (garden u f p hu hf).2 i; have hB := (garden u g p hu hg).2 i
    have ht : 0≤X i := book_nonneg u p hu _ (fun i=> (mcut_range _ _ _ hR i).1) _
    have hq : 0≤Y i := book_nonneg u p hu _ (fun i=> (mcut_range _ _ _ hR i).1) _
    have hp := (garden u f p hu hf).1 i
    by_cases h : X i≤F i
    · by_cases h' : Y i≤ G i
      · nlinarith only [ht,hq,h,h',hA,hB, le_abs_self (F i-X i),le_abs_self (G i-Y i)]
      have hz := le_of_not_ge h'
      nlinarith only [h,hB,hz,le_abs_self (F i-X i),abs_nonneg (G i-Y i),ht]
    have hz := le_of_not_ge h
    by_cases h' : Y i≤ G i
    · nlinarith only [hA,hq,h',hz,abs_nonneg (F i-X i),le_abs_self (G i-Y i)]
    have hi := le_of_not_ge h'
    nlinarith only [hz,hq,hi,hp,abs_nonneg (F i-X i), abs_nonneg (G i-Y i)]
  let A:= mcut R u x; let B:=mcut R u y
  have hz : dip u A B≤overlap u x y :=
    avg_mono hu.nz (fun i=>mul_le_mul ((density_trim u x hx.nz hu _ hR).1 _)
      ((density_trim u y hy.nz hu _ hR).1 _) ((mcut_range R u y hR i).1)
      (div_nonneg (hx.nz _) (hu.nz _)))
  have h :
      dip u X Y≤overlap u x y + |rebate u A B p| := by
    have h : dip u X Y-dip u A B ≤|dip u A B-dip u X Y| := by rw [abs_sub_comm]; exact le_abs_self _
    change _≤ _+ |dip u A B - dip u X Y|; linarith only [h,hz]
  have hp := avg_mono hu.nz hh
  rw [avg_add,avg_add] at hp
  exact (le_trans (projected_min u p hu f g hf hg) hp).trans
    (add_le_add h (add_le_add (he f x hx h1) (he g y hy h2)))
end HadwigerCounterexample

end

end OAI
