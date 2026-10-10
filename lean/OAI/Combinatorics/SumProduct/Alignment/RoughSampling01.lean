import Mathlib
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
noncomputable section
open scoped NNReal
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RoughSamplingWeights

 
def indices (lo hi a q : ℝ) : Finset ℤ:=
  Finset.Ico ⌈(lo-a)/q⌉ ⌈(hi-a)/q⌉

lemma mem_indices (lo hi a q : ℝ) (hq : 0<q) (n : ℤ) :
    n∈indices lo hi a q ↔ lo≤a+q*n ∧ a+q*n<hi := by
  rw [indices,Finset.mem_Ico,Int.ceil_le,Int.lt_ceil]
  constructor
  · rintro ⟨h₁,h₂⟩
    have h₁':= (div_le_iff₀ hq).mp h₁
    have h₂':= (lt_div_iff₀ hq).mp h₂
    constructor <;> nlinarith
  · rintro ⟨h₁,h₂⟩
    constructor
    · apply (div_le_iff₀ hq).mpr; nlinarith
    · apply (lt_div_iff₀ hq).mpr; nlinarith

lemma count_error (lo hi a q : ℝ) (hq : 0<q) (hlo : lo≤hi) :
    |((indices lo hi a q).card:ℝ)-(hi-lo)/q|≤2 := by
  have hceil : ⌈(lo-a)/q⌉≤⌈(hi-a)/q⌉:=Int.ceil_mono
    (div_le_div_of_nonneg_right (sub_le_sub_right hlo a) hq.le)
  have hcard := Int.card_Ico_of_le _ _ hceil
  have hcard' : ((indices lo hi a q).card:ℝ)=
      (⌈(hi-a)/q⌉:ℝ)-(⌈(lo-a)/q⌉:ℝ):=by exact_mod_cast hcard
  rw [hcard',abs_le]
  have hl₁:=Int.le_ceil ((lo-a)/q)
  have hl₂:=Int.ceil_lt_add_one ((lo-a)/q)
  have hh₁:=Int.le_ceil ((hi-a)/q)
  have hh₂:=Int.ceil_lt_add_one ((hi-a)/q)
  have he : (hi-lo)/q=(hi-a)/q-(lo-a)/q:=by ring
  rw [he]
  constructor <;> linarith

lemma indices_subset (lo hi lo' hi' a q : ℝ) (hq : 0<q)
    (hl : lo≤lo') (hh : hi'≤hi) :
    indices lo' hi' a q⊆indices lo hi a q := by
  intro n hn
  rw [mem_indices _ _ _ _ hq] at hn ⊢
  exact ⟨hl.trans hn.1,hn.2.trans_le hh⟩

 

lemma ratio_error {N n L l q : ℝ} (hq : 0<q) (hL : 4*q≤L)
    (hl : 0≤l) (hlL : l≤L)
    (hN : |N-L/q|≤2) (hn : |n-l/q|≤2) :
    0<N ∧ |n/N-l/L|≤8*q/L := by
  have hLp : 0<L:=lt_of_lt_of_le (by positivity) hL
  have hNr : L/q-2≤N:=by have hh:=(abs_le.mp hN).1; linarith
  have hQr : 4≤L/q:=(le_div_iff₀ hq).mpr (by nlinarith)
  have hNp : 0<N:=by linarith
  have hratio : 0≤l/L:=div_nonneg hl hLp.le
  have hratio1 : l/L≤1:=(div_le_one hLp).mpr hlL
  have he : n/N-l/L=((n-l/q)+(l/L)*(L/q-N))/N:=by field_simp; ring
  have hab : |L/q-N|≤2:=by rw [abs_sub_comm]; exact hN
  have hnum : |(n-l/q)+(l/L)*(L/q-N)|≤4:=by
    calc
      _≤|n-l/q|+|(l/L)*(L/q-N)|:=abs_add_le _ _
      _≤2+(l/L)*2:=by
        rw [abs_mul,abs_of_nonneg hratio]
        exact add_le_add hn (mul_le_mul_of_nonneg_left hab hratio)
      _≤4:=by linarith
  refine ⟨hNp,?_⟩
  rw [he,abs_div,abs_of_pos hNp]
  apply (div_le_div_of_nonneg_right hnum hNp.le).trans
  apply (div_le_div_iff₀ hNp hLp).mpr
  have hmul : L-2*q≤N*q:=by
    have hh:=(div_le_iff₀ hq).mp (by linarith [hNr] : L/q≤N+2)
    nlinarith
  nlinarith

 
theorem subinterval_weight (lo hi lo' hi' a q : ℝ) (hq : 0<q)
    (hl : lo≤lo') (hm : lo'≤hi') (hh : hi'≤hi) (hscale : 4*q≤hi-lo) :
    let N : ℝ:=(indices lo hi a q).card
    let n : ℝ:=(indices lo' hi' a q).card
    0<N ∧ 0≤n/N ∧ n/N≤1 ∧
      |n/N-(hi'-lo')/(hi-lo)|≤8*q/(hi-lo) := by
  dsimp only
  have hlen : hi'-lo'≤hi-lo:=by linarith
  obtain ⟨hN,he⟩:=ratio_error hq hscale (sub_nonneg.mpr hm) hlen
    (count_error lo hi a q hq (hl.trans (hm.trans hh)))
    (count_error lo' hi' a q hq hm)
  refine ⟨hN,div_nonneg (by positivity) hN.le,?_,he⟩
  apply (div_le_one hN).mpr
  exact_mod_cast Finset.card_le_card (indices_subset lo hi lo' hi' a q hq hl hh)

 

lemma product_error {ι : Type*} [Fintype ι] (f g : ι → ℝ)
    (hf : ∀ i,0≤f i ∧ f i≤1) (hg : ∀ i,0≤g i ∧ g i≤1) :
    |(∏ i,f i)-(∏ i,g i)|≤∑ i,|f i-g i| := by
  classical
  suffices hh : ∀ s : Finset ι, |(∏ i∈s,f i)-(∏ i∈s,g i)|≤∑ i∈s,|f i-g i| from hh Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.prod_insert ha,Finset.sum_insert ha]
    have hf0:= (hf a).1
    have hf1:= (hf a).2
    have hg0 : 0≤∏ i∈s,g i:=Finset.prod_nonneg (fun i _=>(hg i).1)
    have hg1 : (∏ i∈s,g i)≤1:=Finset.prod_le_one₀ (fun i _=>(hg i).1) (fun i _=>(hg i).2)
    have he : f a*(∏ i∈s,f i)-g a*(∏ i∈s,g i)=
      f a*((∏ i∈s,f i)-(∏ i∈s,g i))+(f a-g a)*(∏ i∈s,g i):=by ring
    rw [he]
    calc
      _≤|f a*((∏ i∈s,f i)-(∏ i∈s,g i))|+|(f a-g a)*(∏ i∈s,g i)|:=abs_add_le _ _
      _≤|(∏ i∈s,f i)-(∏ i∈s,g i)|+|f a-g a|:=by
        rw [abs_mul,abs_mul,abs_of_nonneg hf0,abs_of_nonneg hg0]
        exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) hf1)
          (mul_le_of_le_one_right (abs_nonneg _) hg1)
      _≤|f a-g a|+∑ i∈s,|f i-g i|:=by linarith

 
def boxWeight {ι : Type*} [Fintype ι]
    (lo hi lo' hi' a : ι → ℝ) (q : ℝ) : ℝ:=
  ∏ i,((indices (lo' i) (hi' i) (a i) q).card:ℝ)/(indices (lo i) (hi i) (a i) q).card

 
theorem box_weight_error {ι : Type*} [Fintype ι]
    (lo hi lo' hi' a : ι → ℝ) (q : ℝ) (hq : 0<q)
    (hl : ∀ i,lo i≤lo' i) (hm : ∀ i,lo' i≤hi' i) (hh : ∀ i,hi' i≤hi i)
    (hscale : ∀ i,4*q≤hi i-lo i) :
    |boxWeight lo hi lo' hi' a q-(∏ i,(hi' i-lo' i)/(hi i-lo i))|≤
      ∑ i,8*q/(hi i-lo i) := by
  have hpos (i : ι) : 0<hi i-lo i:=lt_of_lt_of_le (by positivity) (hscale i)
  apply (product_error _ _ (fun i=>?_) (fun i=>?_)).trans
  · apply Finset.sum_le_sum
    intro i _
    exact (subinterval_weight (lo i) (hi i) (lo' i) (hi' i) (a i) q hq (hl i) (hm i) (hh i) (hscale i)).2.2.2
  · have ht:=subinterval_weight (lo i) (hi i) (lo' i) (hi' i) (a i) q hq (hl i) (hm i) (hh i) (hscale i)
    exact ⟨ht.2.1,ht.2.2.1⟩
  · exact ⟨div_nonneg (sub_nonneg.mpr (hm i)) (hpos i).le,
      (div_le_one (hpos i)).mpr (by linarith [hl i,hh i])⟩

 

theorem compare_box_weights {ι : Type*} [Fintype ι]
    (lo hi lo' hi' a b : ι → ℝ) (q t : ℝ) (hq : 0<q) (ht : 0<t)
    (hl : ∀ i,lo i≤lo' i) (hm : ∀ i,lo' i≤hi' i) (hh : ∀ i,hi' i≤hi i)
    (hsq : ∀ i,4*q≤hi i-lo i) (hst : ∀ i,4*t≤hi i-lo i) :
    |boxWeight lo hi lo' hi' a q-boxWeight lo hi lo' hi' b t|≤
      (∑ i,8*q/(hi i-lo i))+(∑ i,8*t/(hi i-lo i)) := by
  have h₁:=box_weight_error lo hi lo' hi' a q hq hl hm hh hsq
  have h₂:=box_weight_error lo hi lo' hi' b t ht hl hm hh hst
  have hx:=abs_sub (boxWeight lo hi lo' hi' a q-(∏ i,(hi' i-lo' i)/(hi i-lo i)))
    (boxWeight lo hi lo' hi' b t-(∏ i,(hi' i-lo' i)/(hi i-lo i)))
  have he : (boxWeight lo hi lo' hi' a q-(∏ i,(hi' i-lo' i)/(hi i-lo i)))-
      (boxWeight lo hi lo' hi' b t-(∏ i,(hi' i-lo' i)/(hi i-lo i)))=
      boxWeight lo hi lo' hi' a q-boxWeight lo hi lo' hi' b t:=by ring
  rw [he] at hx
  linarith

 

lemma refined_card_le (lo hi lo' hi' a q : ℝ) (hq : 0<q)
    (hl : lo≤lo') (hh : hi'≤hi) (j : ℤ) (K : ℕ) (hK : 0<K) :
    (indices lo' hi' (a+q*j) (q*K)).card≤(indices lo hi a q).card := by
  have hKr : 0<(K:ℝ):=by exact_mod_cast hK
  have hKi : (K:ℤ)≠0:=by exact_mod_cast hK.ne'
  apply Finset.card_le_card_of_injOn (fun n : ℤ=>j+K*n)
  · intro n hn
    change n ∈ indices lo' hi' (a+q*j) (q*K) at hn
    change j+(K:ℤ)*n ∈ indices lo hi a q
    rw [mem_indices _ _ _ _ (mul_pos hq hKr)] at hn
    rw [mem_indices _ _ _ _ hq]
    have he : a+q*((j+(K:ℤ)*n:ℤ):ℝ)=(a+q*j)+(q*K)*n:=by push_cast; ring
    rw [he]
    exact ⟨hl.trans hn.1,hn.2.trans_le hh⟩
  · intro x _ y _ hxy
    exact mul_left_cancel₀ hKi (add_left_cancel hxy)

 

theorem refined_interval_weight (lo hi lo' hi' a q : ℝ) (hq : 0<q)
    (hl : lo≤lo') (hm : lo'≤hi') (hh : hi'≤hi) (hscale : 4*q≤hi-lo)
    (j : ℤ) (K : ℕ) (hK : 0<K) :
    let N : ℝ:=(indices lo hi a q).card
    let n : ℝ:=(indices lo' hi' (a+q*j) (q*K)).card
    0<N ∧ 0≤n/N ∧ n/N≤1 ∧
      |n/N-((hi'-lo')/(hi-lo))/(K:ℝ)|≤8*q/(hi-lo) := by
  dsimp only
  have hKr : 0<(K:ℝ):=by exact_mod_cast hK
  have hK1 : 1≤(K:ℝ):=by exact_mod_cast hK
  have hlen : (hi'-lo')/(K:ℝ)≤hi-lo:=by
    apply (div_le_iff₀ hKr).mpr
    have hL : 0≤hi-lo:=by linarith
    have hsub : hi'-lo'≤hi-lo:=by linarith
    exact hsub.trans (le_mul_of_one_le_right hL hK1)
  have he := count_error lo' hi' (a+q*j) (q*K) (mul_pos hq hKr) hm
  have hfrac : (hi'-lo')/(q*K)=((hi'-lo')/(K:ℝ))/q:=by ring
  rw [hfrac] at he
  obtain ⟨hN,hb⟩:=ratio_error hq hscale (div_nonneg (sub_nonneg.mpr hm) hKr.le) hlen
    (count_error lo hi a q hq (hl.trans (hm.trans hh))) he
  refine ⟨hN,div_nonneg (by positivity) hN.le,?_,?_⟩
  · apply (div_le_one hN).mpr
    exact_mod_cast refined_card_le lo hi lo' hi' a q hq hl hh j K hK
  · simpa only [div_div,mul_comm] using hb

 

def refinedBoxWeight {ι : Type*} [Fintype ι]
    (lo hi lo' hi' a : ι → ℝ) (q : ℝ) (j : ι → ℤ) (K : ℕ) : ℝ:=
  ∏ i,((indices (lo' i) (hi' i) (a i+q*j i) (q*K)).card:ℝ)/
    (indices (lo i) (hi i) (a i) q).card

 

theorem refined_box_weight_error {ι : Type*} [Fintype ι]
    (lo hi lo' hi' a : ι → ℝ) (q : ℝ) (hq : 0<q)
    (hl : ∀ i,lo i≤lo' i) (hm : ∀ i,lo' i≤hi' i) (hh : ∀ i,hi' i≤hi i)
    (hscale : ∀ i,4*q≤hi i-lo i) (j : ι → ℤ) (K : ℕ) (hK : 0<K) :
    |refinedBoxWeight lo hi lo' hi' a q j K-
      (∏ i,(hi' i-lo' i)/(hi i-lo i)/(K:ℝ))|≤∑ i,8*q/(hi i-lo i) := by
  have hpos (i : ι) : 0<hi i-lo i:=lt_of_lt_of_le (by positivity) (hscale i)
  have hKr : 0<(K:ℝ):=by exact_mod_cast hK
  have hK1 : 1≤(K:ℝ):=by exact_mod_cast hK
  apply (product_error _ _ (fun i=>?_) (fun i=>?_)).trans
  · apply Finset.sum_le_sum
    intro i _
    exact (refined_interval_weight (lo i) (hi i) (lo' i) (hi' i) (a i) q hq
      (hl i) (hm i) (hh i) (hscale i) (j i) K hK).2.2.2
  · have ht:=refined_interval_weight (lo i) (hi i) (lo' i) (hi' i) (a i) q hq
      (hl i) (hm i) (hh i) (hscale i) (j i) K hK
    exact ⟨ht.2.1,ht.2.2.1⟩
  · refine ⟨div_nonneg (div_nonneg (sub_nonneg.mpr (hm i)) (hpos i).le) hKr.le,?_⟩
    apply (div_le_one hKr).mpr
    exact ((div_le_one (hpos i)).mpr (by linarith [hl i,hh i])).trans hK1

 

theorem compare_refined_box_weights {ι : Type*} [Fintype ι]
    (lo hi lo' hi' a b : ι → ℝ) (q t : ℝ) (hq : 0<q) (ht : 0<t)
    (hl : ∀ i,lo i≤lo' i) (hm : ∀ i,lo' i≤hi' i) (hh : ∀ i,hi' i≤hi i)
    (hsq : ∀ i,4*q≤hi i-lo i) (hst : ∀ i,4*t≤hi i-lo i)
    (j k : ι → ℤ) (K : ℕ) (hK : 0<K) :
    |refinedBoxWeight lo hi lo' hi' a q j K-refinedBoxWeight lo hi lo' hi' b t k K|≤
      (∑ i,8*q/(hi i-lo i))+(∑ i,8*t/(hi i-lo i)) := by
  have h₁:=refined_box_weight_error lo hi lo' hi' a q hq hl hm hh hsq j K hK
  have h₂:=refined_box_weight_error lo hi lo' hi' b t ht hl hm hh hst k K hK
  have hx:=abs_sub (refinedBoxWeight lo hi lo' hi' a q j K-(∏ i,(hi' i-lo' i)/(hi i-lo i)/(K:ℝ)))
    (refinedBoxWeight lo hi lo' hi' b t k K-(∏ i,(hi' i-lo' i)/(hi i-lo i)/(K:ℝ)))
  have he : (refinedBoxWeight lo hi lo' hi' a q j K-(∏ i,(hi' i-lo' i)/(hi i-lo i)/(K:ℝ)))-
      (refinedBoxWeight lo hi lo' hi' b t k K-(∏ i,(hi' i-lo' i)/(hi i-lo i)/(K:ℝ)))=
      refinedBoxWeight lo hi lo' hi' a q j K-refinedBoxWeight lo hi lo' hi' b t k K:=by ring
  rw [he] at hx
  linarith

 

theorem total_weight_error {ι ν : Type*} [Fintype ι] [Fintype ν]
    (lo hi a b : ι → ℝ) (lo' hi' : ν → ι → ℝ) (q t : ℝ) (hq : 0<q) (ht : 0<t)
    (hl : ∀ z i,lo i≤lo' z i) (hm : ∀ z i,lo' z i≤hi' z i) (hh : ∀ z i,hi' z i≤hi i)
    (hsq : ∀ i,4*q≤hi i-lo i) (hst : ∀ i,4*t≤hi i-lo i)
    (j k : ν → ι → ℤ) (K : ℕ) (hK : 0<K) :
    (∑ z,|refinedBoxWeight lo hi (lo' z) (hi' z) a q (j z) K-
      refinedBoxWeight lo hi (lo' z) (hi' z) b t (k z) K|)≤
      (Fintype.card ν:ℝ)*((∑ i,8*q/(hi i-lo i))+(∑ i,8*t/(hi i-lo i))) := by
  calc
    _≤∑ z:ν,((∑ i,8*q/(hi i-lo i))+(∑ i,8*t/(hi i-lo i))):=by
      apply Finset.sum_le_sum
      intro z _
      exact compare_refined_box_weights lo hi (lo' z) (hi' z) a b q t hq ht
        (hl z) (hm z) (hh z) hsq hst (j z) (k z) K hK
    _=_:=by simp [mul_add]

 

theorem residue_parameter (q K : ℕ) (h : q.Coprime K) (a u : ℤ) :
    ∃ j : ℤ,∀ n : ℤ,(a+(q:ℤ)*n ≡ u [ZMOD K]) ↔ n ≡ j [ZMOD K] := by
  let j : ℤ:=(u-a)*Nat.gcdA q K
  have hb : (q:ℤ)*Nat.gcdA q K+(K:ℤ)*Nat.gcdB q K=1:=by
    simpa [h.gcd_eq_one] using (Nat.gcd_eq_gcd_ab q K).symm
  have hu : a+(q:ℤ)*j ≡ u [ZMOD K]:=by
    rw [Int.modEq_iff_dvd]
    refine ⟨(u-a)*Nat.gcdB q K,?_⟩
    dsimp [j]
    nlinarith [congrArg (fun z : ℤ=>(u-a)*z) hb]
  refine ⟨j,fun n=>⟨fun hn=>?_,fun hn=>?_⟩⟩
  · have hc:=Int.ModEq.add_left_cancel' a (hn.trans hu.symm)
    rw [Int.modEq_iff_dvd] at hc ⊢
    have hc' : (K:ℤ)∣(q:ℤ)*(j-n):=by simpa [mul_sub] using hc
    exact h.symm.isCoprime.dvd_of_dvd_mul_left hc'
  · exact (Int.ModEq.add_left a (Int.ModEq.mul_left (q:ℤ) hn)).trans hu

 

theorem residue_sample (lo hi : ℝ) (q K : ℕ) (hq : 0<q) (hK : 0<K)
    (a u : ℤ) (j : ℤ)
    (hj : ∀ n : ℤ,(a+(q:ℤ)*n ≡ u [ZMOD K]) ↔ n ≡ j [ZMOD K]) :
    ∀ x : ℤ,((lo≤(x:ℝ) ∧ (x:ℝ)<hi) ∧
      (∃ n : ℤ,x=a+(q:ℤ)*n) ∧ x ≡ u [ZMOD K]) ↔
      ∃ n∈indices lo hi ((a:ℝ)+q*j) ((q:ℝ)*K),x=a+(q:ℤ)*(j+(K:ℤ)*n) := by
  have hqr : 0<(q:ℝ):=by exact_mod_cast hq
  have hKr : 0<(K:ℝ):=by exact_mod_cast hK
  intro x
  constructor
  · rintro ⟨hx,⟨n,rfl⟩,hu⟩
    have hd' : (K:ℤ)∣n-j:=Int.modEq_iff_dvd.mp (((hj n).mp hu).symm)
    obtain ⟨v,hv⟩:=hd'
    have hn : n=j+(K:ℤ)*v:=by linarith
    refine ⟨v,?_,by rw [hn]⟩
    rw [mem_indices _ _ _ _ (mul_pos hqr hKr)]
    have he : ((a+(q:ℤ)*n:ℤ):ℝ)=(a:ℝ)+q*j+((q:ℝ)*K)*v:=by
      rw [hn]; push_cast; ring
    rwa [he] at hx
  · rintro ⟨n,hn,rfl⟩
    rw [mem_indices _ _ _ _ (mul_pos hqr hKr)] at hn
    refine ⟨?_,⟨j+(K:ℤ)*n,rfl⟩,(hj _).mpr ?_⟩
    · have he : ((a+(q:ℤ)*(j+(K:ℤ)*n):ℤ):ℝ)=(a:ℝ)+q*j+((q:ℝ)*K)*n:=by
        push_cast; ring
      rwa [he]
    · rw [Int.modEq_iff_dvd]
      refine ⟨-n,?_⟩
      ring

end RoughSamplingWeights

end
end
end
end

end OAI
