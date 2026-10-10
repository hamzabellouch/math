import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.IntegerHyperplane01
import OAI.Combinatorics.SumProduct.Alignment.RoughSampling01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
noncomputable section
open scoped BigOperators
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace ConvexDiscrepancy
variable {ι : Type*} [Fintype ι]

def average (p : ι → ℝ) (f : ι → ℂ) : ℂ:=∑ i,(p i:ℂ)*f i

lemma weight_error (p q : ι → ℝ) (f : ι → ℂ) (B : ℝ)
    (hB : 0≤B) (hf : ∀ i,‖f i‖≤B) :
    ‖average p f-average q f‖≤B*∑ i,|p i-q i| := by
  have he : average p f-average q f=∑ i,((p i-q i:ℝ):ℂ)*f i:=by
    simp only [average,Complex.ofReal_sub,sub_mul,Finset.sum_sub_distrib]
  rw [he]
  calc
    _≤∑ i,‖((p i-q i:ℝ):ℂ)*f i‖:=norm_sum_le _ _
    _≤∑ i,|p i-q i| *B:=by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      simpa only [mul_comm] using
        mul_le_mul (hf i) (le_refl |p i-q i|) (abs_nonneg _) hB
    _=B*∑ i,|p i-q i|:=by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

lemma positive_piece (p : ι → ℝ) (hp : ∀ i,0≤p i) (hp1 : ∑ i,p i=1)
    (f g : ι → ℂ) (δ : ℝ) (hδ : δ≤‖average p f-average p g‖) :
    ∃ i,0<p i ∧ δ≤‖f i-g i‖ := by
  classical
  have he : average p f-average p g=∑ i,(p i:ℂ)*(f i-g i):=by
    simp only [average,mul_sub,Finset.sum_sub_distrib]
  have hb : ‖average p f-average p g‖≤∑ i,p i*‖f i-g i‖:=by
    rw [he]
    calc
      _≤∑ i,‖(p i:ℂ)*(f i-g i)‖:=norm_sum_le _ _
      _=∑ i,p i*‖f i-g i‖:=by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp i)]
  have hpos : ∃ i,0<p i:=by
    by_contra h
    push Not at h
    have hs : ∑ i,p i≤0:=Finset.sum_nonpos (fun i _=>h i)
    rw [hp1] at hs
    norm_num at hs
  by_contra h
  push Not at h
  obtain ⟨j,hj⟩:=hpos
  have hs : ∑ i,p i*‖f i-g i‖<∑ i,p i*δ:=by
    apply Finset.sum_lt_sum
    · intro i _
      by_cases hi : 0<p i
      · exact (mul_lt_mul_of_pos_left (h i hi) hi).le
      · have hi0 : p i=0:=le_antisymm (le_of_not_gt hi) (hp i)
        simp only [hi0,zero_mul,le_refl]
    · exact ⟨j,Finset.mem_univ _,mul_lt_mul_of_pos_left (h j hj) hj⟩
  rw [←Finset.sum_mul,hp1,one_mul] at hs
  exact (not_lt_of_ge (hδ.trans hb)) hs

 

theorem select_piece (p q : ι → ℝ) (hp : ∀ i,0≤p i) (hp1 : ∑ i,p i=1)
    (f g : ι → ℂ) (B : ℝ) (hB : 0≤B) (hg : ∀ i,‖g i‖≤B)
    (η τ : ℝ) (hd : η≤‖average p f-average q g‖)
    (hw : B*(∑ i,|p i-q i|)≤τ) :
    ∃ i,0<p i ∧ η-τ≤‖f i-g i‖ := by
  apply positive_piece p hp hp1 f g (η-τ)
  have he:=weight_error p q g B hB hg
  have ht:=norm_sub_le (average p f-average p g) (average q g-average p g)
  have hid : (average p f-average p g)-(average q g-average p g)=average p f-average q g:=by ring
  rw [hid,norm_sub_rev (average q g)] at ht
  linarith

 

theorem select_after_freezing (p q : ι → ℝ) (hp : ∀ i,0≤p i) (hp1 : ∑ i,p i=1)
    (f g : ι → ℂ) (B : ℝ) (hB : 0≤B) (hg : ∀ i,‖g i‖≤B)
    (u v : ℂ) (η ε τ : ℝ) (hd : η≤‖u-v‖)
    (hu : ‖u-average p f‖≤ε) (hv : ‖v-average q g‖≤ε)
    (hw : B*(∑ i,|p i-q i|)≤τ) :
    ∃ i,0<p i ∧ η-2*ε-τ≤‖f i-g i‖ := by
  apply select_piece p q hp hp1 f g B hB hg (η-2*ε) τ _ hw
  have h₁:=norm_sub_le (u-average p f) (v-average p f)
  have h₂:=norm_sub_le (v-average q g) (average p f-average q g)
  have hid₁ : (u-average p f)-(v-average p f)=u-v:=by ring
  have hid₂ : (v-average q g)-(average p f-average q g)=v-average p f:=by ring
  rw [hid₁] at h₁
  rw [hid₂] at h₂
  linarith

end ConvexDiscrepancy
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace FinitePieceAverages
variable {α β ι : Type*} [Fintype ι] [DecidableEq ι]

def fiber (s : Finset α) (label : α → ι) (i : ι) : Finset α:=
  s.filter (fun x=>label x=i)
def weight (s : Finset α) (label : α → ι) (i : ι) : ℝ:=
  (fiber s label i).card/(s.card:ℝ)
def mean (s : Finset α) (f : α → ℂ) : ℂ:=
  (s.card:ℂ)⁻¹ * ∑ x∈s,f x

omit [Fintype ι] in
lemma weight_nonneg [Fintype ι] (s : Finset α) (label : α → ι) (i : ι) :
    0≤weight s label i:=by unfold weight; positivity

lemma sum_weights (s : Finset α) (hs : s.Nonempty) (label : α → ι) :
    ∑ i,weight s label i=1 := by
  have hc : ∑ i,(fiber s label i).card=s.card:=by
    simpa only [fiber,Finset.card_eq_sum_ones] using
      (Finset.sum_fiberwise s label (fun _=>1:α → ℕ))
  simp only [weight,←Finset.sum_div,←Nat.cast_sum,hc]
  exact div_self (by exact_mod_cast hs.card_pos.ne' : (s.card:ℝ)≠0)

lemma decomposition (s : Finset α) (label : α → ι) (f : α → ℂ) :
    mean s f=ConvexDiscrepancy.average (weight s label) (fun i=>mean (fiber s label i) f) := by
  have hfiber (i : ι) :
      (weight s label i:ℂ)*mean (fiber s label i) f=
        (s.card:ℂ)⁻¹ * ∑ x∈fiber s label i,f x:=by
    by_cases hi : (fiber s label i).card=0
    · have he : fiber s label i=∅:=Finset.card_eq_zero.mp hi
      simp [weight,mean,he]
    · have hi' : ((fiber s label i).card:ℂ)≠0:=by exact_mod_cast hi
      simp only [weight,mean]
      push_cast
      field_simp
  rw [ConvexDiscrepancy.average]
  simp_rw [hfiber]
  rw [←Finset.mul_sum]
  unfold mean
  congr 1
  exact (Finset.sum_fiberwise s label f).symm

lemma norm_mean_le (s : Finset α) (f : α → ℂ) (B : ℝ) (hB : 0≤B)
    (hf : ∀ x∈s,‖f x‖≤B) : ‖mean s f‖≤B := by
  by_cases hs : s.Nonempty
  · have hc : 0<(s.card:ℝ):=by exact_mod_cast hs.card_pos
    rw [mean,norm_mul,norm_inv,Complex.norm_natCast]
    apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hc.le)).trans
    have hb : (∑ x∈s,‖f x‖) ≤ (s.card:ℝ)*B:=by
      calc
        _≤∑ _x∈s,B:=Finset.sum_le_sum hf
        _=_:=by simp
    calc
      _≤(s.card:ℝ)⁻¹*(s.card*B):=mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hc.le)
      _=B:=by field_simp
  · have he : s=∅:=Finset.not_nonempty_iff_eq_empty.mp hs
    simpa [he,mean] using hB

lemma mean_difference (s : Finset α) (f g : α → ℂ) :
    mean s f-mean s g=mean s (fun x=>f x-g x) := by
  simp only [mean,Finset.sum_sub_distrib,mul_sub]

 

lemma mean_error (s : Finset α) (f g : α → ℂ) (ε : ℝ) (hε : 0≤ε)
    (h : ∀ x∈s,‖f x-g x‖≤ε) : ‖mean s f-mean s g‖≤ε := by
  rw [mean_difference]
  exact norm_mean_le s _ ε hε h

 

theorem select (s : Finset α) (t : Finset β) (hs : s.Nonempty)
    (a : α → ι) (b : β → ι) (f : α → ℂ) (g : β → ℂ)
    (B : ℝ) (hB : 0≤B) (hg : ∀ y∈t,‖g y‖≤B)
    (η τ : ℝ) (hd : η≤‖mean s f-mean t g‖)
    (hw : B*(∑ i,|weight s a i-weight t b i|)≤τ) :
    ∃ i,(fiber s a i).Nonempty ∧
      η-τ≤‖mean (fiber s a i) f-mean (fiber t b i) g‖ := by
  rw [decomposition s a f,decomposition t b g] at hd
  obtain ⟨i,hi,hd⟩:=ConvexDiscrepancy.select_piece (weight s a) (weight t b)
    (weight_nonneg s a) (sum_weights s hs a)
    (fun i=>mean (fiber s a i) f) (fun i=>mean (fiber t b i) g)
    B hB (fun i=>norm_mean_le _ _ B hB (fun x hx=>hg x (Finset.mem_filter.mp hx).1))
    η τ hd hw
  refine ⟨i,?_,hd⟩
  rw [weight] at hi
  have hc : 0<((fiber s a i).card:ℝ):=(div_pos_iff.mp hi).elim And.left
    (fun h=>False.elim (not_lt_of_ge (by positivity) h.1))
  exact Finset.card_pos.mp (by exact_mod_cast hc)

end FinitePieceAverages
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RoughSamplingWeights
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def boxIndices (lo hi a : ι → ℝ) (q : ℝ) : Finset (ι → ℤ):=
  Fintype.piFinset (fun i=>indices (lo i) (hi i) (a i) q)

lemma mem_boxIndices (lo hi a : ι → ℝ) (q : ℝ) (hq : 0<q) (x : ι → ℤ) :
    x∈boxIndices lo hi a q ↔ ∀ i,lo i≤a i+q*x i ∧ a i+q*x i<hi i := by
  simp only [boxIndices,Fintype.mem_piFinset,mem_indices _ _ _ _ hq]

lemma card_boxIndices (lo hi a : ι → ℝ) (q : ℝ) :
    (boxIndices lo hi a q).card=∏ i,(indices (lo i) (hi i) (a i) q).card:=
  Fintype.card_piFinset _

 

def refinedSet (lo' hi' a : ι → ℝ) (q : ℝ) (j : ι → ℤ) (K : ℕ) : Finset (ι → ℤ):=
  (boxIndices lo' hi' (fun i=>a i+q*j i) (q*K)).image
    (fun x i=>j i+(K:ℤ)*x i)

omit [Fintype ι] [DecidableEq ι] in
lemma affine_injective [Fintype ι] [DecidableEq ι] (j : ι → ℤ) (K : ℕ) (hK : 0<K) :
    Function.Injective (fun x : ι → ℤ=>fun i=>j i+(K:ℤ)*x i) := by
  have hKi : (K:ℤ)≠0:=by exact_mod_cast hK.ne'
  intro x y h
  funext i
  exact mul_left_cancel₀ hKi (add_left_cancel (congrFun h i))

lemma card_refinedSet (lo' hi' a : ι → ℝ) (q : ℝ) (j : ι → ℤ) (K : ℕ) (hK : 0<K) :
    (refinedSet lo' hi' a q j K).card=
      ∏ i,(indices (lo' i) (hi' i) (a i+q*j i) (q*K)).card := by
  rw [refinedSet,Finset.card_image_of_injective _ (affine_injective j K hK),card_boxIndices]

 

lemma mem_refinedSet (lo' hi' a : ι → ℝ) (q : ℝ) (hq : 0<q)
    (j : ι → ℤ) (K : ℕ) (hK : 0<K) (x : ι → ℤ) :
    x∈refinedSet lo' hi' a q j K ↔
      ∀ i,(lo' i≤a i+q*x i ∧ a i+q*x i<hi' i) ∧ x i ≡ j i [ZMOD K] := by
  have hKr : 0<(K:ℝ):=by exact_mod_cast hK
  rw [refinedSet,Finset.mem_image]
  constructor
  · rintro ⟨y,hy,rfl⟩
    rw [mem_boxIndices _ _ _ _ (mul_pos hq hKr)] at hy
    intro i
    refine ⟨?_,?_⟩
    · have he : a i+q*((j i+(K:ℤ)*y i:ℤ):ℝ)=a i+q*j i+(q*K)*y i:=by push_cast; ring
      simpa only [he] using hy i
    · rw [Int.modEq_iff_dvd]
      exact ⟨-y i,by ring⟩
  · intro hx
    have hd (i : ι) : ∃ z : ℤ,x i=j i+(K:ℤ)*z:=by
      obtain ⟨z,hz⟩:=Int.modEq_iff_dvd.mp (hx i).2.symm
      exact ⟨z,by linarith⟩
    choose y hy using hd
    refine ⟨y,?_,funext (fun i=>(hy i).symm)⟩
    rw [mem_boxIndices _ _ _ _ (mul_pos hq hKr)]
    intro i
    have he : a i+q*(x i:ℝ)=a i+q*j i+(q*K)*y i:=by rw [hy i]; push_cast; ring
    simpa only [he] using (hx i).1

lemma refined_subset (lo hi lo' hi' a : ι → ℝ) (q : ℝ) (hq : 0<q)
    (hl : ∀ i,lo i≤lo' i) (hh : ∀ i,hi' i≤hi i)
    (j : ι → ℤ) (K : ℕ) (hK : 0<K) :
    refinedSet lo' hi' a q j K⊆boxIndices lo hi a q := by
  intro x hx
  rw [mem_refinedSet _ _ _ _ hq _ _ hK] at hx
  rw [mem_boxIndices _ _ _ _ hq]
  intro i
  exact ⟨(hl i).trans (hx i).1.1,(hx i).1.2.trans_le (hh i)⟩

 

lemma refined_mass (lo hi lo' hi' a : ι → ℝ) (q : ℝ)
    (j : ι → ℤ) (K : ℕ) (hK : 0<K) :
    ((refinedSet lo' hi' a q j K).card:ℝ)/(boxIndices lo hi a q).card=
      refinedBoxWeight lo hi lo' hi' a q j K := by
  rw [card_refinedSet _ _ _ _ _ _ hK,card_boxIndices]
  simp only [Nat.cast_prod,refinedBoxWeight,Finset.prod_div_distrib]

 

lemma box_nonempty (lo hi a : ι → ℝ) (q : ℝ) (hq : 0<q)
    (hscale : ∀ i,4*q≤hi i-lo i) : (boxIndices lo hi a q).Nonempty := by
  apply Finset.card_pos.mp
  rw [card_boxIndices]
  apply Finset.prod_pos
  intro i _
  have hl : lo i≤hi i:=by linarith [hscale i]
  have ht:=(subinterval_weight (lo i) (hi i) (lo i) (hi i) (a i) q hq
    le_rfl hl le_rfl (hscale i)).1
  exact_mod_cast ht

end RoughSamplingWeights

end
end
end
end

end OAI
