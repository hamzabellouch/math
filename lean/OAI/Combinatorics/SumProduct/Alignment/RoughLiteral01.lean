import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughExtremal01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
noncomputable section
end
 
end

section
 

 

noncomputable section
namespace RoughSourceExceptional
open RationalLattice MalcevCharacters RealPolynomialDegree RoughScales Filter
open RoughSamplingWeights RoughProgressionDensity RoughExtremalProgressions

lemma Ico_eq_range (a b : ℤ) :
    (Finset.Ico a b)=(Finset.range ((Finset.Ico a b).card)).image (fun i : ℕ=>a+(i:ℤ)):=by
  ext z
  simp only [Finset.mem_Ico,Finset.mem_image,Finset.mem_range,Int.card_Ico]
  constructor
  · intro hz
    refine ⟨(z-a).toNat,?_,?_⟩ <;> omega
  · rintro ⟨i,hi,rfl⟩
    omega

def timeLength (S : ℝ) (r L : ℤ) : ℕ:=(indices S (2*S) r L).card
def firstTime (S : ℝ) (r L : ℤ) : ℤ:=r+L*⌈(S-r)/L⌉
def times (S : ℝ) (r L : ℤ) : Finset ℤ:=(indices S (2*S) r L).image (fun z=>r+L*z)

lemma times_eq_range (S : ℝ) (r L : ℤ) :
    times S r L=(Finset.range (timeLength S r L)).image (fun i : ℕ=>firstTime S r L+L*(i:ℤ)):=by
  unfold times timeLength
  conv_lhs => arg 2; unfold indices; rw [Ico_eq_range]
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i hi
  simp only [Function.comp_apply,firstTime]
  ring

lemma mem_times (S : ℝ) (r L t : ℤ) (hL : 0<L) :
    t∈times S r L ↔ S≤(t:ℝ) ∧ (t:ℝ)<2*S ∧ ∃ z : ℤ,t=r+L*z:=by
  have hL' : 0<(L:ℝ):=by exact_mod_cast hL
  constructor
  · intro ht
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp ht
    have hz':=(mem_indices S (2*S) r L hL' z).mp hz
    refine ⟨?_,?_,z,rfl⟩
    · simpa only [Int.cast_add,Int.cast_mul] using hz'.1
    · simpa only [Int.cast_add,Int.cast_mul] using hz'.2
  · rintro ⟨hlo,hhi,z,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨z,?_,rfl⟩
    apply (mem_indices S (2*S) r L hL' z).mpr
    simpa only [Int.cast_add,Int.cast_mul] using And.intro hlo hhi

lemma time_injective (S : ℝ) (r L : ℤ) (hL : 0<L) :
    Function.Injective (fun i : ℕ=>firstTime S r L+L*(i:ℤ)):=by
  intro i j hij
  have hi : (i:ℤ)=(j:ℤ):=mul_left_cancel₀ hL.ne' (add_left_cancel hij)
  exact_mod_cast hi

lemma times_card (S : ℝ) (r L : ℤ) (hL : 0<L) :
    (times S r L).card=timeLength S r L:=by
  rw [times_eq_range,Finset.card_image_of_injective _ (time_injective S r L hL),Finset.card_range]

lemma scale_at_index (S : ℝ) (r L : ℤ) (hL : 0<L) (i : ℕ) (hi : i<timeLength S r L) :
    S≤((firstTime S r L+L*(i:ℤ):ℤ):ℝ) ∧ ((firstTime S r L+L*(i:ℤ):ℤ):ℝ)<2*S:=by
  have ht : firstTime S r L+L*(i:ℤ)∈times S r L:=by
    rw [times_eq_range]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi,rfl⟩
  have hh:=(mem_times S r L _ hL).mp ht
  exact ⟨hh.1,hh.2.1⟩

lemma firstTime_rough {w : ℕ} {S : ℝ} {r L : ℤ} (hr : Rough w r)
    (hWL : (primorial w:ℤ)∣L) : Rough w (firstTime S r L):=
  rough_add_multiple hr hWL _

 

lemma timeLength_tendsto {S : ℕ→ℝ} {r L : ℕ→ℤ} (hL : ∀ n,0<L n)
    (hS : Tendsto S atTop atTop) (hSL : Tendsto (fun n=>S n/(L n:ℝ)) atTop atTop) :
    Tendsto (fun n=>(timeLength (S n) (r n) (L n):ℝ)) atTop atTop:=by
  apply tendsto_atTop.mpr
  intro A
  filter_upwards [hS.eventually (eventually_ge_atTop 0),hSL.eventually (eventually_ge_atTop (A+2))]
    with n hsn hsl
  have he:=count_error (S n) (2*S n) (r n) (L n) (by exact_mod_cast hL n) (by linarith)
  change |(timeLength (S n) (r n) (L n):ℝ)-(2*S n-S n)/(L n:ℝ)|≤2 at he
  have hs : (2*S n-S n)/(L n:ℝ)=S n/(L n:ℝ):=by ring
  rw [hs,abs_le] at he
  linarith

 

lemma integer_scales_of_real {S Z : ℕ→ℝ} (hS : Tendsto S atTop atTop)
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun n=>Z n/S n^a) atTop atTop) :
    ∀ k : ℕ,Tendsto (fun n=>Z n/S n^k) atTop atTop:=by
  intro k
  cases k with
  | zero=>
    have hz1 : Tendsto (fun n=>Z n/S n) atTop atTop:=by
      simpa only [Real.rpow_one] using hZ 1 (by norm_num)
    have hp:=hz1.atTop_mul_atTop₀ hS
    have hz : Tendsto Z atTop atTop:=by
      apply Filter.Tendsto.congr' _ hp
      filter_upwards [hS.eventually (eventually_gt_atTop 0)] with n hn
      exact div_mul_cancel₀ _ hn.ne'
    simpa only [pow_zero,div_one] using hz
  | succ k=>
    simpa only [Real.rpow_natCast] using hZ ((k+1:ℕ):ℝ) (by positivity)

variable {G : Type} [Group G] [TopologicalSpace G] {dim : ℕ}
variable (c : RealCoordinates G dim) (Γ : Subgroup G) [mtr : MetricSpace (G⧸Γ)]
local instance roughLiteral01ExceptionalTopology : TopologicalSpace (G⧸Γ):=
  mtr.toUniformSpace.toTopologicalSpace

 
def exceptional (v : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η Z S : ℝ)
    (P : (Fin (v+1)→ℝ)→G) (r L : ℤ) : Finset ℤ:=by
  classical
  exact (times S r L).filter (BadAt Γ v c₀ C₀ B η Z P)

omit [TopologicalSpace G] in
lemma exceptional_card (v : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η Z S : ℝ)
    (P : (Fin (v+1)→ℝ)→G) (r L : ℤ) (hL : 0<L) :
    (exceptional Γ v c₀ C₀ B η Z S P r L).card=
      (badIndices Γ v (timeLength S r L) c₀ C₀ B η Z P (firstTime S r L) L).card:=by
  classical
  unfold exceptional
  rw [times_eq_range,Finset.filter_image]
  apply Finset.card_image_iff.mpr
  exact (time_injective S r L hL).injOn

variable [IsTopologicalGroup G] (hsk : SecondKind c)
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)

include hsk hΓ htop in
 

theorem source_exceptional_bound (v D : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η)
    (w : ℕ→ℕ) (S Z : ℕ→ℝ) (r L : ℕ→ℤ)
    (hw : Tendsto w atTop atTop) (hS : Tendsto S atTop atTop)
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun n=>Z n/S n^a) atTop atTop)
    (hL : ∀ n,0<L n) (hsm : ∀ n,Smooth (w n) (L n))
    (hWL : ∀ n,(primorial (w n):ℤ)∣L n) (hr : ∀ n,(r n).natAbs.Coprime (primorial (w n)))
    (hSL : Tendsto (fun n=>S n/(L n:ℝ)) atTop atTop) :
    ∃ H : ℕ,0<H ∧ ∀ K : ℕ,0<K →∀ ε : ℝ,0<ε →∀ᶠ n in atTop,
      ∀ P : (Fin (v+1)→ℝ)→G,(∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D) →
      ((exceptional Γ v c₀ C₀ B η (Z n) (S n) P (r n) (L n)).card:ℝ)/
          ((times (S n) (r n) (L n)).card:ℝ)≤(extremal H K:ℝ)/K+ε:=by
  classical
  obtain ⟨H,hH,hbound⟩:=eventual_density_bound c Γ hsk hΓ htop v D c₀ C₀ B η hc₀ hC₀ hB hη
    w S Z hw hS (integer_scales_of_real hS hZ)
  have ht:=timeLength_tendsto (r:=r) hL hS hSL
  refine ⟨H,hH,fun K hK ε hε=>?_⟩
  filter_upwards [hbound K hK,ht.eventually (eventually_ge_atTop 1),
    ht.eventually (eventually_ge_atTop ((K:ℝ)/ε))] with n hbn hn hne
  intro P hP
  have hNp : 0<(timeLength (S n) (r n) (L n):ℝ):=by linarith
  have hN : 0<timeLength (S n) (r n) (L n):=by exact_mod_cast hNp
  have hd : (K:ℝ)/(timeLength (S n) (r n) (L n):ℝ)≤ε:=by
    apply (div_le_iff₀ hNp).mpr
    have hh:=(div_le_iff₀ hε).mp hne
    nlinarith
  rw [exceptional_card Γ v c₀ C₀ B η (Z n) (S n) P (r n) (L n) (hL n),times_card _ _ _ (hL n)]
  exact (hbn _ hN _ _ (hL n) (hsm n) (hWL n)
    (firstTime_rough ((rough_iff_coprime _ _).mpr (hr n)) (hWL n))
    (scale_at_index _ _ _ (hL n)) P hP).trans (by linarith)

end RoughSourceExceptional

end
 
end

section
 

 

noncomputable section
namespace RoughLiteralBoxes
open RationalLattice MalcevCharacters RealPolynomialDegree RoughScales Filter
open RoughSamplingWeights FinitePieceAverages RoughExtremalProgressions

 
def lower (closed : Bool) (a : ℝ) : ℤ := if closed then ⌈a⌉ else ⌊a⌋+1
 
def upper (closed : Bool) (a : ℝ) : ℤ := if closed then ⌊a⌋+1 else ⌈a⌉

def leftCondition (closed : Bool) (a x : ℝ) : Prop := if closed then a≤x else a<x
def rightCondition (closed : Bool) (x a : ℝ) : Prop := if closed then x≤a else x<a

lemma lower_le_iff (closed : Bool) (a : ℝ) (x : ℤ) :
    lower closed a≤x ↔ leftCondition closed a x := by
  cases closed <;> simp only [lower,leftCondition,Bool.false_eq_true,ite_false,ite_true]
  · rw [Int.add_one_le_iff,Int.floor_lt]
  · exact Int.ceil_le

lemma lt_upper_iff (closed : Bool) (a : ℝ) (x : ℤ) :
    x<upper closed a ↔ rightCondition closed x a := by
  cases closed <;> simp only [upper,rightCondition,Bool.false_eq_true,ite_false,ite_true]
  · exact Int.lt_ceil
  · rw [Int.lt_add_one_iff,Int.le_floor]

lemma lower_bounds (closed : Bool) (a : ℝ) :
    a≤(lower closed a:ℝ) ∧ (lower closed a:ℝ)≤a+1 := by
  cases closed
  · simp only [lower,Bool.false_eq_true,ite_false,Int.cast_add,Int.cast_one]
    constructor <;> linarith [Int.floor_le a,Int.lt_floor_add_one a]
  · simpa only [lower,ite_true] using And.intro (Int.le_ceil a) (Int.ceil_lt_add_one a).le

lemma upper_bounds (closed : Bool) (a : ℝ) :
    a≤(upper closed a:ℝ) ∧ (upper closed a:ℝ)≤a+1 := by
  cases closed
  · simpa only [upper,Bool.false_eq_true,ite_false] using
      And.intro (Int.le_ceil a) (Int.ceil_lt_add_one a).le
  · simp only [upper,ite_true,Int.cast_add,Int.cast_one]
    constructor <;> linarith [Int.floor_le a,Int.lt_floor_add_one a]

variable {v : ℕ}

def points (lo hi : Fin v→ℝ) (lc rc : Fin v→Bool) : Finset (Fin v→ℤ) :=
  Fintype.piFinset (fun i=>Finset.Ico (lower (lc i) (lo i)) (upper (rc i) (hi i)))

lemma mem_points (lo hi : Fin v→ℝ) (lc rc : Fin v→Bool) (x : Fin v→ℤ) :
    x∈points lo hi lc rc ↔ ∀ i,leftCondition (lc i) (lo i) (x i) ∧
      rightCondition (rc i) (x i) (hi i) := by
  simp only [points,Fintype.mem_piFinset,Finset.mem_Ico,lower_le_iff,lt_upper_iff]

 
lemma points_eq_box (lo hi : Fin v→ℝ) (lc rc : Fin v→Bool) :
    points lo hi lc rc = boxIndices (fun i=>(lower (lc i) (lo i):ℝ))
      (fun i=>(upper (rc i) (hi i):ℝ)) (fun _=>0) 1 := by
  ext x
  simp only [points,Fintype.mem_piFinset,Finset.mem_Ico,
    mem_boxIndices _ _ _ _ zero_lt_one,zero_add,one_mul,Int.cast_le,Int.cast_lt]

 
def residuePoints (lo hi : Fin v→ℝ) (lc rc : Fin v→Bool) (res : Fin v→ℤ) (t : ℤ) :
    Finset (Fin v→ℤ) :=
  (points lo hi lc rc).filter (fun x=>∀ i,x i ≡ res i [ZMOD t])

lemma residuePoints_eq_box (lo hi : Fin v→ℝ) (lc rc : Fin v→Bool) (res : Fin v→ℤ) (t : ℤ) :
    residuePoints lo hi lc rc res t = physicalResidueBox
      (fun i=>(lower (lc i) (lo i):ℝ)) (fun i=>(upper (rc i) (hi i):ℝ)) res t.natAbs := by
  simp only [residuePoints,physicalResidueBox,points_eq_box,Int.modEq_natAbs]

 
lemma rounded_geometry (lo hi : Fin v→ℝ) (lc rc : Fin v→Bool) (c C Z : ℝ)
    (hZ : 1≤Z) (hcZ : 2≤c*Z)
    (hs : ∀ i,c*Z≤hi i-lo i) (hb : ∀ i,-C*Z≤lo i ∧ hi i≤C*Z) :
    (∀ i,(c/2)*Z≤(upper (rc i) (hi i):ℝ)-(lower (lc i) (lo i):ℝ)) ∧
    (∀ i,-(C+1)*Z≤(lower (lc i) (lo i):ℝ) ∧ (upper (rc i) (hi i):ℝ)≤(C+1)*Z) := by
  constructor
  · intro i
    obtain ⟨hl₀,hl₁⟩:=lower_bounds (lc i) (lo i)
    obtain ⟨hh₀,hh₁⟩:=upper_bounds (rc i) (hi i)
    nlinarith [hs i]
  · intro i
    obtain ⟨hl₀,hl₁⟩:=lower_bounds (lc i) (lo i)
    obtain ⟨hh₀,hh₁⟩:=upper_bounds (rc i) (hi i)
    constructor <;> nlinarith [(hb i).1,(hb i).2]

variable {G : Type} [Group G] [TopologicalSpace G] {dim : ℕ}
variable (c : RealCoordinates G dim) (Γ : Subgroup G) [mtr : MetricSpace (G⧸Γ)]
local instance roughLiteral01BoxesTopology : TopologicalSpace (G⧸Γ):=
  mtr.toUniformSpace.toTopologicalSpace

 
def BadAt (v : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η Z : ℝ)
    (P : (Fin (v+1)→ℝ)→G) (t : ℤ) : Prop :=
  ∃ (lo hi : Fin v→ℝ) (lc rc : Fin v→Bool) (res : Fin v→ℤ) (test : (G⧸Γ)→ℂ),
    (∀ i,c₀*Z≤hi i-lo i) ∧ (∀ i,-C₀*Z≤lo i ∧ hi i≤C₀*Z) ∧
    LipschitzWith B test ∧ (∀ y,‖test y‖≤B) ∧
    η≤‖mean (points lo hi lc rc)
      (fun x=>test (QuotientGroup.mk (P (Fin.cons (t:ℝ) (fun i=>(x i:ℝ))))))-
      mean (residuePoints lo hi lc rc res t)
      (fun x=>test (QuotientGroup.mk (P (Fin.cons (t:ℝ) (fun i=>(x i:ℝ))))))‖

omit [TopologicalSpace G] in
lemma badAt_halfopen (v : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η Z : ℝ)
    (P : (Fin (v+1)→ℝ)→G) (t : ℤ) (hZ : 1≤Z) (hcZ : 2≤c₀*Z) :
    BadAt Γ v c₀ C₀ B η Z P t →
      RoughProgressionDensity.BadAt Γ v (c₀/2) (C₀+1) B η Z P t := by
  rintro ⟨lo,hi,lc,rc,res,test,hs,hb,hlip,hbound,hbad⟩
  obtain ⟨hs',hb'⟩:=rounded_geometry lo hi lc rc c₀ C₀ Z hZ hcZ hs hb
  refine ⟨(fun i=>(lower (lc i) (lo i):ℝ)),(fun i=>(upper (rc i) (hi i):ℝ)),
    res,test,hs',hb',hlip,hbound,?_⟩
  simpa only [points_eq_box,residuePoints_eq_box lo hi lc rc res t] using hbad

 
def exceptional (v : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η Z S : ℝ)
    (P : (Fin (v+1)→ℝ)→G) (r L : ℤ) : Finset ℤ := by
  classical
  exact (RoughSourceExceptional.times S r L).filter (BadAt Γ v c₀ C₀ B η Z P)

omit [TopologicalSpace G] in
lemma exceptional_subset (v : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η Z S : ℝ)
    (P : (Fin (v+1)→ℝ)→G) (r L : ℤ) (hZ : 1≤Z) (hcZ : 2≤c₀*Z) :
    exceptional Γ v c₀ C₀ B η Z S P r L ⊆
      RoughSourceExceptional.exceptional Γ v (c₀/2) (C₀+1) B η Z S P r L := by
  classical
  intro t ht
  obtain ⟨hmem,hbad⟩:=Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨hmem,badAt_halfopen Γ v c₀ C₀ B η Z P t hZ hcZ hbad⟩

variable [IsTopologicalGroup G]
variable (hsk : SecondKind c)
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)

include hsk hΓ htop in
 

theorem source_literal_bound (v D : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η)
    (w : ℕ→ℕ) (S Z : ℕ→ℝ) (r L : ℕ→ℤ)
    (hw : Tendsto w atTop atTop) (hS : Tendsto S atTop atTop)
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun n=>Z n/S n^a) atTop atTop)
    (hL : ∀ n,0<L n) (hsm : ∀ n,Smooth (w n) (L n))
    (hWL : ∀ n,(primorial (w n):ℤ)∣L n) (hr : ∀ n,(r n).natAbs.Coprime (primorial (w n)))
    (hSL : Tendsto (fun n=>S n/(L n:ℝ)) atTop atTop) :
    ∃ H : ℕ,0<H ∧ ∀ K : ℕ,0<K →∀ ε : ℝ,0<ε →∀ᶠ n in atTop,
      ∀ P : (Fin (v+1)→ℝ)→G,(∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D) →
      ((exceptional Γ v c₀ C₀ B η (Z n) (S n) P (r n) (L n)).card:ℝ)/
          ((RoughSourceExceptional.times (S n) (r n) (L n)).card:ℝ)≤(extremal H K:ℝ)/K+ε := by
  classical
  obtain ⟨H,hH,hbound⟩:=RoughSourceExceptional.source_exceptional_bound c Γ hsk hΓ htop
    v D (c₀/2) (C₀+1) B η (by positivity) (by positivity) hB hη
    w S Z r L hw hS hZ hL hsm hWL hr hSL
  have hZ' : Tendsto Z atTop atTop:=by
    simpa only [pow_zero,div_one] using RoughSourceExceptional.integer_scales_of_real hS hZ 0
  refine ⟨H,hH,fun K hK ε hε=>?_⟩
  filter_upwards [hbound K hK ε hε,hZ'.eventually (eventually_ge_atTop 1),
    hZ'.eventually (eventually_ge_atTop (2/c₀))] with n hbn hn hn'
  intro P hP
  have hcn : 2≤c₀*Z n:=by nlinarith [(div_le_iff₀ hc₀).mp hn']
  have hcard := Finset.card_le_card (exceptional_subset Γ v c₀ C₀ B η (Z n) (S n)
    P (r n) (L n) hn hcn)
  apply le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity))
    (hbn P hP)

end RoughLiteralBoxes

end
end
end

end OAI
