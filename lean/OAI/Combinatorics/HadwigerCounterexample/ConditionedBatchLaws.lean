import OAI.Combinatorics.HadwigerCounterexample.IndependentWeightCorrelation

namespace OAI

/-! # Conditioned Batch Laws -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Submodule Function Finset
variable {I J G H : Type} [Fintype I] [Fintype J] [Fintype G] [Fintype H]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {N : ℕ}

def street (g : Route (I×J) G) (i : I) : Route J G := fun j => g (i,j)
def condLane (g : Route (I×J) G) (i : I) (z : G) (k : Port (street g i) z) :
    Port g z := ⟨(i,k.val),k.property⟩
def laneM {g : Route (I×J) G} (Z : GeoM g) (i : I) :
    GeoM (street g i) :=
  fun z => (Z z).submatrix (condLane g i z) (condLane g i z)

private theorem cut_inj {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    (A : PlusRack I N) (h : Injective A.mulVec) {g : J→I} (hg : Injective g) :
    Injective (A.submatrix _root_.id g).mulVec := by
  rw [← mul_embedMat]
  exact inj_comp_mat _ _ h (embedMat_inj hg)

variable {g : Route (I×J) G}

omit [Fintype G] in
set_option maxHeartbeats 600000 in
theorem laneGram (Z : GeoM g) (x : Rack (I × J) N) (h : bothPart Z x) (i : I) :
    bothPart (laneM Z i) (led i x) := by
  classical
  obtain ⟨hh,hj⟩ := (both_test ..).mp h
  apply (both_test ..).mpr
  constructor
  · refine (part_scores ..).mpr fun q a b => ?_
    exact (part_scores ..).mp hh q (condLane g i q a) (condLane g i q b)
  intro j
  let f := condLane g i j
  have he : Injective f := by intro a b h; exact Subtype.ext (congrArg
    (fun x : Port g j => x.val.2) h)
  exact ⟨cut_inj (rackEquiv g N x j).1 (hj j).1 he,
    cut_inj (rackEquiv g N x j).2 (hj j).2 he⟩

def crossroads (g : Route (I×J) G) :=
  (crowded g)\(cInside g)
def outsideZ (Z : GeoM g) : Vec (crossroads g) :=
  fun x => directions g Z ⟨x.val,Finset.sdiff_subset x.property⟩

omit [Fintype G] in
private theorem road_iff (Z : GeoM g) (x : Rack (I×J) N) :
    bothPart Z x ↔ (traced x (crossroads g) (outsideZ Z) ∧
      (∀ i,bothPart (laneM Z i) (led i x))) ∧injPart g x := by
  classical
  constructor
  · intro h
    have ht := (both_test ..).mp h
    refine ⟨⟨?_,laneGram Z x h⟩,ht.2⟩
    funext i
    exact congr_fun ((match_crowd x g Z).mpr ht.1) (⟨i.val,Finset.sdiff_subset i.property⟩ :
      ↑(crowded g))
  rintro ⟨⟨ht,hH⟩,hf⟩
  refine (both_test ..).mpr ⟨(part_scores ..).mpr ?_,hf⟩
  intro i a b
  rcases a with ⟨⟨l,x'⟩,hl⟩
  rcases b with ⟨⟨t,y⟩,hr⟩
  subst i
  let j := g (l,x')
  by_cases hh : l=t
  · subst t
    let a : Port (street g l) j := ⟨x',rfl⟩
    let b : Port (street g l) j := ⟨y,hr⟩
    exact (part_scores ..).mp ((both_test ..).mp (hH l)).1 j a b
  let z : I×J := (l,x')
  let v : I×J := (t,y)
  have hv : (z,v)∈crossroads g := Finset.mem_sdiff.mpr
    ⟨Finset.mem_filter.mpr ⟨mem_univ _,hr.symm⟩,fun h => hh (mem_filter.mp h).2⟩
  exact congr_fun ht (⟨(z,v),hv⟩ : ↑(crossroads g))

private def condMean (p : H→Prop) (f : Wgt H) :=
  avg unif (fun x => ind (p x)*f x)
private theorem cond_reset [Nonempty H] (p : H→Prop) (f : Wgt H) (h : 0<pr unif p) :
    condMean p f=pr unif p * avg (unifOn p) f := by
  rw [←on_unif]; unfold onW
  rw [avg_norm,subW_tot]
  have he : condMean p f = avg (subW unif p) f := by simp only [avg,subW,mul_assoc]; rfl
  rw [he]
  field_simp

def twinkle (_ : Route (I×J) G) (k : ℝ) (N : ℕ) :=
  num G * (2*bp (k-N))+bp (-(N:ℝ)/2)

set_option maxHeartbeats 800000 in
private theorem lane_means (Z : GeoM g) (f : I → Wgt (Rack J N)) (hf : ∀ i x,|f i x|≤1)
    (k : ℝ) (hk : ∀ i,num (Port g i)≤k) :
    |condMean (bothPart Z) (brightProd f) - bp (-( (crossroads g).card:ℝ)) *
      ∏ i,condMean (bothPart (laneM Z i)) (f i)|≤twinkle g k N := by
  classical
  let E := crossroads g
  let F i (x : Rack J N) := ind (bothPart (laneM Z i) x)*f i x
  have hF i x : |F i x|≤1 := by
    unfold F; by_cases h : bothPart (laneM Z i) x <;> simp only [h,ind_true,ind_false,one_mul,
      zero_mul]; exact hf i x; norm_num
  have hE i (h : i∈E) : i.1.1≠i.2.1 := fun he =>
    (mem_sdiff.mp h).2 (mem_filter.mpr ⟨(mem_sdiff.mp h).1,he⟩)
  have ht := speed_expand F hF E (outsideZ Z) hE
  have hP : avg unif (brightProd F)=∏ i, condMean (bothPart (laneM Z i)) (f i) :=
    (led_uniform (prodW F)).trans (prodW_avg _ _)
  let A x := ind (traced x E (outsideZ Z))*brightProd F x
  have hA x : |A x|≤1 := by
    by_cases h : traced x E (outsideZ Z)
    · unfold A; rw [ind_one h,one_mul]; exact lane_abs F hF _ x
    unfold A; rw [ind_zero h,zero_mul]; norm_num
  have hi x :
      ind (bothPart Z x) * brightProd f x= ind (injPart g x) * A x := by
    rw [road_iff]; unfold A F
    simp only [ind_and, ind_all,brightProd,Finset.prod_mul_distrib]
    ring
  have hg :
      |condMean (bothPart Z) (brightProd f) - avg unif A|≤ num G*(2*bp (k-N)) := by
    unfold condMean
    simp_rw [hi]
    rw [← avg_sub]
    refine (abs_avg_le unif_law.nz).trans ((avg_mono unif_law.nz (g:=fun x =>
      ind (¬injPart g x)) fun i => ?_).trans (injPart_failure g N k hk))
    by_cases h : injPart g i <;>
      simp only [h,ind_true,not_true,ind_false,one_mul,sub_self,abs_zero,zero_mul,zero_sub,
        abs_neg,not_false_eq_true]; exact le_rfl; exact hA _
  rw [hP] at ht
  unfold twinkle
  apply le_trans _ (add_le_add hg ht)
  exact abs_sub_le ..

omit [DecidableEq I] in
theorem lane_norm (Z : GeoM g) (hN : ∀ i, 2*num (Port g i)-(N:ℝ)≤ -1)
    (i : I) : 0<pr unif (bothPart (laneM Z i) (N:=N)) := by
  have he j : Injective (condLane g i j) := by intro a b h; exact Subtype.ext (congrArg
    (fun x : Port g j => x.val.2) h)
  have hx j : num (Port (street g i) j)≤num (Port g j) := by
    exact_mod_cast Fintype.card_le_of_injective _ (he j)
  refine lt_of_lt_of_le (inv_pos_of_pos netFact_pos) (net_norm (laneM Z i) N (fun j => ?_)).1
  linarith only [hx j,hN j]

set_option maxHeartbeats 800000 in
theorem compare_lanes (Z : GeoM g) (f : I→ Wgt (Rack J N)) (hf : ∀ i x,|f i x|≤1)
    (k : ℝ) (hk : ∀ i,num (Port g i)≤k) (hN : ∀ i,2*num (Port g i)-(N:ℝ)≤ -1) :
    |avg (rackStation Z N) (brightProd f)- ∏ i,avg (rackStation (laneM Z i) N) (f i)|≤
      2*netFact g*twinkle g k N := by
  classical
  let A := pr unif (bothPart (N:=N) Z)
  let B i := pr unif (bothPart (N:=N) (laneM Z i))
  let u := avg (rackStation Z N) (brightProd f)
  let v i := avg (rackStation (laneM Z i) N) (f i)
  let P := bp (- ((crossroads g).card:ℝ))*(∏ i, B i)
  let V := ∏ i,v i
  have hV : |V|≤1 := by
    unfold V
    rw [Finset.abs_prod]
    have he (i) :
        SubLaw (rackStation (laneM Z i) N) := unifOn_sub _
    refine (Finset.prod_le_prod₀ (fun i _ => abs_nonneg _)
      (fun i _ => (abs_avg_le (he i).nz).trans ((he i).avg_le zero_le_one (hf i)))).trans_eq ?_
    simp
  have hh := net_norm Z N hN
  have h0 : 0<A := (inv_pos_of_pos netFact_pos).trans_le hh.1
  have h1 : |A*u-P*V|≤twinkle g k N := by
    have hb := lane_norm (N:=N) Z hN
    have ht := lane_means Z f hf k hk
    rw [cond_reset (bothPart (N:=N) Z) _ h0] at ht
    simp_rw [cond_reset _ _ (hb _)] at ht; rw [Finset.prod_mul_distrib] at ht
    simpa only [A,B,u,v,P,V,rackStation,mul_assoc] using ht
  have h2 : |A-P|≤ twinkle g k N := by
    let F (i:I) := fun _ : Rack J N => (1:ℝ)
    have ht := lane_means Z F (by intro i x; simp [F]) k hk
    have he (i : I) :
        condMean (bothPart (laneM Z i)) (F i)=B i := by simp only [F,condMean,mul_one]; rfl
    have hx :
        condMean (bothPart (N:=N) Z) (brightProd F)=A := by
      simp only [F,brightProd,condMean,Finset.prod_const_one,mul_one,A,pr]
    simp_rw [he,hx] at ht; exact ht
  have hg : A * |u-V|≤2*twinkle g k N := by
    have hh : |(A-P)*V|≤twinkle g k N := by
      rw [abs_mul]; exact ((mul_le_mul_of_nonneg_left hV (abs_nonneg _)).trans_eq (mul_one _)).trans h2
    calc A*|u-V|= |(A*u-P*V)-(A-P)*V| := by
                 rw [show A*u-P*V-(A-P)*V=(A*(u-V)) by ring,abs_mul,abs_of_nonneg h0.le]
         _ ≤ _ := ((abs_sub ..).trans (add_le_add h1 hh)).trans_eq (two_mul _).symm
  apply le_of_mul_le_mul_left _ (inv_pos_of_pos (netFact_pos (f:=g)))
  exact ((mul_le_mul_of_nonneg_right hh.1 (abs_nonneg _)).trans hg).trans_eq (by
    have h := netFact_pos (f:=g)
    field_simp)

end HadwigerCounterexample

end

end OAI
