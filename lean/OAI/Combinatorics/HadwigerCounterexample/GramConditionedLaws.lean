import OAI.Combinatorics.HadwigerCounterexample.ConditionedBatchLaws

namespace OAI

/-! # Gram Conditioned Laws -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Submodule Function Finset
variable {I J G H : Type} [Fintype I] [Fintype J] [Fintype G] [Fintype H]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {g : Route (I×J) G} {N : ℕ}

omit [Fintype G] in
private theorem wav_iff (Z : GeoM g) (x : Rack (I×J) N) :
    gramPart Z x ↔ (traced x (crossroads g) (outsideZ Z) ∧
      (∀ i,gramPart (laneM Z i) (led i x))) := by
  classical
  constructor
  · intro h
    constructor
    · funext i
      exact congr_fun ((match_crowd x g Z).mpr h) (⟨i.val,Finset.sdiff_subset i.property⟩ :
      ↑(crowded g))
    intro i; refine (part_scores ..).mpr fun q a b => ?_
    exact (part_scores ..).mp h q (condLane g i q a) (condLane g i q b)
  rintro ⟨ht,hH⟩
  refine (part_scores ..).mpr ?_
  intro i a b
  rcases a with ⟨⟨l,x'⟩,hl⟩
  rcases b with ⟨⟨t,y⟩,hr⟩
  subst i
  let j := g (l,x')
  by_cases hh : l=t
  · subst t
    let a : Port (street g l) j := ⟨x',rfl⟩
    let b : Port (street g l) j := ⟨y,hr⟩
    exact (part_scores ..).mp (hH l) j a b
  let z : I×J := (l,x')
  let v : I×J := (t,y)
  have hv : (z,v)∈crossroads g := Finset.mem_sdiff.mpr
    ⟨Finset.mem_filter.mpr ⟨mem_univ _,hr.symm⟩,fun h => hh (mem_filter.mp h).2⟩
  exact congr_fun ht (⟨(z,v),hv⟩ : ↑(crossroads g))

def partMean (p : H→Prop) (f : Wgt H) :=
  avg unif (fun x => ind (p x)*f x)
theorem part_reset [Nonempty H] (p : H→Prop) (f : Wgt H) (h : 0<pr unif p) :
    partMean p f=pr unif p * avg (unifOn p) f := by
  rw [←on_unif]; unfold onW
  rw [avg_norm,subW_tot]
  have he : partMean p f = avg (subW unif p) f := by simp only [avg,subW,mul_assoc]; rfl
  rw [he]
  field_simp

omit [Fintype G] in
set_option maxHeartbeats 600000 in
private theorem wav_means (Z : GeoM g) (f : I → Wgt (Rack J N)) (hf : ∀ i x,|f i x|≤1) :
    |partMean (gramPart Z) (brightProd f) - bp (-( (crossroads g).card:ℝ)) *
      ∏ i,partMean (gramPart (laneM Z i)) (f i)|≤bp (-(N:ℝ)/2) := by
  classical
  let E := crossroads g
  let F i (x : Rack J N) := ind (gramPart (laneM Z i) x)*f i x
  have hF i x : |F i x|≤1 := by
    unfold F; by_cases h : gramPart (laneM Z i) x <;> simp only [h,ind_true,ind_false,one_mul,
      zero_mul]; exact hf i x; norm_num
  have hE i (h : i∈E) : i.1.1≠i.2.1 := fun he =>
    (mem_sdiff.mp h).2 (mem_filter.mpr ⟨(mem_sdiff.mp h).1,he⟩)
  have ht := speed_expand F hF E (outsideZ Z) hE
  have hP : avg unif (brightProd F)=∏ i, partMean (gramPart (laneM Z i)) (f i) :=
    (led_uniform (prodW F)).trans (prodW_avg _ _)
  let A x := ind (traced x E (outsideZ Z))*brightProd F x
  have hi x :
      ind (gramPart Z x) * brightProd f x= A x := by
    rw [wav_iff]; unfold A F E
    simp only [ind_and, ind_all,brightProd,Finset.prod_mul_distrib]
    ring
  rw [hP] at ht
  change |avg unif _-_ *∏ i,partMean _ _|≤_
  simp_rw [hi]
  exact ht

omit [DecidableEq I] in
theorem wave_lane_norm (Z : GeoM g) (hN : ∀ i, 2*num (Port g i)-(N:ℝ)≤ -1)
    (i : I) : 0<pr unif (gramPart (laneM Z i) (N:=N)) :=
  (lane_norm Z hN i).trans_le (pr_mono unif_law.nz fun _ hx => ((both_test ..).mp hx).1)

theorem lane_collapse (A P u V e C : ℝ)
    (h0 : 0<C) (hA : C⁻¹ ≤ A) (hV : |V|≤1)
    (h1 : |A*u-P*V|≤e) (h2 : |A-P|≤e) :
    |u-V|≤2*C*e := by
  have hg : A * |u-V|≤2*e := by
    have hh : |(A-P)*V|≤e := by
      rw [abs_mul]; exact ((mul_le_mul_of_nonneg_left hV (abs_nonneg _)).trans_eq (mul_one _)).trans h2
    calc A*|u-V|= |(A*u-P*V)-(A-P)*V| := by
                 rw [show A*u-P*V-(A-P)*V=(A*(u-V)) by ring,abs_mul,abs_of_nonneg
                   (le_trans ((inv_pos_of_pos h0).le) hA)]
         _ ≤ _ := ((abs_sub ..).trans (add_le_add h1 hh)).trans_eq (two_mul _).symm
  apply le_of_mul_le_mul_left _ (inv_pos_of_pos h0)
  exact ((mul_le_mul_of_nonneg_right hA (abs_nonneg _)).trans hg).trans_eq (by field_simp)

set_option maxHeartbeats 800000 in
theorem compare_waves (Z : GeoM g) (f : I→ Wgt (Rack J N)) (hf : ∀ i x,|f i x|≤1)
    (hN : ∀ i,2*num (Port g i)-(N:ℝ)≤ -1) :
    |avg (rackWave Z N) (brightProd f)- ∏ i,avg (rackWave (laneM Z i) N) (f i)|≤
      2*netFact g*bp (-(N:ℝ)/2) := by
  classical
  let A := pr unif (gramPart (N:=N) Z)
  let B i := pr unif (gramPart (N:=N) (laneM Z i))
  let u := avg (rackWave Z N) (brightProd f)
  let v i := avg (rackWave (laneM Z i) N) (f i)
  let P := bp (- ((crossroads g).card:ℝ))*(∏ i, B i)
  let V := ∏ i,v i
  have hV : |V|≤1 := by
    unfold V
    rw [Finset.abs_prod]
    have he (i) :
        SubLaw (rackWave (laneM Z i) N) := unifOn_sub _
    refine (Finset.prod_le_prod₀ (fun i _ => abs_nonneg _)
      (fun i _ => (abs_avg_le (he i).nz).trans ((he i).avg_le zero_le_one (hf i)))).trans_eq ?_
    simp
  have hh := wave_norm Z N hN
  have h0 : 0<A := (inv_pos_of_pos netFact_pos).trans_le hh
  let e := bp (-(N:ℝ)/2)
  have h1 : |A*u-P*V|≤e := by
    have hb := wave_lane_norm (N:=N) Z hN
    have ht := wav_means Z f hf
    rw [part_reset (gramPart (N:=N) Z) _ h0] at ht
    simp_rw [part_reset _ _ (hb _)] at ht; rw [Finset.prod_mul_distrib] at ht
    simpa only [A,B,u,v,P,V,rackWave,mul_assoc] using ht
  have h2 : |A-P|≤ e := by
    let F (i:I) := fun _ : Rack J N => (1:ℝ)
    have ht := wav_means Z F (by intro i x; simp [F])
    have he (i : I) :
        partMean (gramPart (laneM Z i)) (F i)=B i := by simp only [F,partMean,mul_one]; rfl
    have hx :
        partMean (gramPart (N:=N) Z) (brightProd F)=A := by
      simp only [F,brightProd,partMean,Finset.prod_const_one,mul_one,A,pr]
    simp_rw [he,hx] at ht; exact ht
  exact lane_collapse A P u V e _ netFact_pos hh hV h1 h2

set_option maxHeartbeats 500000 in
theorem compare_station {g : Route J G} (Z : GeoM g) (f : Wgt (Rack J N))
    (hf : ∀ x,|f x|≤1) (k : ℝ) (hk : ∀ i,num (Port g i)≤ k)
    (hN : 2*k-(N:ℝ)≤ -1) :
    |avg (rackStation Z N) f- avg (rackWave Z N) f| ≤
      2 * netFact g * (num G*(2*bp (k-N))) := by
  classical
  have hh i : 2*num (Port g i)-(N:ℝ)≤ -1 := by linarith only [hk i,hN]
  let A := pr unif (bothPart Z (N:=N))
  let B := pr unif (gramPart Z (N:=N))
  let Q := avg (rackWave Z N) f
  let W := avg (rackStation Z N) f
  let e := num G*(2*bp (k-N))
  have he (f : Wgt (Rack J N)) (hf : ∀ x,|f x|≤1) :
      |partMean (bothPart Z) f-partMean (gramPart Z) f|≤ e := by
    unfold partMean
    rw [←avg_sub]
    have hi (x : Rack J N) :
        |ind (bothPart Z x)*f x-ind (gramPart Z x)*f x| ≤ ind (¬injPart g x) := by
      rw [both_test]
      by_cases h : injPart g x
      · simp only [h,and_true,not_true,ind_false,sub_self,abs_zero,le_refl]
      by_cases h' : gramPart Z x
      · simpa [h,h',ind] using hf x
      simp [h,h',ind]
    exact (abs_avg_le unif_law.nz).trans
      ((avg_mono unif_law.nz hi).trans (injPart_failure g N k hk))
  have hx := (net_norm Z N hh).1
  have hA : 0<A := (inv_pos_of_pos netFact_pos).trans_le hx
  have hB : 0<B := (inv_pos_of_pos netFact_pos).trans_le (wave_norm Z N hh)
  have h1 := he f hf
  rw [part_reset (bothPart Z) f hA,part_reset (gramPart Z) f hB] at h1
  have h2 : |A-B|≤e := by
    have ht := he (fun i => 1) (by intro i; norm_num)
    simp only [partMean,mul_one] at ht
    exact ht
  have h := unifOn_sub (gramPart Z (N:=N))
  exact lane_collapse A B W Q e _ netFact_pos hx
    ((abs_avg_le h.nz).trans (h.avg_le zero_le_one hf)) h1 h2
end HadwigerCounterexample

end

end OAI
