import OAI.Combinatorics.HadwigerCounterexample.SmallCoverBounds

namespace OAI

/-! # Low Rank Kernel Alternative -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Filter
open scoped BigOperators Topology
variable {A J B : Type} [Fintype A] [Fintype J] [Fintype B]

private def rbase (a : A → Vec B) (S : Finset A) :=
  Submodule.span F (Set.image a (S : Set A))
omit [Fintype A] in
private theorem row_extract (a : A → Vec B) (S : Finset A) :
    ∃ T⊆ S,rbase a T=rbase a S ∧ T.card=dim (rbase a T) := by
  classical
  induction S using Finset.induction with
  | empty =>
    have hh : Set.image a ((∅:Finset A):Set _) = ∅ := by ext; simp
    have he : rbase a ∅=⊥ := by unfold rbase; rw [hh,Submodule.span_empty]
    refine ⟨∅,by simp, rfl,?_⟩; rw [he]; exact (finrank_bot ..).symm
  | insert x S hx ih =>
    obtain ⟨T,hT,hR,hD⟩ := ih
    have he (S : Finset A) :
        rbase a (insert x S)= rbase a S⊔Submodule.span F ({a x} : Set _) := by
      unfold rbase
      rw [← span_union]
      congr 1
      ext; simp
    rw [he]
    by_cases h : a x∈rbase a T
    · refine ⟨T,hT.trans (Finset.subset_insert ..),?_,hD⟩
      rw [←hR,sup_eq_left.mpr (by rwa [Submodule.span_singleton_le_iff_mem])]
    refine ⟨insert x T,Finset.insert_subset_insert x hT,by rw [he,hR],?_⟩
    rw [he]
    have hh (h' : a x∉rbase a T) :=
      Submodule.finrank_sup_span_singleton h'
    rw [Finset.card_insert_of_notMem (fun e => hx (hT e)),hD]
    exact (hh h).symm

private def tilt (m u : ℝ) : Wgt F :=
  fun x => if x=0 then bp (-m) else bp (-u)

private theorem tilt_sub (m u : ℝ) (h : bp (-m)+bp (-u) ≤1) : SubLaw (tilt m u) := by
  classical
  refine ⟨fun x => ?_,?_⟩
  · unfold tilt; split <;> exact (bp_pos _).le
  unfold tot
  rw [show (Finset.univ : Finset F)={0,1} from (by ext x; simp [bit_cases])]
  simpa only [Finset.sum_insert (show (0:F)∉({1}:Finset _) by simp), tilt,ite_true,
    Finset.sum_singleton, ite_eq_right (show (1:F) ≠ 0 from one_ne_zero)] using h

theorem draws_sub {K : Type} [Fintype K] [DecidableEq K] (w : Wgt A) (h : SubLaw w) :
    SubLaw (draws K w) := by
  refine ⟨prodW_nonneg (fun _ => h.nz),?_⟩
  rw [draws,prodW_tot]
  refine (Finset.prod_le_prod₀ (g:=fun _ => 1) (fun _ _ => tot_nonneg h.nz) (fun _ _ => h.total)).trans_eq
    (by simp)

private theorem tilted_fiber [DecidableEq J] (w : Wgt A) (f : A → Vec J)
    (v m u η : ℝ) (hh : 0<v)
    (hw : IsLaw w)
    (hm : 0<m) (hu : 0<u) (hp : bp (-m)+bp (-u)≤1)
    (he : Fintype.card J*(u+m*η)≤v/2)
    (h : ∀ i,pr w (fun x => f x i=0)≤η) :
    ∃ z : Vec J,bp (-v)/4 ≤ pr w (fun x => f x=z) := by
  classical
  let d (i : F) := u+m*ind (i=0)
  let c (v : Vec J) := ∑ i,d (v i)
  have hd i : 0 ≤ d i := add_nonneg hu.le (mul_nonneg hm.le (ind_nonneg _))
  have hc :
      avg w (fun x => c (f x)) ≤ v/2 := by
    unfold c; rw [avg_sum]
    refine (Finset.sum_le_sum (g:=fun _ => u+m*η) fun i _ => ?_).trans ?_
    · simp only [d,avg_add,avg_mul',hw.avg_const]
      exact add_le_add_right (mul_le_mul_of_nonneg_left (h _) hm.le) _
    simpa [mul_add] using he
  let H (x : Vec J) := ¬ v≤ c x
  let W := mapW w f
  have h1 : (1/2:ℝ) ≤ pr W H := by
    rw [mapW_pr,show (fun x => H (f x))=(fun x => ¬ v≤c (f x)) from rfl,
      pr_not,hw.total]
    have heq := (le_avg_markov hw.nz (f:=fun x => c (f x))
      (fun x => Finset.sum_nonneg (fun i _ => hd _)) v).trans hc
    apply le_of_mul_le_mul_right _ hh; linarith only [heq]
  let t : Wgt (Vec J) := draws J (tilt m u)
  have hk (x : Vec J) : H x → bp (-v) ≤ t x := by
    intro h'
    apply le_trans (bp_le (show -v ≤ -c x from neg_le_neg (le_of_not_ge h')))
    unfold c t draws prodW
    rw [← Finset.sum_neg_distrib,bp_sum]
    refine Finset.prod_le_prod₀ (fun i _ => (bp_pos _).le) fun i _ => ?_
    by_cases he : x i=0
    · simp only [tilt,d,he,ite_true,ind_true,mul_one]
      exact bp_le (by linarith)
    simp only [d,tilt,ite_eq_right he,ind_zero he,mul_zero,add_zero,le_refl]
  by_contra! hz
  have hi x : W x*ind (H x)≤t x * (1/4) := by
    by_cases h : H x
    · rw [ind_one h,mul_one]
      apply le_trans (hz x).le
      simpa only [div_eq_mul_inv,one_mul] using div_le_div_of_nonneg_right (hk x h)
        (show 0 ≤ (4:ℝ) by norm_num)
    · rw [ind_zero h,mul_zero]
      exact mul_nonneg ((draws_sub _ (tilt_sub m u hp)).nz _) (by norm_num)
  have ht : SubLaw t := draws_sub _ (tilt_sub m u hp)
  have h2 := h1.trans ((Finset.sum_le_sum (s:=Finset.univ) fun i _ => hi i).trans
    (ht.avg_le (show (0:ℝ) ≤ 1/4 by norm_num) (fun _ => le_rfl)))
  norm_num at h2

set_option maxHeartbeats 800000 in
theorem fiber_growth (d : ℝ) (c : ℝ) (hc : 0<c) (hd : 0≤d) :
    ∃ θ : ℝ,0<θ ∧ ∀ᶠ N : ℕ in atTop,∀ (A : Type) [Fintype A]
    (P : Mat A A) (w : Wgt A), IsLaw w → (P.rank : ℝ) ≤ d*N →
      (∀ x,P x x=0) →
      pr (pairW w w) (fun x => P x.1 x.2=0)≤ θ →
      ∃ S : A→Prop, bp (-c*N) ≤ pr w S ∧ ∀ x,S x → ∀ y,S y → P x y=0 := by
  classical
  let u := c /(16*(d+1))
  have hu : 0 < u := div_pos hc (by linarith)
  obtain ⟨m,hm,hp⟩ : ∃ m : ℝ,0<m ∧ bp (-m)+bp (-u) ≤1 := by
    have hh : 0 < 1-bp (-u) := sub_pos.mpr ((bp_lt (neg_lt_zero.mpr hu)).trans_eq bp_zero)
    have he := (bp_nat_vanish (by norm_num : 0<(1:ℝ))).eventually (gt_mem_nhds hh)
    obtain ⟨n,hn,hN⟩ := (he.and (eventually_gt_atTop 0)).exists
    refine ⟨n,Nat.cast_pos.mpr hN,?_⟩
    have he' : bp (-(n:ℝ))<1-bp (-u) := by simpa using hn
    linarith
  let θ := u/(4*m)
  have ht : 0<θ := div_pos hu (by linarith)
  refine ⟨θ,ht,?_⟩
  filter_upwards [eventually_gt_atTop 0,tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (8/c))] with N hN h A _ P w hw hP hz hp'
  let f (x : A) := pr w (fun y => P x y=0)
  let Q : Finset A := Finset.univ.filter (fun x => ¬ 2*θ ≤ f x)
  have hq : (1/2:ℝ) ≤ pr w (fun x => x∈Q) := by
    have hg : avg w f ≤ θ := by rw [pr,pairW_avg] at hp'; exact hp'
    have hi := (le_avg_markov hw.nz (f:=f) (fun x => pr_nonneg hw.nz) (2*θ)).trans hg
    simp only [Q,Finset.mem_filter,Finset.mem_univ,true_and,pr_not,hw.total]
    apply le_of_mul_le_mul_right _ ht; linarith only [hi]
  let v := onW w (fun x => x∈Q)
  obtain ⟨T,hT,hR,hM⟩ := row_extract (P.row) Q
  have hM' : ↑T.card ≤ d*N := by
    rw [hM]
    have hg : rbase P.row T≤colSp Pᵀ := by
      apply Submodule.span_le.mpr
      rintro y ⟨x,hx,rfl⟩; exact colSp_mem (P:=Pᵀ) x
    have hi := Submodule.finrank_mono hg
    change dim _ ≤ Pᵀ.rank at hi; rw [Matrix.rank_transpose] at hi
    exact le_trans (Nat.cast_le.mpr hi) hP
  let g (x : A) : Vec T := fun j => P j.val x
  let E (x : A) := x∈Q
  have hpc : 0<pr w E := by linarith
  have he (i : ↑T) : pr v (fun x => g x i=0)≤4*θ := by
    have h : f i.val ≤ 2*θ := le_of_not_ge (Finset.mem_filter.mp (hT i.property)).2
    unfold v
    rw [pr_on]; refine (div_le_iff₀ hpc).mpr ?_
    apply le_trans _ (le_trans h ?_)
    · exact pr_mono hw.nz fun x => And.right
    nlinarith only [mul_le_mul_of_nonneg_left hq ht.le]
  let x := c*N/2
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hx : 0<x := div_pos (mul_pos hc hn) (by norm_num)
  have ht' : (↑(Fintype.card ↑T):ℝ)*(u+m*(4*θ))≤x/2 := by
    rw [Fintype.card_coe]
    have hθ : u+m*(4*θ) = 2*u := by unfold θ; field_simp; ring
    rw [hθ]; refine (mul_le_mul_of_nonneg_right hM' (by linarith)).trans ?_
    have hu' : u*(16*(d+1))=c := by unfold u; field_simp
    unfold x
    rw [←hu']
    nlinarith
  obtain ⟨z,hZ⟩ := tilted_fiber v g x m u (4*θ) hx (on_law hw.nz hpc) hm hu hp ht' he
  refine ⟨fun x => E x∧g x=z,?_,fun x hx y hy => ?_⟩
  · rw [pr_of_on hw.nz E]
    calc bp (-c*N) ≤ (1/2)*(bp (-x)/4) := by
           have hq : bp (-c*N) ≤ bp (-3+ -x) := bp_le (by
             change (8/c) ≤ (N:ℝ) at h
             have he := (div_le_iff₀ hc).mp h
             unfold x; linarith only [he])
           rw [bp_add,bp_neg,show (3:ℝ)=↑(3:ℕ) from by norm_num,bp_nat] at hq
           linarith only [hq]
         _ ≤ _ := mul_le_mul hq hZ (div_nonneg (bp_pos _).le (by norm_num)) hpc.le
  · have hv (x y : A) (h : g x=g y) :
        ∀ i∈Q,P i x=P i y := by
      let f := LinearMap.proj (R:=HadwigerCounterexample.F) (φ:=fun _ : A => HadwigerCounterexample.F) x
      let f' := LinearMap.proj (R:=HadwigerCounterexample.F) (φ:=fun _ : A => HadwigerCounterexample.F) y
      have hh : rbase P.row T ≤ LinearMap.ker (f-f') := by
        refine Submodule.span_le.mpr ?_
        rintro v ⟨i,hi,rfl⟩
        exact sub_eq_zero.mpr (congr_fun h (⟨i,hi⟩ : T))
      intro i hi
      rw [hR] at hh
      exact sub_eq_zero.mp (hh (Submodule.subset_span ⟨i,hi,rfl⟩))
    rw [← hv x y (hx.2.trans hy.2.symm) x hx.1,hz]
end HadwigerCounterexample

end

end OAI
