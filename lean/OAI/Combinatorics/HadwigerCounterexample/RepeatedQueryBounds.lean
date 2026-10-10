import OAI.Combinatorics.HadwigerCounterexample.BatchCharacters

namespace OAI

/-! # Repeated Query Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Function Finset
open scoped BigOperators
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {N : ℕ}

private theorem num_cross_peak (E : Rail (I×J))
    (he : ∀ i∈E,i.1.1≠i.2.1) (t : ℕ) :
    nbr (fun v : Vec E=> peak (ledgerM E v)=t) ≤ bp (peakExpense I J t) := by
  classical
  let Γ := fun M : Avenue I J => interDraw M ∧ peak M=t
  have hh (v) : interDraw (ledgerM E v) := fun i j k => within_recorded E v _ _
    (fun h => he _ h rfl)
  rw [nbr_eq_card]
  apply le_trans _ (price_peak (I:=I) (J:=J) t)
  rw [nbr_eq_card]
  let f (v : {v : Vec E//peak (ledgerM E v)=t}) : { M//Γ M} :=
    ⟨ledgerM E v.val, hh _,v.property⟩
  have h : Injective f := by
    intro v w he
    apply Subtype.ext
    have h : ledgerM E v.val=ledgerM E w.val := congrArg Subtype.val he
    rw [←inLedger E v.val,h,inLedger]
  exact_mod_cast Fintype.card_le_of_injective f h

private theorem peak_sum (E : Rail (I×J))
    (he : ∀ i∈E,i.1.1≠ i.2.1) (u : ℝ)
    (h : peakExpense I J 1+u≤0) :
    ∑ v : Vec E,bp (u*peak (ledgerM E v))≤num (I×J)+1 := by
  classical
  let T := Fintype.card (I×J)
  let f (v : Vec E) : Fin (T+1) :=
     ⟨peak (ledgerM E v), Nat.lt_succ_of_le (peak_le _)⟩
  have hg : ∑ v : Vec E,bp (u*peak (ledgerM E v))=
      ∑ i : Fin (T+1),bp (u*i.val) * nbr (fun v : Vec E => peak (ledgerM E v)=i.val) := by
    unfold nbr tot; simp only [Finset.mul_sum]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_eq_single (f v)]
    · simp only [f,ind_true,mul_one]
    · intro i _ hi; rw [ind_zero (show peak _≠i.val from
        fun h => hi (Fin.ext h.symm)),mul_zero]
    simp
  have hi (i : Fin (T+1)) :
      bp (u*i.val)*nbr (fun v : Vec E=>peak (ledgerM E v)=i.val) ≤ 1 := by
    refine (mul_le_mul_of_nonneg_left (num_cross_peak E he i.val) (bp_pos _).le).trans ?_
    rw [←bp_add,←bp_zero]
    apply bp_le
    unfold peakExpense at *
    have h1 := mul_nonpos_of_nonpos_of_nonneg h (Nat.cast_nonneg i.val : 0≤(i.val:ℝ))
    norm_num at h1
    linarith only [h1]
  rw [hg]
  exact (Finset.sum_le_sum fun i _ => hi i).trans_eq (by simp [num,T])

set_option maxHeartbeats 800000 in
theorem cross_flood (E : Rail (I×J)) (Z : Vec E)
    (he : ∀ i∈E,i.1.1≠ i.2.1) (u : ℝ) (hu : 0≤u)
    (P : I → Rack J N → Prop) (hp : ∀ i,bp (-u)≤pr unif (P i))
    (hδ : peakExpense I J 1+(-(N:ℝ)/2+2*u) ≤0) :
    pr unif (fun x => traced x E Z ∧ ∀ i,P i (led i x))≤
      bp (-(E.card:ℝ)) * (num (I×J)+1) *∏ i,pr unif (P i) := by
  classical
  let H := ∏ i,pr unif (P i)
  have hg : 0≤H := Finset.prod_nonneg fun _ _ => pr_nonneg unif_law.nz
  let C : ℝ := -(N:ℝ)/2+2*u
  let F (v : Vec E) :=
    vectorPhase v Z*avg unif (fun x => phasedBy (ledgerM E v) x*phot P x)
  have hh v : F v ≤ bp (C*peak (ledgerM E v))*H := by
    refine (le_abs_self _).trans ?_
    unfold F; rw [abs_mul,vectorPhase,wsign_abs,one_mul]
    exact light_bound _ P u hu hp
  have heq : pr unif (fun x => traced x E Z ∧ ∀ i,P i (led i x))=
      avg unif F := by
    unfold pr F
    simp_rw [ind_and,ind_all,rail_expand,← avg_mul,← avg_mul']
    rw [avg_avg]
    refine avg_congr fun v _ => avg_congr fun x _ => ?_
    unfold phot; ring
  rw [heq]
  refine (avg_mono unif_law.nz hh).trans ?_
  let lamh := bp (-(E.card:ℝ))
  have he' (x : Vec E) :
      unif x=lamh := by rw [unif_apply,card_space,dim_vec,Fintype.card_coe, ← bp_neg]
  simp only [avg,he',← Finset.mul_sum]
  rw [← Finset.sum_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (peak_sum E he _ hδ) hg)
    (bp_pos _).le

def cInside (g : Route (I×J) G) :=
  (crowded g).filter (fun i => i.1.1=i.2.1)

omit [Fintype G] in
theorem inside_count (g : Route (I×J) G) :
    (cInside g).card≤ Fintype.card I*Fintype.card J*Fintype.card J := by
  classical
  let f : I×J×J → (I×J)×(I×J) := fun x => ((x.1,x.2.1),(x.1,x.2.2))
  have h : cInside g ⊆ Finset.univ.image f := by
    rintro ⟨⟨x,i⟩,y,j⟩ hv
    obtain rfl : x=y := (mem_filter.mp hv).2
    exact mem_image.mpr ⟨(x,i,j),mem_univ _,rfl⟩
  exact (card_le_card h).trans (card_image_le.trans_eq (by simp [mul_assoc]))

set_option maxHeartbeats 800000 in
theorem many_frames (g : Route (I×J) G) (Z : GeoM g) (hN : ∀ i,2*num (Port g i)-N≤ -1)
    (u : ℝ) (hu : 0≤u) (P : I→Rack J N→Prop) (hp : ∀ i,bp (-u) ≤ pr unif (P i))
    (hd : peakExpense I J 1+ (-(N:ℝ)/2+2*u) ≤0) :
    pr (rackStation Z N) (fun x => ∀ i,P i (led i x))≤
      (4:ℝ)^Fintype.card G * bp (num I * num J * num J) * (num (I×J)+1) *
        ∏ i:I,pr unif (P i) := by
  classical
  let E := crowded g
  let Y := cInside g
  let R := E\Y
  have hn := (net_norm Z N hN).1
  let Z' := directions g Z
  let w (x : R) := Z' ⟨x.val,sdiff_subset x.property⟩
  have hl (x : Rack (I×J) N) (h : gramPart Z x) :
      traced x R w := by
    have he := (match_crowd x g Z).mpr h
    funext i
    exact congr_fun he (⟨i.val,sdiff_subset i.property⟩ : ↑E)
  have he i (h : i∈R) : i.1.1≠ i.2.1 := by
    intro hx
    obtain ⟨h1,h2⟩ := Finset.mem_sdiff.mp h
    exact h2 (Finset.mem_filter.mpr ⟨h1,hx⟩)
  let Q := fun x => ∀ i, P i (led i x)
  let H := ∏ i,pr unif (P i)
  have h0 := netFact_pos (f:=g)
  unfold rackStation
  rw [← on_unif, pr_on]
  have hh : pr unif (fun x => bothPart (N:=N) Z x ∧ Q x) ≤
      pr unif (fun x => traced x R w ∧ Q x) :=
    pr_mono unif_law.nz (fun x h => ⟨hl x ((both_test ..).mp h.1).1,h.2⟩)
  have hf := cross_flood R w he u hu P hp hd
  refine le_trans (div_le_div₀ ((pr_nonneg unif_law.nz).trans hf)
    (hh.trans hf) (inv_pos_of_pos h0) hn) ?_
  let K : ℝ := num (I×J)+1
  have hk : 0 ≤ K := by unfold K num; positivity
  change bp (- (R.card:ℝ)) * K * H / (netFact g)⁻¹ ≤ (4:ℝ)^_ * _ * K * H
  have hY : Y ⊆ E := Finset.filter_subset ..
  have hy : (R.card:ℝ)+(Y.card:ℝ) = netSize g := by
    rw [← rail_count]; exact_mod_cast Finset.card_sdiff_add_card_eq_card hY
  have hY' : (Y.card:ℝ) ≤ num I * num J * num J := by exact_mod_cast inside_count g
  unfold netFact
  have hg : 0 ≤ H := Finset.prod_nonneg fun i _ => pr_nonneg unif_law.nz
  calc _ = (4:ℝ)^Fintype.card G * bp (netSize g- (R.card:ℝ))*K*H := by
            rw [div_eq_mul_inv,inv_inv,bp_sub,bp_neg]; ring
       _ ≤ _ := by gcongr; linarith
end HadwigerCounterexample

end

end OAI
