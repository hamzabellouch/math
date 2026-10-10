import OAI.Combinatorics.HadwigerCounterexample.EmpiricalInformation

namespace OAI

/-! # Repeated Query Energy -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C X J : Type} [Fintype A] [Fintype B] [Fintype X] [Fintype J]
variable [DecidableEq J]

omit [Fintype B] in
theorem path_repeat {μ : Wgt A} {w : Wgt X} (f : A→ X→B) :
    mixW μ (fun i => draws J (mapW w (f i))) =
      mixW (draws J w) (fun x => mapW μ (fun i => f i ∘ x)) := by
  classical
  funext i
  have h (j : A) :
      draws J (mapW w (f j)) i=pr (draws J w) (fun x => f j ∘ x=i) := by
    simp_rw [funext_iff]
    exact Eq.symm (prodW_pr _ (fun l y => f j y=i l))
  simp_rw [mixW,h]
  exact avg_avg ..

theorem path_sub (w : Wgt X) (p : X→Prop) (f : X → Wgt A)
    (hw : SubLaw w) (hf : ∀ i,IsLaw (f i)) :
    SubLaw (mixW (subW w p) f) ∧ tot (mixW (subW w p) f)=pr w p := by
  have hh : tot (mixW (subW w p) f)=pr w p := by
    rw [mixW_tot]; simp_rw [(hf _).total,avg_const,mul_one,subW_tot]
  exact ⟨⟨fun i => avg_nonneg (subLaw_sub hw p).nz (fun j => (hf j).nz i),
    hh ▸ (pr_le_tot hw.nz).trans hw.total⟩,hh⟩

omit [Fintype A] in
theorem path_patch (w : Wgt X) (p : X→Prop) (f : X → Wgt A) :
    ∀ i,mixW w f i=mixW (subW w p) f i+mixW (subW w (fun x=>¬ p x)) f i := by
  intro i
  unfold mixW subW avg
  rw [←Finset.sum_add_distrib]; simp_rw [ind_not]
  exact sum_congr rfl fun j _ => by ring

set_option maxHeartbeats 1000000 in
theorem path_energy (μ : Wgt A) (w : Wgt X) (q : Wgt B)
    (f : A → X→B) (hμ : IsLaw μ) (hw : IsLaw w) (hq : IsLaw q)
    (h : ∀ i j,q (f i j)≠0)
    (u : ℝ) (hu : 0≤u) (hp : ∀ i,q i ≠0 → bp (-u)≤q i)
    (l : ℕ) (P : (Fin l→X)→ Prop) (r : ℝ)
    (hr : pr (draws (Fin l) w) (fun x => ¬ P x)≤r)
    (C : ℝ) (hc : 0≤C)
    (hP : ∀ x,P x→ ∀ y,mapW μ (fun i => f i ∘ x) y ≤ bp C * draws (Fin l) q y) :
    (l:ℝ)* avg μ (fun i => tension (mapW w (f i)) q) ≤
      num B*log (↑l+1)+(C+r*u*l+1)*log 2 := by
  classical
  let F (i : A) := mapW w (f i)
  let W := draws (Fin l) w
  let Q := draws (Fin l) q
  let k (x : Fin l → X) := mapW μ (fun i => f i ∘ x)
  let g := mixW (subW W P) k
  let b := mixW (subW W (fun x => ¬ P x)) k
  let V := mixW μ (fun i => draws (Fin l) (F i))
  have h0 : ∀ i, lsupp (F i) q := by
    intro i j hj; obtain ⟨t,ht,rfl⟩ := lsupp_witness hj
    exact h _ _
  have hF : ∀ i,IsLaw (F i) := fun i => mapW_law hw (f i)
  have hV : IsLaw V := mixW_law hμ (fun i => draws_law (hF i))
  have hQ : IsLaw Q := draws_law hq
  have hW : IsLaw W := draws_law hw
  have hk : ∀ i,IsLaw (k i) := fun i => mapW_law hμ _
  have h1 := traj_charge (l:=l) μ F q hμ hF h0
  have h2 : ∀ i,V i=g i+b i := by unfold V F; rw [path_repeat]; exact path_patch W P k
  have hg := path_sub W P k hW.sub hk
  have hb := path_sub W (fun x => ¬ P x) k hW.sub hk
  have h2L : 0 ≤ log (2:ℝ) := (Real.log_pos (by norm_num)).le
  have h3 : tension g Q ≤ C*log 2 := by
    have hz i : g i ≤ bp C*Q i := by
      let c := bp C*Q i
      have hc : 0≤c := mul_nonneg (bp_pos _).le (hQ.nz _)
      have he (j) : ind (P j)*k j i ≤ c := by
        by_cases h : P j
        · rw [ind_one h,one_mul]; exact hP j h i
        rw [ind_zero h,zero_mul]; exact hc
      refine le_trans ?_ (hW.avg_le he)
      simp only [g,mixW,subW,avg,mul_assoc]; rfl
    refine (tension_le_cap hg.1.nz hQ.nz _ (bp_pos _) hz).trans ?_
    rw [log_bp]
    exact (mul_le_mul_of_nonneg_right hg.1.total
      (mul_nonneg hc h2L)).trans_eq (one_mul _)
  have h4 : tension b Q ≤ r*(u*l*log 2) := by
    have hz (i : Fin l → B) : b i ≤ bp (u*l)*Q i := by
      by_cases he : Q i=0
      · have ht (j) : k j i=0 := by
          by_contra h
          obtain ⟨z,hz,rfl⟩ := lsupp_witness h
          have ht : Q (f z ∘ j) ≠ 0 := by
            change ∏ i:Fin l,q (f z (j i)) ≠0
            rw [Finset.prod_ne_zero_iff]; exact fun i _ => ‹∀ i j,q (f i j)≠0› _ _
          exact ht he
        unfold b mixW; simp_rw [ht]; rw [he,avg_zero,mul_zero]
      have hq := traj_cap q hq u hp i he
      refine (hb.1.weight_le_one i).trans ?_
      exact (le_of_eq (by rw [←bp_add,show u*l+ -u*l = 0 by ring,bp_zero])).trans
        (mul_le_mul_of_nonneg_left hq (bp_pos _).le)
    refine (tension_le_cap hb.1.nz hQ.nz _ (bp_pos _) hz).trans ?_
    rw [log_bp]
    exact mul_le_mul_of_nonneg_right (hb.2.le.trans hr)
      (by apply mul_nonneg (by positivity) h2L)
  apply h1.trans
  refine add_le_add_right ?_ _
  have h5 := tension_add_le V g b Q h2 hg.1.nz hb.1.nz
  rw [hV.total] at h5
  linarith only [h5,h4,h3]
end HadwigerCounterexample

end

end OAI
