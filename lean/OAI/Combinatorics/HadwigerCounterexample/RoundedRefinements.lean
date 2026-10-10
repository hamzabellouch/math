import OAI.Combinatorics.HadwigerCounterexample.RefinementEnergy

namespace OAI

/-! # Rounded Refinements -/

noncomputable section
namespace HadwigerCounterexample
open Finset Filter Matrix Real
open scoped BigOperators
variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

set_option maxHeartbeats 900000 in
theorem divide_fit (q : Wgt B) (hq : IsLaw q) (f : B→C) (P : B→Prop)
    (δ γ : ℝ) (hγ : 0<γ) (hz : 2*γ ≤ δ) (h : stamina (mapW q f) δ) :
    ∃ F : B→C×Bool, f=Prod.fst∘F ∧ stamina (mapW q F) γ ∧
    pr q (fun i => ¬(P i ↔ (F i).2))≤num (C×Bool)*γ := by
  classical
  let g (i : B) : C × Bool := (f i,decide (P i))
  let Q := mapW q g
  have hQ := mapW_law hq g
  have hf : f=Prod.fst∘g := rfl
  have hi (i) : mapW q f i=Q (i,true)+Q (i,false) := by
    have hs : mapW q f=mapW Q Prod.fst := hf ▸ Eq.symm (map_nested g Prod.fst)
    rw [hs]
    simp only [mapW,pr,avg,Fintype.sum_prod_type,Fintype.sum_bool]; simp [ind,Finset.sum_add_distrib]
  let s (j:C×Bool) : Bool := if Q (j.1,true) < γ then false else
    if Q (j.1,false) < γ then true else j.2
  let F (j : C × Bool) : C × Bool := (j.1,s j)
  refine ⟨F ∘ g,rfl,?_,?_⟩
  · rintro ⟨i,b⟩ h'
    have hb :
        mapW Q F (i,b)=Q (i,true)*ind (s (i,true)=b)+
          Q (i,false)*ind (s (i,false)=b) := by
      unfold mapW pr avg
      rw [Fintype.sum_prod_type, sum_eq_single i]
      · rw [Fintype.sum_bool]; simp [ind,F]
      · intro j _ hj; rw [Fintype.sum_bool]; simp [ind,F,hj]
      simp
    rw [←map_nested,hb] at h' ⊢
    by_cases hx : Q (i,true)<γ
    · cases b
      · simp only [s,hx,ite_true,ind_true,mul_one] at *
        rw [←hi] at *
        exact le_trans (by linarith only [hz,hγ]) (h i h')
      simp [s,hx,ind] at h'
    by_cases hy : Q (i,false)<γ
    · cases b
      · simp [s,hx,hy,ind] at h'
      simp only [s,hx,hy,ite_true,ite_false,ind_true,mul_one] at *
      rw [←hi] at *
      exact le_trans (by linarith only [hz,hγ]) (h i h')
    cases b
    · simpa [s,hx,hy,ind] using (le_of_not_gt hy)
    simpa [s,hx,hy,ind] using (le_of_not_gt hx)
  let R (i : C×Bool) := i.2≠s i
  have he j : (¬ (P j ↔ (F (g j)).2)) ↔ R (g j) := by
    change (¬ (P j ↔ s (g j)=true)) ↔ decide (P j)≠s (g j)
    cases s (g j) <;> simp
  have h1 (j : C×Bool) : R j→ Q j≤γ := by
    intro hj
    rcases j with ⟨i,b⟩
    by_cases hx : Q (i,true)<γ
    · cases b
      · simp [R,s,hx] at hj
      exact hx.le
    by_cases hy : Q (i,false)<γ
    · cases b
      · exact hy.le
      simp [R,s,hx,hy] at hj
    simp [R,s,hx,hy] at hj
  have hg (j) : Q j * ind (R j) ≤ γ := by
    by_cases hh : R j
    · simpa only [ind_one hh,mul_one] using h1 j hh
    rw [ind_zero hh,mul_zero]; exact hγ.le
  simp_rw [Function.comp_apply,he]
  rw [← mapW_pr]
  exact (Finset.sum_le_sum fun i _ => hg i).trans_eq (by simp only [Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,num])

theorem bucket_upper (w : Wgt B) (hw : SubLaw w) (q : Wgt B) (hq : IsLaw q)
    (f : B→ C) (δ : ℝ) (h0 : 0<δ) (hz : stamina (mapW q f) δ) :
    ∀ i,bucket q f w i ≤ δ⁻¹*q i := by
  intro i
  have he : mapW w f (f i) ≤1 := by
    exact (pr_le_tot hw.nz).trans hw.total
  unfold bucket pour
  by_cases hi : mapW q f (f i)=0
  · rw [hi,div_zero,mul_zero]; exact mul_nonneg (inv_pos_of_pos h0).le (hq.nz _)
  rw [mul_comm δ⁻¹]
  exact mul_le_mul_of_nonneg_left ((div_le_div₀ zero_le_one he h0 (hz _ hi)).trans_eq
    (one_div _)) (hq.nz _)

theorem pr_ref_delta (w : Wgt A) (hw : ∀ i,0 ≤ w i) (P Q : A→ Prop) :
    pr w P ≤ pr w Q + pr w (fun i => ¬(P i↔Q i)) :=
  (pr_mono hw (q:=fun i => Q i ∨ ¬(P i↔Q i)) fun i _ => by tauto).trans (pr_or_le hw)

variable {μ : Wgt A} {p : A →Wgt B}

set_option maxHeartbeats 1000000 in
theorem divide_progress [Nonempty B] (h : Ultra μ p)
    (ε δ α k : ℝ) (hε : 0<ε) (hk : 0<k) (hk' : 2*k≤1)
    (hδ : 0<δ) (hα : δ≤1)
    (hB : ∀ P : B→ Prop, pr unif P ≤α → pr (mixW μ p) P ≤ε)
    (f : B→ C) (hz : stamina (mapW unif f) δ)
    (hC : num (C×Bool)*k ≤min α ε)
    (w : Wgt B) (hw : catalog μ p w) (hr : 8*ε<varOne w (bucket unif f w)) :
    ∃ F : B → C×Bool, stamina (mapW unif F) (k*δ) ∧
      budget μ p f + ε^2 ≤ budget μ p F := by
  classical
  let q : Wgt B := unif
  have hq : IsLaw q := unif_law
  let v := bucket q f w
  have ht := h.cat_sub w hw
  let P (i : B) := v i < w i
  have hv (i) : 0≤v i := pour_nz _ hq.nz (map_nz ht.nz f) i
  have hh : varOne w v=2*(pr w P-pr v P) := by
    have hx : lsupp w q := fun i _ => by unfold q; rw [unif_apply]; positivity
    exact var_event w v (by rw [←map_mass w f,←map_mass v f,bucket_scale q w hq.nz hx])
  obtain ⟨F,hF,hφ,hL⟩ := divide_fit q hq f P δ (k*δ) (by positivity)
    ((le_of_eq (by rw [← mul_assoc])).trans ((mul_le_mul_of_nonneg_right hk' hδ.le).trans_eq
      (one_mul _))) hz
  refine ⟨F,hφ,?_⟩
  let Q := fun i : B => ((F i).2=true)
  let S := fun i => ¬(P i ↔ Q i)
  have h1 : pr w S ≤ ε := by
    obtain ⟨hu,he⟩ := h.cat_dom w hw
    have hs : pr q S ≤α := by
      have hμ := (le_min_iff.mp hC).1
      have : 0≤num (C×Bool) := Nat.cast_nonneg _
      exact hL.trans (by nlinarith only [this,hk,hα,hμ,
        mul_le_mul_of_nonneg_left hα (mul_nonneg this hk.le)])
    exact (pr_mono_left he S).trans (hB S hs)
  have h2 : pr v S ≤ ε := by
    have hh := (pr_cap (bucket_upper w ht q hq f δ hδ hz) S).trans
      (mul_le_mul_of_nonneg_left hL (inv_pos_of_pos hδ).le)
    exact hh.trans ((le_of_eq (by field_simp)).trans (le_min_iff.mp hC).2)
  have h3 : 2*ε < pr w Q-pr v Q := by
    have he := pr_ref_delta w ht.nz P Q
    have hr' := pr_ref_delta v hv Q P
    have heq : (fun i=>¬(Q i↔P i))=S := funext fun i => propext (by unfold S; tauto)
    rw [heq] at hr'
    change 8*ε < varOne w v at hr
    rw [hh] at hr; change pr w P≤pr w Q+pr w S at he
    linarith only [hr,h1,h2,he,hr']
  have h4 := var_pr (mapW w F) (mapW v F) (fun i:C×Bool => i.2=true)
  rw [mapW_pr,mapW_pr] at h4
  have he := budget_progress h w hw F Prod.fst
  change varOne _ (mapW (bucket q (Prod.fst ∘ F) w) F) ^ 2 ≤ _ at he
  rw [← hF] at he
  nlinarith only [he,hε,(le_trans h3.le h4)]
end HadwigerCounterexample

end

end OAI
