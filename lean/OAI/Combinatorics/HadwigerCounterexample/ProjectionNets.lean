import OAI.Combinatorics.HadwigerCounterexample.RoundedRefinements

namespace OAI

/-! # Projection Nets -/

noncomputable section
namespace HadwigerCounterexample
open Finset Filter Matrix Real Function
open scoped BigOperators
variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

theorem stamina_equiv (p : Wgt A) (e : A≃C) (a : ℝ)
    (h : stamina p a) :
    stamina (mapW p e) a := by
  intro i hi; rw [mapW_equiv_val] at *
  exact h _ hi

theorem tension_equiv (p q : Wgt A) (e : A≃C) :
    tension (mapW p e) (mapW q e)=tension p q := by
  unfold tension
  rw [mapW_avg]
  simp_rw [mapW_equiv_val,Equiv.symm_apply_apply]

theorem budget_equiv (μ : Wgt A) (p : A → Wgt B) (f : B→C) (e : C≃D) :
    budget μ p (e ∘ f)=budget μ p f := by
  unfold budget
  simp_rw [←map_nested f _,tension_equiv]

def ample (μ : Wgt A) (p : A→Wgt B) (r : ℕ) (ε : ℝ) :=
  ∃ t : ℕ,t ≤ r ∧ ∃ f : B → Fin t,∀ w,catalog μ p w →
    varOne w (bucket unif f w) ≤ ε

set_option maxHeartbeats 800000 in
theorem ample_thresh (V ε : ℝ) (hε : 0<ε) :
    ∃ (r : ℕ) (δ : ℝ),0<δ ∧ ∀ (A B : Type) [Fintype A] [Fintype B] [Nonempty B]
      (μ : Wgt A) (p : A→ Wgt B), Ultra μ p →
      tariffs μ p r δ V → ample μ p r ε := by
  classical
  let c := ε/8
  have hc : 0<c := by positivity
  obtain ⟨α,hα,hα',hh⟩ := ui_threshold V c hc
  obtain ⟨D,hD⟩ := exists_nat_gt (max 0 (V/c^2))
  have hd := (max_lt_iff.mp hD).2
  rw [div_lt_iff₀ (by positivity)] at hd
  let r := 2^(D+1)
  have h0 : 0<(r:ℝ) := by unfold r; positivity
  let k := min (min α c/r) (1/2)
  have hk : 0<k := lt_min (div_pos (lt_min hα hc) h0) (by norm_num)
  have hk0 : k≤1/2 := min_le_right ..
  have hk' : k≤1 := le_trans hk0 (by norm_num)
  let δ := min α (k^D)
  have hδ : 0<δ := lt_min hα (pow_pos hk D)
  refine ⟨r,δ,hδ,fun A B _ _ _ μ p hw hV => ?_⟩
  let e : Wgt B := unif
  have he : IsLaw e := unif_law
  by_contra h
  have hr2 : 2≤r := by
    unfold r; rw [pow_succ]
    have : 0<2^D := by positivity
    omega
  have ht := hh A B μ p hw (tariffs_monotone hV hr2 (min_le_left ..))
  have hstep (n : ℕ) (hn : n≤ D) :
      ∃ f : B → Fin (2^n), stamina (mapW e f) (k^n) ∧
        ↑n*c^2 ≤ budget μ p f := by
    induction n with
    | zero =>
      let f := fun _ : B => (0 : Fin (2^0))
      refine ⟨f,?_,by simpa using budget_nonneg hw f⟩
      intro i hi
      have hi : i = 0 := by
        have hh := i.isLt; norm_num at hh
        exact Fin.ext (by simp only [Fin.val_zero]; omega)
      subst i; change 1 ≤ pr e (fun x => f x=0)
      simp [f,he.total]
    | succ i ih =>
      obtain ⟨f,hf,hB⟩ := ih (by omega)
      let t := 2^i
      have he' : ∃ w,catalog μ p w ∧ 8*c<varOne w (bucket unif f w) := by
        by_contra! hh
        apply h; refine ⟨t,Nat.pow_le_pow_right (by decide) (by omega),f,?_⟩
        rwa [show 8*c=ε by unfold c; ring] at hh
      obtain ⟨w,hw',hwv⟩ := he'
      have hz : num (Fin t × Bool)*k ≤ min α c := by
        have h1 : Fintype.card (Fin t × Bool) ≤ r :=
          calc _ = 2^(i+1) := by simp [pow_succ,t]
               _ ≤ r := Nat.pow_le_pow_right (by decide) (by omega)
        have h2 := min_le_left (min α c/r) (1/2)
        change k ≤ min α c/r at h2
        rw [le_div_iff₀ h0,mul_comm k] at h2
        exact (mul_le_mul_of_nonneg_right (by exact_mod_cast h1) hk.le).trans h2
      obtain ⟨F,hF',hF⟩ := divide_progress hw c (k^i) α k hc hk (by linarith)
        (pow_pos hk _) (pow_le_one₀ hk.le hk') ht f hf hz w hw' hwv
      let E : (Fin t×Bool)≃ Fin (2^(i+1)) := Fintype.equivFinOfCardEq (by simp [pow_succ,t])
      refine ⟨E ∘ F,?_,?_⟩
      · rw [←map_nested,pow_succ' k]; exact stamina_equiv _ E _ hF'
      rw [budget_equiv,Nat.cast_add,Nat.cast_one]; linarith only [hF,hB]
  obtain ⟨f,hf,hf'⟩ := hstep D le_rfl
  have he' : stamina (mapW unif f) δ := fun i hi => (min_le_right ..).trans (hf i hi)
  have hz := hV _ (f:=f) (by simp; unfold r; rw [pow_succ]; omega) he'
  exact (not_lt_of_ge (le_trans hf' hz)) hd
end HadwigerCounterexample

end

end OAI
