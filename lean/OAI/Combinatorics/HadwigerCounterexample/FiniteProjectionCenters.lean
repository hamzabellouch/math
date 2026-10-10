import OAI.Combinatorics.HadwigerCounterexample.ProjectionNets

namespace OAI

/-! # Finite Projection Centers -/

noncomputable section
namespace HadwigerCounterexample
open Finset Filter Matrix Real Function
open scoped BigOperators
variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

theorem var_pour (q : Wgt B) (f : B → C) (hq : IsLaw q) (w v : Wgt C) :
    varOne (pour q f w) (pour q f v)≤varOne w v := by
  classical
  let Q := mapW q f
  have hQ := mapW_law hq f
  let g i := |w i-v i| / Q i
  have he : varOne (pour q f w) (pour q f v)=avg Q g := by
    unfold Q
    rw [mapW_avg]
    unfold varOne avg; refine sum_congr rfl fun i _ => ?_
    simp only [pour,←mul_sub,←sub_div,abs_mul,abs_div,
      abs_of_nonneg (hq.nz i),abs_of_nonneg (hQ.nz _)]
    rfl
  rw [he]
  unfold varOne avg; refine sum_le_sum fun i _ => ?_
  by_cases hi : Q i=0
  · rw [hi,zero_mul]; exact abs_nonneg _
  exact le_of_eq (by unfold g; field_simp)

def roster (P : Wgt A→ Prop) (r : ℕ) (ε : ℝ) :=
  ∃ (t : ℕ), t ≤ r ∧ ∃ w : Fin t→ Wgt A, ∀ p,P p→ ∃ i,varOne p (w i)≤ ε

theorem roster_mono (P Q : Wgt A → Prop) (h : ∀ i,P i→Q i) (r ε)
    (hw : roster Q r ε) : roster P r ε := by
  obtain ⟨t,ht,w,hw⟩ := hw; exact ⟨t,ht,w,fun i hi => hw i (h i hi)⟩

private theorem grid_form (k : ℕ) (hk : 0<k) :
    let G := fun i : Fin (k+1) => (i.val:ℝ)/(k:ℝ)
    ∀ a : ℝ,0≤a→a≤1→∃ i,|a-G i|≤(k:ℝ)⁻¹ := by
  intro G a ha h1
  let i := ⌊a*(k:ℝ)⌋₊
  have hk : 0<(k:ℝ) := by exact_mod_cast hk
  have hx : ↑i≤a*k := Nat.floor_le (by positivity)
  have hy : i≤k := by
    exact_mod_cast (show (i:ℝ)≤k from hx.trans (by nlinarith))
  have hi : a*(k:ℝ)< (i:ℝ) +1 := Nat.lt_floor_add_one _
  refine ⟨⟨i,Nat.lt_succ_of_le hy⟩,?_⟩
  change |a-(i:ℝ)/k|≤_
  rw [abs_of_nonneg (sub_nonneg.mpr ((div_le_iff₀ hk).mpr hx))]
  refine sub_le_iff_le_add.mpr ?_
  rw [← one_div,←add_div]
  exact (le_div_iff₀ hk).mpr (by linarith only [hi])

variable {μ : Wgt A} {p : A→ Wgt B}

theorem roster_price (r : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ s : ℕ,∀ (A B : Type) [Fintype A] [Fintype B] [Nonempty B]
      (μ : Wgt A) (p : A→ Wgt B), Ultra μ p →
      ample μ p r (ε/2) → roster (catalog μ p) s ε := by
  classical
  obtain ⟨k,hk⟩ := exists_nat_gt (max 0 ((r:ℝ)/(ε/2)))
  have h0 := (max_lt_iff.mp hk).1
  have h1 : 0<ε/2 := by positivity
  have hk' := (div_lt_iff₀ h1).mp ((max_lt_iff.mp hk).2)
  have hv := grid_form k (by exact_mod_cast h0)
  refine ⟨(k+1)^r,fun A B _ _ _ μ p hw ⟨t,ht,f,h⟩ => ?_⟩
  let e := Fintype.equivFin (Fin t → Fin (k+1))
  let G (i : Fin (k+1)) := (i.val:ℝ)/(k:ℝ)
  let g (i : Fin (Fintype.card (Fin t →Fin (k+1)))) := G∘(e.symm i)
  refine ⟨Fintype.card (Fin t → Fin (k+1)),(by simp; exact Nat.pow_le_pow_right (by omega) ht),
    fun i => pour unif f (g i),fun w hw' => ?_⟩
  let Q := mapW w f
  have he := hw.cat_sub w hw'
  choose j hj using fun i : Fin t =>
    hv (Q i) (map_nz he.nz f i) ((pr_le_tot he.nz).trans he.total)
  have he : varOne Q (g (e j)) ≤ ε/2 := by
    refine le_trans (Finset.sum_le_sum (g:=fun i : Fin t => (k:ℝ)⁻¹) ?_) ?_
    · intro i _
      simp only [g,Function.comp_apply,Equiv.symm_apply_apply]
      exact hj i
    simp only [Finset.sum_const, Finset.card_univ,nsmul_eq_mul, Fintype.card_fin,
      ←div_eq_mul_inv]
    rw [mul_comm (k:ℝ)] at hk'
    exact (div_le_iff₀ h0).mpr ((by exact_mod_cast ht : (t:ℝ)≤r).trans hk'.le)
  exact ⟨e j,(var_tri _ _ _).trans ((add_le_add (h w hw') ((var_pour _ f unif_law Q
    (g (e j))).trans he)).trans_eq (by ring))⟩

end HadwigerCounterexample

end

end OAI
