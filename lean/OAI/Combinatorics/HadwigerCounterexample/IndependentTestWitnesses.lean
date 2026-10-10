import OAI.Combinatorics.HadwigerCounterexample.AdditionalProbeBounds

namespace OAI

/-! # Independent Test Witnesses -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N r : ℕ} {T : Cov p N}

namespace Bazaar
variable (s : Bazaar p n r T)

set_option maxHeartbeats 800000 in
theorem shooting {w : Wgt (UnitType p n N)} (hw : IsLaw w)
    (S : Party) (j : Bool) (k d : ℕ) (hh : k ≤ d) (l : ℝ) (hl : 0 < l)
    (h : 5*l ≤ pr (pairW w w) (fun x => s.frequent w S j (s.ix x.1) (s.ix x.2) x.2))
    (hC : ∀ C : Cov p N,cdim p C≤d → pr w (fun x => offsetCov (s.ix x) ≤ C) ≤ l)
    (hb : ∀ A M Z,(↑(s.bids w S j A M Z).card:ℝ) ≤ bp (0.51*N)) :
    ∃ (q : Place p→ℕ) (R : DTuple (p:=p) q N)
      (F : Catalog p T r q), ctot p q=k ∧
      (∀ i, Injective (R i).mulVec) ∧
      (∀ M Z,(↑(F M Z).card:ℝ) ≤ bp (0.51*k*N)) ∧ l^(k+1)≤pr w (s.atList S j R F) := by
  classical
  let A := UnitType p n N
  let u (x y : A) := s.frequent w S j (s.ix x) (s.ix y) y
  let B (y : A) := 3*l≤pr w (fun x => u x y)
  suffices he : ∃ (q : Place p→ℕ) (R : DTuple (p:=p) q N)
      (F : Catalog p T r q), ctot p q=k ∧
      (∀ i, Injective (R i).mulVec) ∧ (∀ M Z,(↑(F M Z).card:ℝ) ≤ bp (0.51*k*N)) ∧
      l^(k+1)≤pr w (fun x => B x ∧ s.atList S j R F x) by
    obtain ⟨a,b,c,h1,h2,h3,h4⟩ := he
    exact ⟨a,b,c,h1,h2,h3,h4.trans (pr_mono hw.nz fun x h => h.2)⟩
  induction k with
  | zero =>
    let q := fun _ : Place p => 0
    let R : DTuple (p:=p) q N := 0
    let F : Catalog p T r q := fun _ _ => {R}
    have heq x : s.atList S j R F x := mem_singleton.mpr (Subsingleton.elim _ _)
    refine ⟨q,R,F,by simp [ctot,q],fun i x y h => Subsingleton.elim _ _,by simp [F],?_⟩
    simp only [heq,and_true,Nat.zero_add,pow_one]
    have hf : 5*l ≤ avg w (fun y => pr w (fun x => u x y)) := by
      change 5*l≤avg (pairW w w) _ at h
      rw [pairW_avg,avg_avg] at h
      exact h
    have hg (y) : pr w (fun x => u x y) ≤ 3*l+ind (B y) := by
      by_cases hh : B y
      · rw [ind_one hh]; exact ((pr_le_tot hw.nz).trans hw.total.le).trans (by linarith)
      rw [ind_zero hh,add_zero]; exact le_of_not_ge hh
    have ha := hf.trans (avg_mono hw.nz hg)
    rw [avg_add,hw.avg_const] at ha
    unfold pr; linarith only [hl,ha]
  | succ k ih =>
    obtain ⟨q,R,F,h1,h2,h3,h4⟩ := ih (Nat.le_of_succ_le hh)
    let P := fun x => B x ∧ s.atList S j R F x
    let C := Bazaar.probed p R
    let Z := fun x => offsetCov (s.ix x) ≤ C
    have hD : pr w Z ≤ l := by
      apply hC C
      refine le_trans ?_ (Nat.le_of_succ_le hh)
      rw [←h1]
      exact Finset.sum_le_sum fun i _ => (R i).rank_le_card_width.trans_eq (Fintype.card_fin _)
    obtain ⟨x,hx,hg⟩ :
        ∃ x,¬ Z x ∧ l^(k+2)≤ pr w (fun y => P y ∧ u x y) := by
      have he :
          avg w (fun x => ind (¬Z x)*pr w (fun y => P y ∧ u x y)) =
          avg w (fun y => ind (P y)*pr w (fun x => u x y ∧ ¬Z x)) := by
        unfold pr; simp_rw [← avg_mul',ind_and]
        rw [avg_avg]; apply congrArg
        funext y; apply congrArg; ext; ring
      let f := fun x => ind (¬Z x)*pr w (fun y => P y ∧ u x y)
      have hu (y : A) (hy : P y) : 2*l ≤ pr w (fun x => u x y ∧ ¬Z x) := by
        have hi (x : A) (h : u x y) : Z x ∨ (u x y ∧ ¬ Z x) :=
          or_iff_not_imp_left.mpr fun hx => ⟨h,hx⟩
        have hf := (show 3*l ≤ pr w _ from hy.1).trans
          ((pr_mono hw.nz hi).trans (pr_or_le hw.nz))
        linarith
      have hp := pow_pos hl (k+2)
      have hi : l^(k+2)<avg w f := by
        unfold f; rw [he]
        calc l^(k+2) < (2*l)*l^(k+1) := by rw [pow_succ l (k+1)] at *; linarith
             _ ≤ (2*l)*pr w P := mul_le_mul_of_nonneg_left h4 (by linarith)
             _ ≤ _ := by
               unfold pr
               rw [← avg_mul']
               refine avg_mono hw.nz (fun y => ?_)
               by_cases hv : P y
               · rw [ind_one hv,mul_one,one_mul]
                 exact hu y hv
               simp only [ind_zero hv,mul_zero,zero_mul,le_refl]
      obtain ⟨x,hx⟩ : ∃ x,l^(k+2)<f x := by
        by_contra! hn; exact not_lt_of_ge (hw.avg_le hn) hi
      by_cases hz : Z x
      · have hg : f x=0 := by simp [f,hz]
        exact (not_lt_of_ge hp.le (hg ▸ hx)).elim
      exact ⟨x,hz, (show f x=pr w (fun y => P y ∧ u x y) from (by simp [f,hz])) ▸ hx.le⟩
    obtain ⟨q',R',F',hQ,hR,hF,hH⟩ :=
      s.extend_probe w S j R h1 h2 F h3 (s.ix x) hx (hb _)
    refine ⟨q',R',F',hQ,hR, ?_,hg.trans (pr_mono hw.nz (fun y h => ⟨h.1.1,hH y h.1.2 h.2⟩))⟩
    simpa only [Nat.cast_add,Nat.cast_one] using hF

end Bazaar
end HadwigerCounterexample

end

end OAI
