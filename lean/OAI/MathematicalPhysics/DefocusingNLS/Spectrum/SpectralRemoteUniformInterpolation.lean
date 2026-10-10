import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExpansionDifferentiation

namespace OAI

/-! Uniform interpolation of arbitrary-order exterior expansions. A common
coarse growth bound upgrades the value remainder to every fixed derivative. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

theorem spectralRemote_uniform_expansion_derivatives
    (F : ℕ → ℝ → ℂ) (P : ℕ → ℕ → ℝ → ℂ) (L : ℝ)
    (hF : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (F n) (Ioi L))
    (hP : ∀ n j, ContDiff ℝ ∞ (P n j))
    (hgrowth : ∀ k : ℕ, ∃ C B T : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ᶠ n in atTop,
      ∀ t, T ≤ t → ‖iteratedDeriv k (F n) t‖ ≤ B*Real.exp (C*t))
    (hpoly : ∀ j k : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n in atTop,
      ∀ t, 0 ≤ t → ‖iteratedDeriv k (P n j) t‖ ≤ D)
    (happrox : ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ ∃ A T : ℝ, 0 ≤ A ∧ ∀ᶠ n in atTop,
      ∀ t, T ≤ t → ‖F n t-P n j t‖ ≤ A*Real.exp (-(2*(j : ℝ))*t)) :
    ∀ k : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ ∃ A T : ℝ, 0 ≤ A ∧
      ∀ᶠ n in atTop, ∀ t, T ≤ t →
        ‖iteratedDeriv k (fun s => F n s-P n j s) t‖ ≤ A*Real.exp (-R*t) := by
  intro k
  induction k with
  | zero =>
      intro R hR J
      obtain ⟨K,hK⟩ := exists_nat_gt R
      obtain ⟨j,hj,A,T,hA,hb⟩ := happrox (max J K)
      refine ⟨j,(le_max_left J K).trans hj,A,max T 0,hA,?_⟩
      filter_upwards [hb] with n hn
      intro t ht
      have ht0 : 0 ≤ t := (le_max_right T 0).trans ht
      have hjR : R ≤ 2*(j : ℝ) := by
        have hKj : (K : ℝ) ≤ j := by exact_mod_cast (le_max_right J K).trans hj
        nlinarith [Nat.cast_nonneg (α := ℝ) j]
      exact (hn t ((le_max_left T 0).trans ht)).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hA)
  | succ k ih =>
      intro R hR J
      obtain ⟨C,B,Tg,hC,hB,hgrow⟩ := hgrowth (k+2)
      obtain ⟨j,hj,A,Ta,hA,hap⟩ := ih (2*R+C) (by positivity) J
      obtain ⟨D,hD,hpb⟩ := hpoly j (k+2)
      let T := max (L+1) (max Ta (max Tg 0))
      have hTL : L < T := lt_of_lt_of_le (by linarith : L < L+1) (le_max_left _ _)
      have hTa : Ta ≤ T := (le_max_left Ta _).trans (le_max_right _ _)
      have hTg : Tg ≤ T := (le_max_left Tg 0).trans
        ((le_max_right Ta _).trans (le_max_right _ _))
      have hT0 : 0 ≤ T := (le_max_right Tg 0).trans
        ((le_max_right Ta _).trans (le_max_right _ _))
      refine ⟨j,hj,2*A+(B+D)*Real.exp C,T,by positivity,?_⟩
      filter_upwards [hF,hap,hgrow,hpb] with n hFn hapn hgn hpn
      let H := fun s => F n s-P n j s
      have hH : ContDiffOn ℝ ∞ H (Ioi L) := hFn.sub (hP n j).contDiffOn
      have hkH := radial_contDiffOn_iteratedDeriv H L hH k
      have hsmall : ∀ t, T ≤ t → ‖iteratedDeriv k H t‖ ≤ A*Real.exp (-(2*R+C)*t) :=
        fun t ht => hapn t (hTa.trans ht)
      have hsecond : ∀ t, T ≤ t →
          ‖deriv (deriv (iteratedDeriv k H)) t‖ ≤ (B+D)*Real.exp (C*t) := by
        intro t ht
        have hLt : L < t := hTL.trans_le ht
        have ht0 : 0 ≤ t := hT0.trans ht
        have hf : ContDiffAt ℝ (k+2) (F n) t :=
          ((hFn t hLt).contDiffAt (Ioi_mem_nhds hLt)).of_le (by simp)
        have hp : ContDiffAt ℝ (k+2) (P n j) t := (hP n j).contDiffAt.of_le (by simp)
        have hd : deriv (deriv (iteratedDeriv k H)) = iteratedDeriv (k+2) H := by
          rw [show k+2=(k+1)+1 by omega,iteratedDeriv_succ,iteratedDeriv_succ]
        rw [hd]
        change ‖iteratedDeriv (k+2) (F n-P n j) t‖ ≤ _
        rw [iteratedDeriv_sub hf hp]
        calc
          _ ≤ ‖iteratedDeriv (k+2) (F n) t‖+‖iteratedDeriv (k+2) (P n j) t‖ := norm_sub_le _ _
          _ ≤ B*Real.exp (C*t)+D := add_le_add (hgn t (hTg.trans ht)) (hpn t ht0)
          _ ≤ B*Real.exp (C*t)+D*Real.exp (C*t) :=
            add_le_add le_rfl (le_mul_of_one_le_right hD
              (Real.one_le_exp_iff.mpr (mul_nonneg hC ht0)))
          _ = _ := by ring
      intro t ht
      have hdf : ∀ s, T ≤ s → DifferentiableAt ℝ (iteratedDeriv k H) s := by
        intro s hs
        exact ((hkH s (hTL.trans_le hs)).contDiffAt (Ioi_mem_nhds (hTL.trans_le hs))).differentiableAt (by simp)
      have hddf : ∀ s, T ≤ s → DifferentiableAt ℝ (deriv (iteratedDeriv k H)) s := by
        intro s hs
        exact (((hkH.deriv_of_isOpen (m := ∞) isOpen_Ioi (by simp)) s (hTL.trans_le hs)).contDiffAt
          (Ioi_mem_nhds (hTL.trans_le hs))).differentiableAt (by simp)
      simpa only [iteratedDeriv_succ] using radial_derivative_exp_interpolation
        (iteratedDeriv k H) T A (B+D) C R t hA (add_nonneg hB hD) hC hR ht
        (hT0.trans ht) hdf hddf hsmall hsecond

end DefocusingNLS

end OAI
