import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CompactCoulombSmooth

namespace OAI

/-! Derivatives through order four of a compact source's Coulomb field.
The pole stays in the integrable kernel; all derivatives land on the source. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem compact_derivative_eval {q : Position → ℝ} (hc : HasCompactSupport q)
    (k : ℕ) (v : Fin k → Position) :
    HasCompactSupport (fun x => iteratedFDeriv ℝ k q x v) := by
  exact (hc.iteratedFDeriv (𝕜 := ℝ) k).comp_left
    (g := fun T : ContinuousMultilinearMap ℝ (fun _ : Fin k => Position) ℝ => T v)
    (by simp)

theorem compact_coulomb_iteratedFDeriv {q : Position → ℝ}
    (hq : ContDiff ℝ 4 q) (hc : HasCompactSupport q) :
    ∀ k : ℕ, k ≤ 4 → ∀ (v : Fin k → Position) (y : Position),
      iteratedFDeriv ℝ k (NeutralAtom.potentialOf q) y v =
        NeutralAtom.potentialOf (fun x => iteratedFDeriv ℝ k q x v) y := by
  intro k
  induction k with
  | zero =>
    intro _ v y
    simp only [iteratedFDeriv_zero_apply]
  | succ k ih =>
    intro hk v y
    have hk4 : k < (4 : WithTop ℕ∞) := by exact_mod_cast (by omega : k < 4)
    have hp := (compact_coulomb_C4 hq hc).differentiable_iteratedFDeriv hk4
    have hq' := hq.differentiable_iteratedFDeriv hk4
    have hr : ContDiff ℝ 1 (fun x => iteratedFDeriv ℝ k q x (Fin.tail v)) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Position) ℝ (Fin.tail v)).contDiff.comp
        (hq.iteratedFDeriv_right (by exact_mod_cast (show 1+k ≤ 4 by omega)))
    have hs : HasCompactSupport (fun x => iteratedFDeriv ℝ k q x (Fin.tail v)) :=
      compact_derivative_eval hc k (Fin.tail v)
    rw [(hp y).iteratedFDeriv_succ_apply_left']
    have hid : (fun z => iteratedFDeriv ℝ k (NeutralAtom.potentialOf q) z (Fin.tail v)) =
        NeutralAtom.potentialOf (fun x => iteratedFDeriv ℝ k q x (Fin.tail v)) :=
      funext (ih (by omega) (Fin.tail v))
    rw [hid]
    change NeutralAtom.dirPartial _ (v 0) y = _
    rw [compact_coulomb_partial hr hs]
    congr 1
    funext x
    exact ((hq' x).iteratedFDeriv_succ_apply_left').symm

theorem compact_coulomb_jet_bound {q : Position → ℝ}
    (hq : ContDiff ℝ 4 q) (hc : HasCompactSupport q)
    {k : ℕ} (hk : k ≤ 4) {M : ℝ}
    (hM : ∀ x, ‖iteratedFDeriv ℝ k q x‖ ≤ M) (y : Position) :
    ‖iteratedFDeriv ℝ k (NeutralAtom.potentialOf q) y‖ ≤
      2*Real.pi*M+∫ x, ‖iteratedFDeriv ℝ k q x‖ := by
  let D := fun x => ‖iteratedFDeriv ℝ k q x‖
  have hd : Continuous D := (hq.continuous_iteratedFDeriv (by exact_mod_cast hk)).norm
  have hcD : HasCompactSupport D := (hc.iteratedFDeriv (𝕜 := ℝ) k).norm
  have hbound := compact_coulomb_bound hd hcD (fun x => by
    simpa only [D,Real.norm_of_nonneg (norm_nonneg _)] using hM x) y
  have hpot : 0 ≤ NeutralAtom.potentialOf D y :=
    integral_nonneg (fun x => mul_nonneg (NeutralAtom.coulombKernel_nonneg _) (norm_nonneg _))
  simp only [Real.norm_of_nonneg hpot] at hbound
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  rw [compact_coulomb_iteratedFDeriv hq hc k hk]
  let P : ℝ := ∏ i, ‖v i‖
  have hP : 0 ≤ P := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  have hi : Integrable (fun x => NeutralAtom.coulombKernel (y-x)*D x) := by
    have hh := hcD.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      NeutralAtom.locallyIntegrable_coulombKernel hd y
    change Integrable (fun x => NeutralAtom.coulombKernel x*D (y-x)) at hh
    simpa only [sub_sub_cancel] using hh.comp_sub_left y
  have hb := norm_integral_le_of_norm_le (hi.mul_const P) (Filter.Eventually.of_forall
    (fun x => show ‖NeutralAtom.coulombKernel (y-x)*iteratedFDeriv ℝ k q x v‖ ≤
        (NeutralAtom.coulombKernel (y-x)*D x)*P from by
      rw [norm_mul,Real.norm_of_nonneg (NeutralAtom.coulombKernel_nonneg _),mul_assoc]
      exact mul_le_mul_of_nonneg_left ((iteratedFDeriv ℝ k q x).le_opNorm v)
        (NeutralAtom.coulombKernel_nonneg _)))
  change ‖∫ x, NeutralAtom.coulombKernel (y-x)*iteratedFDeriv ℝ k q x v‖ ≤ _
  apply hb.trans
  rw [integral_mul_const]
  apply mul_le_mul_of_nonneg_right _ hP
  simpa only [D,norm_norm,NeutralAtom.potentialOf] using hbound

end ContinuumCoulomb

end

end OAI
