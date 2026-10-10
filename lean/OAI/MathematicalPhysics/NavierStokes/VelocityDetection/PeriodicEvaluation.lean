import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicMild
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicSpaceOfPeriodicCurve

namespace OAI

noncomputable section
namespace VelocityDetection.PeriodicSpace.Jets
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ZeroAtInfty BigOperators
open PeriodicMild

theorem continuous_uncurry_value {a : ℕ} {J : ℝ → compatibleJets 2 a}
    (hJ : Continuous J) : Continuous (fun p : ℝ × Coord 2 => value (J p.1) p.2) := by
  let L : compatibleJets 2 a →L[ℝ] PeriodicSpace.compatible 2 :=
    LinearMap.mkContinuous
      { toFun := fun J : compatibleJets 2 a => entry J 0 (Nat.zero_le a) Fin.elim0
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
      1 (fun J => by
        change ‖entry J 0 (Nat.zero_le a) Fin.elim0‖ ≤ 1 * ‖J‖
        rw [one_mul]; exact norm_entry_le _ _ _ _)
  have hb : Continuous (fun t : ℝ => PeriodicSpace.realLift (L (J t))) :=
    PeriodicSpace.realLiftLI.continuous.comp (L.continuous.comp hJ)
  exact (hb.comp continuous_fst).eval continuous_snd

theorem hasDerivAt_value_curve {a : ℕ} {J : ℝ → compatibleJets 2 a}
    {J' : compatibleJets 2 a} {t : ℝ} (hJ : HasDerivAt J J' t) (X : Coord 2) :
    HasDerivAt (fun r => value (J r) X) (value J' X) t := by
  have he : HasFDerivAt (evaluate X : compatibleJets 2 a →L[ℝ] ℝ)
      (evaluate X) (J t) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := compatibleJets 2 a) (F := ℝ) (evaluate X)
  exact HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := compatibleJets 2 a) (E := ℝ)
    (l := evaluate X) (l' := evaluate X) t he hJ

theorem contDiff_uncurry_value (a : ℕ) {J : ℝ → compatibleJets 2 a}
    (hJ : ContDiff ℝ a J) : ContDiff ℝ a (fun p : ℝ × Coord 2 => value (J p.1) p.2) := by
  induction a with
  | zero => exact contDiff_zero.mpr (continuous_uncurry_value hJ.continuous)
  | succ a ih =>
    have hdc : ContDiff ℝ a (deriv J) := hJ.deriv'
    have hvT : ContDiff ℝ a (fun p : ℝ × Coord 2 => value (deriv J p.1) p.2) := by
      have hl : ContDiff ℝ a (fun t : ℝ => restrict (Nat.le_succ a) (deriv J t)) :=
        (restrictL (n := 2) (Nat.le_succ a)).contDiff.comp hdc
      simpa only [restrict_value] using ih hl
    have hJ' : ContDiff ℝ a J := hJ.of_le (by exact_mod_cast Nat.le_succ a)
    have hvX (i : Fin 2) :
        ContDiff ℝ a (fun p : ℝ × Coord 2 => value (differentiate i (J p.1)) p.2) :=
      ih ((differentiateL (n := 2) (a := a) i).contDiff.comp hJ')
    let dT : ℝ → Coord 2 → ℝ →L[ℝ] ℝ := fun t X =>
      (1 : ℝ →L[ℝ] ℝ).smulRight (value (deriv J t) X)
    let dX : ℝ → Coord 2 → Coord 2 →L[ℝ] ℝ := fun t X =>
      firstGradient (fun i => differentiate i (J t)) X
    have hT : ContDiff ℝ a (uncurry dT) :=
      (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).contDiff.comp hvT
    have hX : ContDiff ℝ a (uncurry dX) := by
      change ContDiff ℝ a (fun p : ℝ × Coord 2 =>
        ∑ i : Fin 2, value (differentiate i (J p.1)) p.2 •
          (ContinuousLinearMap.proj i : Coord 2 →L[ℝ] ℝ))
      apply ContDiff.sum
      intro i _
      exact (hvX i).smul contDiff_const
    have hD : ContDiff ℝ a (fun p : ℝ × Coord 2 => (dT p.1 p.2).coprod (dX p.1 p.2)) := by
      apply contDiff_clm_apply_iff.mpr
      intro v
      change ContDiff ℝ a (fun p : ℝ × Coord 2 => dT p.1 p.2 v.1 + dX p.1 p.2 v.2)
      exact (hT.clm_apply contDiff_const).add (hX.clm_apply contDiff_const)
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun p : ℝ × Coord 2 => (dT p.1 p.2).coprod (dX p.1 p.2), hD, ?_⟩
    intro p
    apply HasStrictFDerivAt.hasFDerivAt
    apply hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (E₁ := ℝ) (E₂ := Coord 2)
      (F := ℝ) (f := fun t X => value (J t) X) (f₁ := dT) (f₂ := dX)
    · apply Eventually.of_forall
      intro r
      exact (hasDerivAt_value_curve ((hJ.differentiable (by simp) r.1).hasDerivAt) r.2).hasFDerivAt
    · apply Eventually.of_forall
      intro r
      exact hasFDerivAt_value (J r.1) r.2
    · exact hT.continuous.continuousAt
    · exact hX.continuous.continuousAt

end VelocityDetection.PeriodicSpace.Jets
end

end OAI
