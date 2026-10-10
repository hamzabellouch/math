import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CorrectedOneElectronProjection
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CorrectedResidualPairing

namespace OAI

/-! Derivative coordinates of an actual corrected-orbital H1 state. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def correctedPartialLp {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) (a : Fin 1 × Fin 3) :
    Lp ℂ 2 (volume : Measure (Configuration 1)) :=
  (oneElectronCorrectedMode_partial_memLp hfreq u i a).ofReal.toLp
    (fun x => (configurationRealPartial (oneElectronCorrectedMode freq u i) a x : ℂ))

theorem oneElectronCorrectedMode_partial_physical (freq : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) (b : Fin 3) (x : Configuration 1) :
    configurationRealPartial (oneElectronCorrectedMode freq u i) (0,b) x =
      fderiv ℝ (correctedLocalizedMode freq u i) (oneElectronCoordinates x)
        (EuclideanSpace.single b 1) := by
  change fderiv ℝ (fun y : Configuration 1 => correctedLocalizedMode freq u i (oneElectronCoordinates y)) x
    (EuclideanSpace.single (0,b) 1) = _
  have h := ((correctedLocalizedMode_C1 freq u i).differentiable (by norm_num)
    (oneElectronCoordinates x)).hasFDerivAt.comp x
      oneElectronCoordinates.toContinuousLinearEquiv.hasFDerivAt
  simpa only [Function.comp_def,
    ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe,oneElectronCoordinates_single] using
      congrArg (fun L : Configuration 1 →L[ℝ] ℝ => L (EuclideanSpace.single (0,b) 1)) h.fderiv

theorem correctedOneElectronState_gradient {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (c : SpinConfiguration 1 → Fin m → ℂ)
    (s : SpinConfiguration 1) (a : Fin 1 × Fin 3) (x : Configuration 1) :
    (correctedOneElectronState hfreq u c).gradient s a x =
      ∑ i, c s i*(configurationRealPartial (oneElectronCorrectedMode freq u i) a x : ℂ) := by
  obtain ⟨a,b⟩ := a
  have ha : a = 0 := Subsingleton.elim _ _
  subst a
  change fderiv ℝ (correctedOneElectronValue freq u c s) x (EuclideanSpace.single (0,b) 1) = _
  rw [correctedOneElectronValue_partial]
  simp only [oneElectronCorrectedMode_partial_physical]

theorem correctedOneElectronState_gradient_coordinate {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (c : SpinConfiguration 1 → Fin m → ℂ)
    (s : SpinConfiguration 1) (a : Fin 1 × Fin 3) :
    h1Coordinates (correctedOneElectronState hfreq u c) (Sum.inr (s,a)) =
      ∑ i, c s i • correctedPartialLp hfreq u i a := by
  have he (i : Fin m) : (c s i • correctedPartialLp hfreq u i a :
      Lp ℂ 2 (volume : Measure (Configuration 1))) =ᵐ[volume]
      (fun x => c s i*(configurationRealPartial (oneElectronCorrectedMode freq u i) a x : ℂ)) := by
    have hm : MemLp (fun x => (configurationRealPartial (oneElectronCorrectedMode freq u i) a x : ℂ)) 2 :=
      (oneElectronCorrectedMode_partial_memLp hfreq u i a).ofReal
    filter_upwards [Lp.coeFn_smul (c s i) (correctedPartialLp hfreq u i a),hm.coeFn_toLp] with x hs hx
    rw [hs]
    change c s i*(correctedPartialLp hfreq u i a x) = _
    change correctedPartialLp hfreq u i a x = _ at hx
    rw [hx]
  have hall := Filter.eventually_all.2 he
  apply Lp.ext
  filter_upwards [(h1Coordinate_memLp (correctedOneElectronState hfreq u c) (Sum.inr (s,a))).coeFn_toLp,
    Lp.coeFn_fun_finsetSum Finset.univ (fun i => c s i • correctedPartialLp hfreq u i a),hall]
      with x hx hs hh
  change h1Coordinates (correctedOneElectronState hfreq u c) (Sum.inr (s,a)) x = _ at hx
  rw [hs,hx]
  change (correctedOneElectronState hfreq u c).gradient s a x = _
  rw [correctedOneElectronState_gradient]
  exact Finset.sum_congr rfl (fun i _ => (hh i).symm)

end ContinuumCoulomb

end

end OAI
