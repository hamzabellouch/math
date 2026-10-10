import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedMultiwellResidual
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabOrbitalResidual
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.WellFieldOrbitalResidual

namespace OAI

/-! The residual for the actual manufactured one-body operator is the sum
of the checked off-site, finite-slab, and cutoff/counterterm residuals. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def manufacturedOrbitalResidual (rho H S freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) (x : Position) : ℝ :=
  localizedMultiwellResidual freq u j x+slabOrbitalResidual rho H S freq (u j) x+
    wellFieldOrbitalResidual freq scale S u j x

theorem manufacturedOrbitalResidual_eq {rho freq : ℝ} (hfreq : freq^2 = 4*Real.pi*rho)
    (H S scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (j : Fin m) (x : Position) :
    manufacturedOrbitalResidual rho H S freq scale u j x =
      -(1/2 : ℝ)*splitLaplacian (localizedMode freq (u j)) (positionSplitCoordinates x)+
      manufacturedSlabPotential rho H S freq scale u x*continuumLocalizedMode freq (u j) x-
      ((-1/2 : ℝ)+freq/2)*continuumLocalizedMode freq (u j) x := by
  rw [manufacturedOrbitalResidual, localizedMultiwellResidual_eq]
  unfold multiwellAction multiwellPotential slabOrbitalResidual slabResidualMultiplier
    wellFieldOrbitalResidual manufacturedSlabPotential planarWellSum
  rw [hfreq]
  simp only [continuumLocalizedMode, positionSplitCoordinates_snd]
  ring

private theorem slab_residual_continuous {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (freq : ℝ) (u : PlanarPosition) :
    Continuous (slabOrbitalResidual rho H S freq u) :=
  (((slabPotential_continuous hrho hH hS).sub continuous_const).sub
    (continuous_const.mul (positionSplitCoordinates.continuous.snd.pow 2))).mul
    (continuumLocalizedMode_C7 freq u).continuous

private theorem well_residual_continuous (freq scale S : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) :
    Continuous (wellFieldOrbitalResidual freq scale S u j) :=
  ((manufacturedWellField_C7 freq scale S u).continuous.sub
    ((planarWellSum_continuous u).comp positionSplitCoordinates.continuous.fst)).mul
    (continuumLocalizedMode_C7 freq (u j)).continuous

theorem manufacturedOrbitalResidual_memLp {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (j : Fin m) :
    MemLp (manufacturedOrbitalResidual rho H S freq scale u j) 2 := by
  have hs : MemLp (slabOrbitalResidual rho H S freq (u j)) 2 :=
    (memLp_two_iff_integrable_sq (slab_residual_continuous hrho hH hS freq (u j)).aestronglyMeasurable).mpr
      (slabOrbitalResidual_square_integrable hrho hH hS hfreq (u j))
  have hw : MemLp (wellFieldOrbitalResidual freq scale S u j) 2 :=
    (memLp_two_iff_integrable_sq (well_residual_continuous freq scale S u j).aestronglyMeasurable).mpr
      (wellFieldOrbitalResidual_square_integrable hfreq scale S u hδ hcoeff j)
  exact ((localizedMultiwellResidual_memLp hfreq u j).add hs).add hw

theorem manufacturedOrbitalResidual_square_integrable {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (j : Fin m) :
    Integrable (fun x => manufacturedOrbitalResidual rho H S freq scale u j x^2) :=
  (manufacturedOrbitalResidual_memLp hrho hH hS hfreq scale u hδ hcoeff j).integrable_sq

/-- The seventy-second-moment tail keeps the residual compatible with the
physical mesh scale even for high-aspect slabs. -/
def manufacturedOrbitalSquaredError (rho H S freq δ D R : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) : ℝ :=
  3*((m : ℝ)^2*(PlanarSobolev.wellBound*planarWellMatrixConstant)*Real.exp (-(19/10 : ℝ)*D)+
    (2*(6*Real.pi*rho*S^3/H)^2+2*(64*rho*S/H)^2*localizedDensityMoment freq (u j) 4+
      2*(2*slabUniformBound rho H S)^2*(localizedDensityMoment freq (u j) 72/R^72)+
      2*(2*Real.pi*rho)^2*(localizedDensityMoment freq (u j) 72/R^68))+
    (((m : ℝ)*δ*PlanarSobolev.wellBound)^2+
      ((m : ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*
        (localizedDensityMoment freq (u j) 8/(S/2)^8)))

theorem manufacturedOrbitalResidual_square_bound {rho H S freq δ D R : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (j : Fin m) :
    (∫ x, manufacturedOrbitalResidual rho H S freq scale u j x^2) ≤
      manufacturedOrbitalSquaredError rho H S freq δ D R u j := by
  have hpoint (x : Position) : manufacturedOrbitalResidual rho H S freq scale u j x^2 ≤
      3*(localizedMultiwellResidual freq u j x^2+slabOrbitalResidual rho H S freq (u j) x^2+
        wellFieldOrbitalResidual freq scale S u j x^2) := by
    unfold manufacturedOrbitalResidual
    nlinarith [sq_nonneg (localizedMultiwellResidual freq u j x-slabOrbitalResidual rho H S freq (u j) x),
      sq_nonneg (localizedMultiwellResidual freq u j x-wellFieldOrbitalResidual freq scale S u j x),
      sq_nonneg (slabOrbitalResidual rho H S freq (u j) x-wellFieldOrbitalResidual freq scale S u j x)]
  have hm := localizedMultiwellResidual_square_integrable hfreq u j
  have hs := slabOrbitalResidual_square_integrable hrho hH.le hS.le hfreq (u j)
  have hw := wellFieldOrbitalResidual_square_integrable hfreq scale S u hδ hcoeff j
  have h := integral_mono
    (manufacturedOrbitalResidual_square_integrable hrho hH.le hS.le hfreq scale u hδ hcoeff j)
    (((hm.add hs).add hw).const_mul 3) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_const_mul] at h
  have hsum := integral_add (hm.add hs) hw
  have hpair := integral_add hm hs
  simp only [Pi.add_apply] at hsum hpair
  rw [hsum, hpair] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (localizedMultiwellResidual_square_bound hfreq u hsep j)
      (slabOrbitalResidual_square_bound_seventySecond hrho hH hS.le hfreq hR hRH hRS (u j)))
      (wellFieldOrbitalResidual_square_bound hfreq hS scale u hδ hcoeff j)) (by norm_num))

end ContinuumCoulomb

end

end OAI
