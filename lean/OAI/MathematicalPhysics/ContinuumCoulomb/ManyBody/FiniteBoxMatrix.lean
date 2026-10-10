import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteWellResidual
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedOrbitalResidual
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.WeightedSourcePairing

namespace OAI

/-! Finite-box correction to the intended one-body matrix. The well-depth
counterterm remains part of the target matrix; only its vertical truncation
and the finite slab approximation contribute to this error. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def finiteBoxOrbitalResidual (rho H S freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) (x : Position) : ℝ :=
  slabOrbitalResidual rho H S freq (u j) x+finiteWellOrbitalResidual freq scale S u j x

def finiteBoxOrbitalSquaredError (rho H S freq δ r : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) : ℝ :=
  2*((2*(6*Real.pi*rho*S^3/H)^2+2*(64*rho*S/H)^2*localizedDensityMoment freq (u j) 4+
      2*(2*slabUniformBound rho H S)^2*(localizedDensityMoment freq (u j) 72/r^72)+
      2*(2*Real.pi*rho)^2*(localizedDensityMoment freq (u j) 72/r^68))+
    ((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2/(S/2)^24*
      (∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2))

private theorem slabOrbitalResidual_continuous {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (freq : ℝ) (u : PlanarPosition) :
    Continuous (slabOrbitalResidual rho H S freq u) :=
  (((slabPotential_continuous hrho hH hS).sub continuous_const).sub
    (continuous_const.mul (positionSplitCoordinates.continuous.snd.pow 2))).mul
    (continuumLocalizedMode_C7 freq u).continuous

theorem finiteBoxOrbitalResidual_continuous {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) :
    Continuous (finiteBoxOrbitalResidual rho H S freq scale u j) :=
  (slabOrbitalResidual_continuous hrho hH hS freq (u j)).add
    (finiteWellOrbitalResidual_continuous freq scale S u j)

theorem finiteBoxOrbitalResidual_memLp {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 < S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ)
    (j : Fin m) : MemLp (finiteBoxOrbitalResidual rho H S freq scale u j) 2 := by
  have hs := (memLp_two_iff_integrable_sq
    (slabOrbitalResidual_continuous hrho hH hS.le freq (u j)).aestronglyMeasurable).mpr
    (slabOrbitalResidual_square_integrable hrho hH hS.le hfreq (u j))
  have hw := (memLp_two_iff_integrable_sq
    (finiteWellOrbitalResidual_continuous freq scale S u j).aestronglyMeasurable).mpr
    (finiteWellOrbitalResidual_square_bound hfreq hS scale u hδ hcoeff j).1
  exact hs.add hw

theorem finiteBoxOrbitalResidual_square_bound {rho H S freq r : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (hr : 0 < r) (hrH : r ≤ H/2) (hrS : r ≤ S)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ)
    (j : Fin m) :
    (∫ x, finiteBoxOrbitalResidual rho H S freq scale u j x^2) ≤
      finiteBoxOrbitalSquaredError rho H S freq δ r u j := by
  have hs := slabOrbitalResidual_square_integrable hrho hH.le hS.le hfreq (u j)
  obtain ⟨hw,hwb⟩ := finiteWellOrbitalResidual_square_bound hfreq hS scale u hδ hcoeff j
  have h := integral_mono (finiteBoxOrbitalResidual_memLp hrho hH.le hS hfreq scale u hδ hcoeff j).integrable_sq
    ((hs.add hw).const_mul 2) (fun x => show
      finiteBoxOrbitalResidual rho H S freq scale u j x^2 ≤
        2*(slabOrbitalResidual rho H S freq (u j) x^2+finiteWellOrbitalResidual freq scale S u j x^2) from by
      dsimp [finiteBoxOrbitalResidual]
      nlinarith [sq_nonneg (slabOrbitalResidual rho H S freq (u j) x-finiteWellOrbitalResidual freq scale S u j x)])
  rw [integral_const_mul] at h
  simp only [Pi.add_apply] at h
  rw [integral_add hs hw] at h
  have hsb := slabOrbitalResidual_square_bound_seventySecond hrho hH hS.le hfreq hr hrH hrS (u j)
  unfold finiteBoxOrbitalSquaredError
  linarith

def manufacturedRawOneBodyMatrix (rho H S freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i j : Fin m) : ℝ :=
  ∫ x, continuumLocalizedMode freq (u i) x*manufacturedOrbitalResidual rho H S freq scale u j x

theorem manufacturedRawOneBodyMatrix_integrand (rho H S freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i j : Fin m) (x : Position) :
    continuumLocalizedMode freq (u i) x*manufacturedOrbitalResidual rho H S freq scale u j x =
      localizedCorrectedOneBodyIntegrand freq scale u i j x+
        continuumLocalizedMode freq (u i) x*finiteBoxOrbitalResidual rho H S freq scale u j x := by
  have hc : countertermWellSum freq scale u (positionSplitCoordinates x).1-
      planarWellSum u (positionSplitCoordinates x).1 =
      scale⁻¹*∑ k, localizedCounterterm freq u k*manufacturedPlanarWell ((positionSplitCoordinates x).1-u k) := by
    rw [countertermWellSum_sub_eq,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [div_eq_mul_inv]
    ring
  rw [manufacturedOrbitalResidual,localizedMultiwellResidual_eq]
  unfold localizedCorrectedOneBodyIntegrand correctedMultiwellAction finiteBoxOrbitalResidual
    finiteWellOrbitalResidual wellFieldOrbitalResidual
  change _ = continuumLocalizedMode freq (u i) x*
    (multiwellAction freq u (localizedMode freq (u j)) (positionSplitCoordinates x)+
      scale⁻¹*(∑ k, localizedCounterterm freq u k*manufacturedPlanarWell ((positionSplitCoordinates x).1-u k))*
        continuumLocalizedMode freq (u j) x-((-1/2:ℝ)+freq/2)*continuumLocalizedMode freq (u j) x)+_
  linear_combination continuumLocalizedMode freq (u i) x*continuumLocalizedMode freq (u j) x*hc

theorem manufacturedRawOneBodyMatrix_error_integral {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 < S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ)
    (i j : Fin m) :
    |manufacturedRawOneBodyMatrix rho H S freq scale u i j-
      localizedCorrectedOneBodyMatrix freq scale u i j|^2 ≤
        (∫ x, finiteBoxOrbitalResidual rho H S freq scale u j x^2) := by
  have hm := continuumLocalizedMode_memLp hfreq (u i)
  have hf := finiteBoxOrbitalResidual_memLp hrho hH hS hfreq scale u hδ hcoeff j
  have hi : Integrable (fun x => continuumLocalizedMode freq (u i) x*
      finiteBoxOrbitalResidual rho H S freq scale u j x) := hm.integrable_mul hf
  have he : manufacturedRawOneBodyMatrix rho H S freq scale u i j-
      localizedCorrectedOneBodyMatrix freq scale u i j =
      ∫ x, continuumLocalizedMode freq (u i) x*finiteBoxOrbitalResidual rho H S freq scale u j x := by
    unfold manufacturedRawOneBodyMatrix
    simp_rw [manufacturedRawOneBodyMatrix_integrand]
    rw [integral_add (localizedCorrectedOneBodyIntegrand_integrable hfreq scale u i j) hi]
    change localizedCorrectedOneBodyMatrix freq scale u i j+_ -
      localizedCorrectedOneBodyMatrix freq scale u i j = _
    ring
  have hmass : (∫ x, continuumLocalizedMode freq (u i) x^2) = 1 := localizedDensity_mass hfreq (u i)
  have hpair := (weighted_source_pairing (fun _ => 1) _ _ measurable_const
    (continuumLocalizedMode_C7 freq (u i)).continuous.measurable
    (finiteBoxOrbitalResidual_continuous hrho hH hS.le freq scale u j).measurable
    (by simpa only [abs_one,one_mul] using hm.integrable_sq)
    (by simpa only [abs_one,one_mul] using hf.integrable_sq)).2
  simp only [abs_one,one_mul,hmass] at hpair
  rw [he]
  exact hpair


theorem manufacturedRawOneBodyMatrix_error {rho H S freq r : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (hr : 0 < r) (hrH : r ≤ H/2) (hrS : r ≤ S)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ)
    (i j : Fin m) :
    |manufacturedRawOneBodyMatrix rho H S freq scale u i j-
      localizedCorrectedOneBodyMatrix freq scale u i j|^2 ≤
        finiteBoxOrbitalSquaredError rho H S freq δ r u j := by
  exact (manufacturedRawOneBodyMatrix_error_integral hrho hH.le hS hfreq scale u hδ hcoeff i j).trans
    (finiteBoxOrbitalResidual_square_bound hrho hH hS hfreq hr hrH hrS scale u hδ hcoeff j)

end ContinuumCoulomb

end

end OAI
