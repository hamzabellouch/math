import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedMomentTail
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabInterior
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabRegularity

namespace OAI

/-! The finite slab's actual harmonic-oscillator residual on a localized
orbital. Interior accuracy and weighted tails are kept separately. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def slabResidualMultiplier (rho H S : ℝ) (x : Position) : ℝ :=
  slabPotential rho H S x-slabPotential rho H S 0-2*Real.pi*rho*(x 2)^2

def slabUniformBound (rho H S : ℝ) : ℝ :=
  rho*NeutralAtom.kernelBallMass 1+volume.real (slabDomain H S)*rho

def slabOrbitalResidual (rho H S freq : ℝ) (u : PlanarPosition) (x : Position) : ℝ :=
  slabResidualMultiplier rho H S x*continuumLocalizedMode freq u x

theorem slabResidualMultiplier_abs_bound {rho H S : ℝ} (hrho : 0 ≤ rho)
    (hH : 0 ≤ H) (hS : 0 ≤ S) (x : Position) :
    |slabResidualMultiplier rho H S x| ≤
      2*slabUniformBound rho H S+(2*Real.pi*rho)*‖x‖^2 := by
  have hx := slabPotential_abs_bound hrho hH hS x
  have h0 := slabPotential_abs_bound hrho hH hS 0
  have hn : (x 2)^2 ≤ ‖x‖^2 := by
    have h := PiLp.norm_apply_le x 2
    rw [Real.norm_eq_abs] at h
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr h
  have hc : 0 ≤ 2*Real.pi*rho := by positivity
  unfold slabResidualMultiplier
  calc
    _ ≤ |slabPotential rho H S x-slabPotential rho H S 0|+
        |2*Real.pi*rho*(x 2)^2| := abs_sub _ _
    _ ≤ 2*slabUniformBound rho H S+(2*Real.pi*rho)*(x 2)^2 := by
      rw [abs_of_nonneg (mul_nonneg hc (sq_nonneg _))]
      have h := (abs_sub (slabPotential rho H S x) (slabPotential rho H S 0)).trans
        (add_le_add hx h0)
      dsimp [slabUniformBound]
      linarith
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hn hc)

private theorem square_times_density_bound {f : ℝ} {A B t d : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 ≤ t) (hd : 0 ≤ d)
    (hf : |f| ≤ A+B*t) : f^2*d ≤ 2*A^2*d+2*B^2*t^2*d := by
  have hs := (sq_le_sq₀ (abs_nonneg f) (by positivity : 0 ≤ A+B*t)).mpr hf
  rw [sq_abs] at hs
  have hq : f^2 ≤ 2*A^2+2*B^2*t^2 := by nlinarith [sq_nonneg (A-B*t)]
  nlinarith [mul_le_mul_of_nonneg_right hq hd]

theorem slabOrbitalResidual_square_integrable {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (u : PlanarPosition) : Integrable (fun x => slabOrbitalResidual rho H S freq u x^2) := by
  let A := 2*slabUniformBound rho H S
  let B := 2*Real.pi*rho
  have hA : 0 ≤ A := by
    have h := slabPotential_abs_bound hrho hH hS (0 : Position)
    have := abs_nonneg (slabPotential rho H S 0)
    dsimp [A, slabUniformBound]
    linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmajor : Integrable (fun x : Position =>
      2*A^2*localizedDensity freq u x+2*B^2*(‖x‖^4*localizedDensity freq u x)) :=
    ((localizedDensity_integrable hfreq u).const_mul _).add
      ((localizedDensity_fourth_moment_translate hfreq u).1.const_mul _)
  apply hmajor.mono'
    ((((slabPotential_continuous hrho hH hS).sub continuous_const).sub
      (continuous_const.mul (positionSplitCoordinates.continuous.snd.pow 2))).mul
      (continuumLocalizedMode_C7 freq u).continuous |>.pow 2).aestronglyMeasurable
  filter_upwards [] with x
  change ‖slabOrbitalResidual rho H S freq u x^2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h := square_times_density_bound hA hB (sq_nonneg ‖x‖)
    (localizedDensity_nonnegative freq u x) (slabResidualMultiplier_abs_bound hrho hH hS x)
  convert h using 1 <;> dsimp [slabOrbitalResidual, localizedDensity, A, B] <;> ring

theorem slabOrbitalResidual_square_bound {rho H S freq R : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S) (u : PlanarPosition) :
    (∫ x, slabOrbitalResidual rho H S freq u x^2) ≤
      2*(6*Real.pi*rho*S^3/H)^2+
      2*(64*rho*S/H)^2*localizedDensityMoment freq u 4+
      2*(2*slabUniformBound rho H S)^2*(localizedDensityMoment freq u 24/R^24)+
      2*(2*Real.pi*rho)^2*(localizedDensityMoment freq u 24/R^20) := by
  let K := Metric.closedBall (0 : Position) R
  let a := 6*Real.pi*rho*S^3/H
  let b := 64*rho*S/H
  let A := 2*slabUniformBound rho H S
  let B := 2*Real.pi*rho
  have hK : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hA : 0 ≤ A := by
    have h := slabPotential_abs_bound hrho hH.le hS (0 : Position)
    have := abs_nonneg (slabPotential rho H S 0)
    dsimp [A, slabUniformBound]
    linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hi := slabOrbitalResidual_square_integrable hrho hH.le hS hfreq u
  have hd := localizedDensity_integrable hfreq u
  have h4 := (localizedDensity_fourth_moment_translate hfreq u).1
  have hout (x : Position) (hx : x ∉ K) : R ≤ ‖x‖ := by
    exact (lt_of_not_ge (by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx)).le
  have hinner (x : Position) (hx : x ∈ K) : |slabResidualMultiplier rho H S x| ≤ a+b*‖x‖^2 := by
    have hnorm : ‖x‖ ≤ R := by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx
    have hcoord (i : Fin 3) : |x i| ≤ R := by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le x i).trans hnorm
    have hxy : (x 0)^2+(x 1)^2 ≤ ‖x‖^2 := by
      have he := positionSplitCoordinates_norm_sq x
      have hp : ‖(positionSplitCoordinates x).1‖^2 = (x 0)^2+(x 1)^2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp only [Fin.sum_univ_two, positionSplitCoordinates_fst_zero, positionSplitCoordinates_fst_one, Real.norm_eq_abs, sq_abs]
      rw [hp] at he
      nlinarith [sq_nonneg (x 2)]
    have h := slabPotential_interior_error hrho hH hS x
      ((hcoord 0).trans hRH) ((hcoord 1).trans hRH) ((hcoord 2).trans hRS)
    change |slabResidualMultiplier rho H S x| ≤ _ at h
    calc
      _ ≤ 64*rho*S*((x 0)^2+(x 1)^2)/H+6*Real.pi*rho*S^3/H := h
      _ = a+b*((x 0)^2+(x 1)^2) := by dsimp [a,b]; ring
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hxy hb)
  have hinnerSq (x : Position) (hx : x ∈ K) : slabOrbitalResidual rho H S freq u x^2 ≤
      2*a^2*localizedDensity freq u x+2*b^2*(‖x‖^4*localizedDensity freq u x) := by
    have h := square_times_density_bound ha hb (sq_nonneg ‖x‖)
      (localizedDensity_nonnegative freq u x) (hinner x hx)
    convert h using 1 <;> dsimp [slabOrbitalResidual, localizedDensity] <;> ring
  have houterSq (x : Position) : slabOrbitalResidual rho H S freq u x^2 ≤
      2*A^2*localizedDensity freq u x+2*B^2*(‖x‖^4*localizedDensity freq u x) := by
    have h := square_times_density_bound hA hB (sq_nonneg ‖x‖)
      (localizedDensity_nonnegative freq u x) (slabResidualMultiplier_abs_bound hrho hH.le hS x)
    convert h using 1 <;> dsimp [slabOrbitalResidual, localizedDensity, A, B] <;> ring
  have hinside := setIntegral_mono_on hi.integrableOn
    ((hd.const_mul (2*a^2)).add (h4.const_mul (2*b^2))).integrableOn hK hinnerSq
  have houtside := setIntegral_mono_on hi.integrableOn
    ((hd.const_mul (2*A^2)).add (h4.const_mul (2*B^2))).integrableOn hK.compl
    (fun x _ => houterSq x)
  simp only [Pi.add_apply] at hinside houtside
  rw [integral_add (hd.const_mul (2*a^2)).integrableOn (h4.const_mul (2*b^2)).integrableOn,
    integral_const_mul, integral_const_mul] at hinside
  rw [integral_add (hd.const_mul (2*A^2)).integrableOn (h4.const_mul (2*B^2)).integrableOn,
    integral_const_mul, integral_const_mul] at houtside
  have hmass : (∫ x in K, localizedDensity freq u x) ≤ 1 := by
    rw [← localizedDensity_mass hfreq u]
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (localizedDensity_nonnegative freq u)) hd
  have hmoment : (∫ x in K, ‖x‖^4*localizedDensity freq u x) ≤ localizedDensityMoment freq u 4 :=
    integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun x => mul_nonneg (pow_nonneg (norm_nonneg x) 4)
        (localizedDensity_nonnegative freq u x))) h4
  have ht0 := localizedDensity_mass_tail_twentyFourth hfreq hR u hK hout
  have ht4 := localizedDensity_fourth_tail_twentyFourth hfreq hR u hK hout
  have hsum := add_le_add (hinside.trans (add_le_add
    (mul_le_mul_of_nonneg_left hmass (by positivity))
    (mul_le_mul_of_nonneg_left hmoment (by positivity))))
    (houtside.trans (add_le_add (mul_le_mul_of_nonneg_left ht0 (by positivity))
      (mul_le_mul_of_nonneg_left ht4 (by positivity))))
  rw [integral_add_compl hK hi] at hsum
  simpa only [mul_one, a, b, A, B, add_assoc] using hsum

theorem slabOrbitalResidual_square_bound_seventySecond {rho H S freq R : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S) (u : PlanarPosition) :
    (∫ x, slabOrbitalResidual rho H S freq u x^2) ≤
      2*(6*Real.pi*rho*S^3/H)^2+
      2*(64*rho*S/H)^2*localizedDensityMoment freq u 4+
      2*(2*slabUniformBound rho H S)^2*(localizedDensityMoment freq u 72/R^72)+
      2*(2*Real.pi*rho)^2*(localizedDensityMoment freq u 72/R^68) := by
  let K := Metric.closedBall (0 : Position) R
  let a := 6*Real.pi*rho*S^3/H
  let b := 64*rho*S/H
  let A := 2*slabUniformBound rho H S
  let B := 2*Real.pi*rho
  have hK : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hA : 0 ≤ A := by
    have h := slabPotential_abs_bound hrho hH.le hS (0 : Position)
    have := abs_nonneg (slabPotential rho H S 0)
    dsimp [A, slabUniformBound]
    linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hi := slabOrbitalResidual_square_integrable hrho hH.le hS hfreq u
  have hd := localizedDensity_integrable hfreq u
  have h4 := (localizedDensity_fourth_moment_translate hfreq u).1
  have hout (x : Position) (hx : x ∉ K) : R ≤ ‖x‖ := by
    exact (lt_of_not_ge (by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx)).le
  have hinner (x : Position) (hx : x ∈ K) : |slabResidualMultiplier rho H S x| ≤ a+b*‖x‖^2 := by
    have hnorm : ‖x‖ ≤ R := by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx
    have hcoord (i : Fin 3) : |x i| ≤ R := by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le x i).trans hnorm
    have hxy : (x 0)^2+(x 1)^2 ≤ ‖x‖^2 := by
      have he := positionSplitCoordinates_norm_sq x
      have hp : ‖(positionSplitCoordinates x).1‖^2 = (x 0)^2+(x 1)^2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp only [Fin.sum_univ_two, positionSplitCoordinates_fst_zero, positionSplitCoordinates_fst_one, Real.norm_eq_abs, sq_abs]
      rw [hp] at he
      nlinarith [sq_nonneg (x 2)]
    have h := slabPotential_interior_error hrho hH hS x
      ((hcoord 0).trans hRH) ((hcoord 1).trans hRH) ((hcoord 2).trans hRS)
    change |slabResidualMultiplier rho H S x| ≤ _ at h
    calc
      _ ≤ 64*rho*S*((x 0)^2+(x 1)^2)/H+6*Real.pi*rho*S^3/H := h
      _ = a+b*((x 0)^2+(x 1)^2) := by dsimp [a,b]; ring
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hxy hb)
  have hinnerSq (x : Position) (hx : x ∈ K) : slabOrbitalResidual rho H S freq u x^2 ≤
      2*a^2*localizedDensity freq u x+2*b^2*(‖x‖^4*localizedDensity freq u x) := by
    have h := square_times_density_bound ha hb (sq_nonneg ‖x‖)
      (localizedDensity_nonnegative freq u x) (hinner x hx)
    convert h using 1 <;> dsimp [slabOrbitalResidual, localizedDensity] <;> ring
  have houterSq (x : Position) : slabOrbitalResidual rho H S freq u x^2 ≤
      2*A^2*localizedDensity freq u x+2*B^2*(‖x‖^4*localizedDensity freq u x) := by
    have h := square_times_density_bound hA hB (sq_nonneg ‖x‖)
      (localizedDensity_nonnegative freq u x) (slabResidualMultiplier_abs_bound hrho hH.le hS x)
    convert h using 1 <;> dsimp [slabOrbitalResidual, localizedDensity, A, B] <;> ring
  have hinside := setIntegral_mono_on hi.integrableOn
    ((hd.const_mul (2*a^2)).add (h4.const_mul (2*b^2))).integrableOn hK hinnerSq
  have houtside := setIntegral_mono_on hi.integrableOn
    ((hd.const_mul (2*A^2)).add (h4.const_mul (2*B^2))).integrableOn hK.compl
    (fun x _ => houterSq x)
  simp only [Pi.add_apply] at hinside houtside
  rw [integral_add (hd.const_mul (2*a^2)).integrableOn (h4.const_mul (2*b^2)).integrableOn,
    integral_const_mul, integral_const_mul] at hinside
  rw [integral_add (hd.const_mul (2*A^2)).integrableOn (h4.const_mul (2*B^2)).integrableOn,
    integral_const_mul, integral_const_mul] at houtside
  have hmass : (∫ x in K, localizedDensity freq u x) ≤ 1 := by
    rw [← localizedDensity_mass hfreq u]
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (localizedDensity_nonnegative freq u)) hd
  have hmoment : (∫ x in K, ‖x‖^4*localizedDensity freq u x) ≤ localizedDensityMoment freq u 4 :=
    integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun x => mul_nonneg (pow_nonneg (norm_nonneg x) 4)
        (localizedDensity_nonnegative freq u x))) h4
  have ht0 := localizedDensity_mass_tail_seventySecond hfreq hR u hK hout
  have ht4 := localizedDensity_fourth_tail_seventySecond hfreq hR u hK hout
  have hsum := add_le_add (hinside.trans (add_le_add
    (mul_le_mul_of_nonneg_left hmass (by positivity))
    (mul_le_mul_of_nonneg_left hmoment (by positivity))))
    (houtside.trans (add_le_add (mul_le_mul_of_nonneg_left ht0 (by positivity))
      (mul_le_mul_of_nonneg_left ht4 (by positivity))))
  rw [integral_add_compl hK hi] at hsum
  simpa only [mul_one, a, b, A, B, add_assoc] using hsum

end ContinuumCoulomb

end

end OAI
