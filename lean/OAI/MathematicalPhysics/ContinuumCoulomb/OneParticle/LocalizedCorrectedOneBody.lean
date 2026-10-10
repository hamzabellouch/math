import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedOneBody
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCountertermMatrix

namespace OAI

/-! The actual one-body operator including well-depth counterterms. Its
shifted matrix is exactly the base multiwell matrix plus the weighted well
matrix divided by the physical scale. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def correctedMultiwellAction (freq scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (f : SplitPosition → ℝ) (p : SplitPosition) : ℝ :=
  multiwellAction freq u f p + scale⁻¹ *
    (∑ k, localizedCounterterm freq u k * manufacturedPlanarWell (p.1 - u k)) * f p

def localizedCorrectedOneBodyIntegrand (freq scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (i j : Fin m) (x : Position) : ℝ :=
  continuumLocalizedMode freq (u i) x *
    (correctedMultiwellAction freq scale u (localizedMode freq (u j)) (positionSplitCoordinates x) -
      ((-1 / 2 : ℝ) + freq / 2) * continuumLocalizedMode freq (u j) x)

theorem localizedCorrectedOneBodyIntegrand_eq (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i j : Fin m) (x : Position) :
    localizedCorrectedOneBodyIntegrand freq scale u i j x = localizedOneBodyIntegrand freq u i j x +
      scale⁻¹ * ∑ k, localizedCounterterm freq u k * localizedWellIntegrand freq (u i) (u j) (u k) x := by
  have hs : continuumLocalizedMode freq (u i) x *
      (scale⁻¹ * (∑ k, localizedCounterterm freq u k *
        manufacturedPlanarWell ((positionSplitCoordinates x).1 - u k)) * continuumLocalizedMode freq (u j) x) =
      scale⁻¹ * ∑ k, localizedCounterterm freq u k * localizedWellIntegrand freq (u i) (u j) (u k) x := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    unfold localizedWellIntegrand
    ring
  unfold localizedCorrectedOneBodyIntegrand correctedMultiwellAction localizedOneBodyIntegrand
  change continuumLocalizedMode freq (u i) x *
      (multiwellAction freq u (localizedMode freq (u j)) (positionSplitCoordinates x) +
        scale⁻¹ * (∑ k, localizedCounterterm freq u k *
          manufacturedPlanarWell ((positionSplitCoordinates x).1 - u k)) * continuumLocalizedMode freq (u j) x -
        ((-1 / 2 : ℝ) + freq / 2) * continuumLocalizedMode freq (u j) x) = _
  nlinarith only [hs]

theorem localizedCorrectedOneBodyIntegrand_integrable {freq : ℝ} (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) :
    Integrable (localizedCorrectedOneBodyIntegrand freq scale u i j) := by
  have hi : Integrable (fun x => ∑ k, localizedCounterterm freq u k *
      localizedWellIntegrand freq (u i) (u j) (u k) x) :=
    integrable_finsetSum _ (fun k _ => (localizedWellIntegrand_integrable hfreq _ _ _).const_mul _)
  change Integrable (fun x => localizedCorrectedOneBodyIntegrand freq scale u i j x)
  simp_rw [localizedCorrectedOneBodyIntegrand_eq]
  exact (localizedOneBodyIntegrand_integrable hfreq u i j).add (hi.const_mul _)

def localizedCorrectedOneBodyMatrix (freq scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) : ℝ :=
  ∫ x, localizedCorrectedOneBodyIntegrand freq scale u i j x

theorem localizedCorrectedOneBodyMatrix_eq {freq : ℝ} (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) :
    localizedCorrectedOneBodyMatrix freq scale u i j =
      localizedOneBodyMatrix freq u i j + scale⁻¹ * localizedCountertermMatrix freq u i j := by
  have hi (k : Fin m) : Integrable (fun x => localizedCounterterm freq u k *
      localizedWellIntegrand freq (u i) (u j) (u k) x) :=
    (localizedWellIntegrand_integrable hfreq _ _ _).const_mul _
  unfold localizedCorrectedOneBodyMatrix
  simp_rw [localizedCorrectedOneBodyIntegrand_eq]
  rw [integral_add (localizedOneBodyIntegrand_integrable hfreq u i j)
      ((integrable_finsetSum Finset.univ (fun k _ => hi k)).const_mul _), integral_const_mul,
    integral_finsetSum Finset.univ (fun k _ => hi k)]
  simp only [integral_const_mul, localizedWellIntegrand_integral hfreq]
  rfl

theorem localizedCorrectedOneBodyMatrix_scaled {freq scale : ℝ} (hfreq : 0 < freq) (hscale : scale ≠ 0)
    {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) :
    scale * localizedCorrectedOneBodyMatrix freq scale u i j =
      scale * localizedOneBodyMatrix freq u i j + localizedCountertermMatrix freq u i j := by
  rw [localizedCorrectedOneBodyMatrix_eq hfreq, mul_add, ← mul_assoc, mul_inv_cancel₀ hscale, one_mul]

end ContinuumCoulomb

end

end OAI
