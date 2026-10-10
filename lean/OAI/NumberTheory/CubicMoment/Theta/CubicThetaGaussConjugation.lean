import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEven
import OAI.NumberTheory.CubicGram.Reciprocity

namespace OAI

/-! Complex conjugation of the finite arithmetic data used to normalize
Patterson's theta series. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicTheta_gauss_conjugate {b : Eisenstein} (hb : primary b) :
    gauss (conjugate b) = star (gauss b) := by
  refine primary_induction (P := fun b => gauss (conjugate b) = star (gauss b)) ?_ ?_ hb
  · simp only [map_one, gauss_one, star_one]
  · intro p c hp hc ih
    rw [map_mul, gauss_mul (primary_conjugate hp.1) (primary_conjugate hc),
      gauss_mul hp.1 hc, cubicSymbol_conjugate hc p, ih,
      gauss_prime (primaryPrime_conjugate hp), gaussAtPrime_conjugate hp,
      ← gauss_prime hp, star_mul, star_mul, star_star]
    ring

lemma cubicTheta_conjugate_lambda : conjugate lambdaE = -lambdaE := by
  apply Subtype.ext
  change star (traceLambda) = -traceLambda
  simp only [traceLambda, star_add, star_mul, star_ofNat, star_one, star_omega]
  linear_combination 2*omega_quadratic

lemma cubicTheta_squarefree_conjugate {b : Eisenstein} (hb : Squarefree b) :
    Squarefree (conjugate b) := by
  intro c hc
  have hd := conjugate.map_dvd hc
  change conjugate (c*c) ∣ conjugate (conjugate b) at hd
  rw [map_mul, conjugate_conjugate] at hd
  have hu := hb _ hd
  have hu' : IsUnit (conjugate (conjugate c)) := hu.map conjugate.toMonoidHom
  simpa only [conjugate_conjugate] using hu'

end CubicFirstMoment

end

end OAI
