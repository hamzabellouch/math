import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedModeDerivatives
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedTransition

namespace OAI

/-! Actual finite linear combinations of localized orbitals. Their
classical partials remain L2, and their integral Gram matrix is the
corresponding finite congruence of the actual overlap matrix. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def localizedLinearOrbital (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (a : Fin m → ℝ) (x : Position) : ℝ :=
  ∑ j, a j * continuumLocalizedMode freq (u j) x

theorem localizedLinearOrbital_C7 (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (a : Fin m → ℝ) : ContDiff ℝ 7 (localizedLinearOrbital freq u a) :=
  ContDiff.sum (fun j _ => contDiff_const.mul (continuumLocalizedMode_C7 freq (u j)))

theorem localizedLinearOrbital_memLp {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (a : Fin m → ℝ) :
    MemLp (localizedLinearOrbital freq u a) 2 := by
  have ht (j : Fin m) : MemLp (fun x => a j * continuumLocalizedMode freq (u j) x) 2 volume :=
    (continuumLocalizedMode_memLp hfreq (u j)).const_mul (a j)
  exact memLp_finsetSum Finset.univ (fun j _ => ht j)

theorem localizedLinearOrbital_fderiv (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (a : Fin m → ℝ) (x e : Position) :
    fderiv ℝ (localizedLinearOrbital freq u a) x e =
      ∑ j, a j * fderiv ℝ (continuumLocalizedMode freq (u j)) x e := by
  have hd (j : Fin m) : DifferentiableAt ℝ (continuumLocalizedMode freq (u j)) x :=
    (continuumLocalizedMode_C7 freq (u j)).differentiable (by norm_num) x
  unfold localizedLinearOrbital
  rw [fderiv_fun_sum (fun j _ => (hd j).const_mul _)]
  simp only [sum_apply, fderiv_const_mul (hd _), smul_apply, smul_eq_mul]

theorem localizedLinearOrbital_fderiv_memLp {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (a : Fin m → ℝ) (e : Position) :
    MemLp (fun x => fderiv ℝ (localizedLinearOrbital freq u a) x e) 2 := by
  have ht (j : Fin m) : MemLp (fun x => a j *
      fderiv ℝ (continuumLocalizedMode freq (u j)) x e) 2 volume :=
    (continuumLocalizedMode_fderiv_memLp hfreq (u j) e).const_mul (a j)
  have hs : MemLp (fun x => ∑ j, a j *
      fderiv ℝ (continuumLocalizedMode freq (u j)) x e) 2 volume :=
    memLp_finsetSum Finset.univ (fun j _ => ht j)
  simpa only [localizedLinearOrbital_fderiv] using hs

theorem localizedLinearOrbital_inner {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (a b : Fin m → ℝ) :
    (∫ x, localizedLinearOrbital freq u a x * localizedLinearOrbital freq u b x) =
      ∑ j, ∑ k, (a j * b k) * planarModeOverlap (u j) (u k) := by
  have hi (j k : Fin m) : Integrable (fun x => (a j * b k) *
      localizedTransition freq (u j) (u k) x) :=
    (localizedTransition_integrable hfreq (u j) (u k)).const_mul _
  have he (x : Position) : localizedLinearOrbital freq u a x * localizedLinearOrbital freq u b x =
      ∑ j, ∑ k, (a j * b k) * localizedTransition freq (u j) (u k) x := by
    unfold localizedLinearOrbital
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    unfold localizedTransition
    ring
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun j _ =>
    integrable_finsetSum Finset.univ (fun k _ => hi j k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum Finset.univ (fun k _ => hi j k)]
  simp only [integral_const_mul, localizedTransition_mass hfreq]

end ContinuumCoulomb

end

end OAI
