import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedWellMatrix
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarMultiwellMatrix

namespace OAI

/-! The actual differential action of the full multiwell operator on the
localized modes. Subtraction of the common ground energy leaves exactly the
sum of other wells, so its matrix is the checked hopping matrix plus the
explicit two-tail error. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def multiwellPotential (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (p : SplitPosition) : ℝ :=
  (∑ k, manufacturedPlanarWell (p.1 - u k)) + freq ^ 2 * p.2 ^ 2 / 2

def multiwellAction (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (f : SplitPosition → ℝ) (p : SplitPosition) : ℝ :=
  -(1 / 2 : ℝ) * splitLaplacian f p + multiwellPotential freq u p * f p

theorem multiwellAction_localizedMode (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (j : Fin m) (p : SplitPosition) :
    multiwellAction freq u (localizedMode freq (u j)) p - ((-1 / 2 : ℝ) + freq / 2) * localizedMode freq (u j) p =
      ∑ k, if k = j then 0 else manufacturedPlanarWell (p.1 - u k) * localizedMode freq (u j) p := by
  classical
  have hs : (∑ k, manufacturedPlanarWell (p.1 - u k)) =
      manufacturedPlanarWell (p.1 - u j) + (∑ k, if k = j then 0 else manufacturedPlanarWell (p.1 - u k)) := by
    calc
      _ = ∑ k, ((if k = j then manufacturedPlanarWell (p.1 - u j) else 0) +
          (if k = j then 0 else manufacturedPlanarWell (p.1 - u k))) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k = j <;> simp [hk]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have he := localizedMode_eigen_equation freq (u j) p
  unfold localizedPotential at he
  unfold multiwellAction multiwellPotential
  rw [hs]
  have hm : (∑ k, if k = j then 0 else manufacturedPlanarWell (p.1 - u k)) * localizedMode freq (u j) p =
      ∑ k, if k = j then 0 else manufacturedPlanarWell (p.1 - u k) * localizedMode freq (u j) p := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp only [zero_mul]
  rw [← hm]
  nlinarith only [he]

def localizedOneBodyIntegrand (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (i j : Fin m) (x : Position) : ℝ :=
  continuumLocalizedMode freq (u i) x *
    (multiwellAction freq u (localizedMode freq (u j)) (positionSplitCoordinates x) -
      ((-1 / 2 : ℝ) + freq / 2) * continuumLocalizedMode freq (u j) x)

theorem localizedOneBodyIntegrand_eq (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (i j : Fin m) (x : Position) :
    localizedOneBodyIntegrand freq u i j x =
      ∑ k, if k = j then 0 else localizedWellIntegrand freq (u i) (u j) (u k) x := by
  classical
  unfold localizedOneBodyIntegrand
  change continuumLocalizedMode freq (u i) x *
    (multiwellAction freq u (localizedMode freq (u j)) (positionSplitCoordinates x) -
      ((-1 / 2 : ℝ) + freq / 2) * localizedMode freq (u j) (positionSplitCoordinates x)) = _
  rw [multiwellAction_localizedMode, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs
  · simp only [mul_zero]
  · unfold localizedWellIntegrand continuumLocalizedMode
    ring

theorem localizedOneBodyIntegrand_integrable {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) :
    Integrable (localizedOneBodyIntegrand freq u i j) := by
  classical
  change Integrable (fun x => localizedOneBodyIntegrand freq u i j x)
  simp_rw [localizedOneBodyIntegrand_eq]
  apply integrable_finsetSum
  intro k _
  by_cases hk : k = j
  · simp only [hk, ite_true]
    exact integrable_zero Position ℝ volume
  · simp only [hk, ite_false]
    exact localizedWellIntegrand_integrable hfreq _ _ _

def localizedOneBodyMatrix (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) : ℝ :=
  ∫ x, localizedOneBodyIntegrand freq u i j x

theorem localizedOneBodyMatrix_eq {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) :
    localizedOneBodyMatrix freq u i j = planarMultiwellMatrix u i j := by
  classical
  unfold localizedOneBodyMatrix
  simp_rw [localizedOneBodyIntegrand_eq]
  rw [integral_finsetSum]
  · unfold planarMultiwellMatrix
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k = j
    · simp only [hk, ite_true, integral_zero]
    · simp only [hk, ite_false]
      exact localizedWellIntegrand_integral hfreq _ _ _
  · intro k _
    by_cases hk : k = j
    · simp only [hk, ite_true]
      exact integrable_zero Position ℝ volume
    · simp only [hk, ite_false]
      exact localizedWellIntegrand_integrable hfreq _ _ _

theorem localizedOneBodyMatrix_error_bound {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖) (i j : Fin m) :
    |localizedOneBodyMatrix freq u i j - planarHoppingMatrix u i j| ≤
      m * planarWellMatrixConstant * Real.exp (-(19 / 10 : ℝ) * D) := by
  rw [localizedOneBodyMatrix_eq hfreq]
  exact planarMultiwellMatrix_error_bound u hsep i j

end ContinuumCoulomb

end

end OAI
