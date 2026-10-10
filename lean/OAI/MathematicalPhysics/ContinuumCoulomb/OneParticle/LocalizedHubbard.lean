import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombCalibration
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.GramPenalty

namespace OAI

/-! The actual localized direct Coulomb matrix satisfies the full charge
penalty condition used by the complete half-filled Hubbard comparison. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def localizedOffsiteCoulomb {m : ℕ} (freq : ℝ) (u : Fin m → PlanarPosition)
    (i j : Fin m) : ℝ := if i = j then 0 else localizedCoulombCoeff freq (u i) (u j)

theorem localizedOffsiteCoulomb_diagonal {m : ℕ} (freq : ℝ) (u : Fin m → PlanarPosition) (i : Fin m) :
    localizedOffsiteCoulomb freq u i i = 0 := by simp [localizedOffsiteCoulomb]

theorem localizedOffsiteCoulomb_symmetric {m : ℕ} {freq : ℝ} (hfreq : 0 < freq)
    (u : Fin m → PlanarPosition) (i j : Fin m) :
    localizedOffsiteCoulomb freq u i j = localizedOffsiteCoulomb freq u j i := by
  simp only [localizedOffsiteCoulomb, eq_comm]
  rw [localizedCoulombCoeff_symmetric hfreq]

theorem localizedCoulomb_diagonal_split {m : ℕ} (freq : ℝ) (u : Fin m → PlanarPosition)
    (d : Fin m → ℝ) :
    (∑ i, ∑ j, localizedCoulombCoeff freq (u i) (u j) * d i * d j) =
      localizedCoulombProfile freq 0 * ∑ i, d i ^ 2 +
        ∑ i, ∑ j, localizedOffsiteCoulomb freq u i j * d i * d j := by
  classical
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ j, ((if i = j then localizedCoulombProfile freq 0 * d i ^ 2 else 0) +
        localizedOffsiteCoulomb freq u i j * d i * d j) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j
      · subst j
        simp only [ite_true, localizedOffsiteCoulomb_diagonal, zero_mul, add_zero,
          localizedCoulombCoeff_distance, sub_self, norm_zero, pow_two]
        ring
      · simp only [ite_eq_right hij, localizedOffsiteCoulomb, zero_add]
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem localizedCoulomb_charge_condition {freq D : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (hleak : m * localLeakageBound freq D ≤ localDualMass freq / 2) (d : Fin m → ℝ) :
    localizedGramConstant freq * ∑ i, d i ^ 2 ≤
      localizedCoulombProfile freq 0 * ∑ i, d i ^ 2 +
        ∑ i, ∑ j, localizedOffsiteCoulomb freq u i j * d i * d j := by
  rw [← localizedCoulomb_diagonal_split]
  exact localizedGram_uniform_coercive hfreq hD u hsep hleak d

namespace HubbardGlobal

theorem localized_hubbard_Heisenberg {Edge : Type*} [Fintype Edge]
    {freq D : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D) (m : ℕ)
    (u : Fin (m + 1) → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (hleak : (m + 1 : ℕ) * localLeakageBound freq D ≤ localDualMass freq / 2)
    (left right : Edge → Fin (m + 1)) (t J : Edge → ℝ)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e = left f ∧ right e = right f) ∧ ¬(left e = right f ∧ right e = left f))
    (hcal : ∀ e, t e ^ 2 = J e *
      (localizedCoulombProfile freq 0 - localizedCoulombCoeff freq (u (left e)) (u (right e))))
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon < 1 / 2)
    (ht : 4 * ∑ e, |t e| ≤ epsilon * localizedGramConstant freq) :
    |hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
        left right t - graphSourceBottom m left right J| ≤
      2 * localizedGramConstant freq * epsilon ^ 3 := by
  apply hubbardFermionBottom_Gram_Heisenberg m (localizedCoulombProfile freq 0)
    (localizedGramConstant freq) (localizedOffsiteCoulomb freq u)
    (localizedOffsiteCoulomb_symmetric hfreq u) (localizedOffsiteCoulomb_diagonal freq u)
    (localizedGramConstant_positive hfreq) (localizedCoulomb_charge_condition hfreq hD u hsep hleak)
    left right t J hloop hsimple ?_ hepsilon hsmall ht
  intro e
  simpa only [localizedOffsiteCoulomb, ite_eq_right (hloop e)] using hcal e

theorem localized_calibrated_hubbard {Edge : Type*} [Fintype Edge]
    {freq D scale τ : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D) (m : ℕ)
    (u : Fin (m + 1) → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (hleak : (m + 1 : ℕ) * localLeakageBound freq D ≤ localDualMass freq / 2)
    (left right : Edge → Fin (m + 1)) (K : Edge → ℝ) (hK : ∀ e, 0 ≤ K e)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e = left f ∧ right e = right f) ∧ ¬(left e = right f ∧ right e = left f))
    (hcal : ∀ e, scale * planarHopping ‖u (left e) - u (right e)‖ =
      coulombHoppingTarget freq τ (K e) ‖u (left e) - u (right e)‖)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon < 1 / 2)
    (ht : 4 * ∑ e, |scale * planarHopping ‖u (left e) - u (right e)‖| ≤
      epsilon * localizedGramConstant freq) :
    |hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
        left right (fun e => scale * planarHopping ‖u (left e) - u (right e)‖) -
      graphSourceBottom m left right (fun e => τ ^ 2 * K e)| ≤
        2 * localizedGramConstant freq * epsilon ^ 3 := by
  apply localized_hubbard_Heisenberg hfreq hD m u hsep hleak left right _ _ hloop hsimple ?_
    hepsilon hsmall ht
  intro e
  have hgap := chargeTransfer_Gram_denominator (localizedCoulombProfile freq 0)
    (localizedGramConstant freq) (localizedOffsiteCoulomb freq u)
    (localizedCoulomb_charge_condition hfreq hD u hsep hleak) (left e) (right e) (hloop e)
    (localizedOffsiteCoulomb_symmetric hfreq u) (localizedOffsiteCoulomb_diagonal freq u)
  simp only [localizedOffsiteCoulomb, ite_eq_right (hloop e)] at hgap
  have hn := (localizedGramConstant_positive hfreq).le.trans hgap
  rw [localizedCoulombCoeff_distance] at hn ⊢
  rw [hcal e, coulombHoppingTarget, mul_pow, Real.sq_sqrt (mul_nonneg (hK e) hn)]
  ring

end HubbardGlobal
end ContinuumCoulomb

end

end OAI
