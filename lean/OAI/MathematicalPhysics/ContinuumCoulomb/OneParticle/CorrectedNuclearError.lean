import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.OrthonormalLocalizedModes
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedOrbitalNuclearError

namespace OAI

/-! Finite basis correction of the actual nuclear error form. Only
polynomially many orbital matrix entries are summed. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedLinearOrbital_weighted_integrable (freq : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (F : Position → ℝ)
    (hI : ∀ i j, Integrable (fun x => F x*continuumLocalizedMode freq (u i) x*
      continuumLocalizedMode freq (u j) x)) (a b : Fin m → ℝ) :
    Integrable (fun x => F x*localizedLinearOrbital freq u a x*localizedLinearOrbital freq u b x) := by
  have hi (i j : Fin m) : Integrable (fun x => (a i*b j)*
      (F x*continuumLocalizedMode freq (u i) x*continuumLocalizedMode freq (u j) x)) :=
    (hI i j).const_mul _
  have he (x : Position) : F x*localizedLinearOrbital freq u a x*localizedLinearOrbital freq u b x =
      ∑ i, ∑ j, (a i*b j)*(F x*continuumLocalizedMode freq (u i) x*continuumLocalizedMode freq (u j) x) := by
    simp only [localizedLinearOrbital,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))

theorem localizedLinearOrbital_weighted_pairing (freq : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (F : Position → ℝ)
    (hI : ∀ i j, Integrable (fun x => F x*continuumLocalizedMode freq (u i) x*
      continuumLocalizedMode freq (u j) x)) (a b : Fin m → ℝ) :
    (∫ x, F x*localizedLinearOrbital freq u a x*localizedLinearOrbital freq u b x) =
      ∑ i, ∑ j, (a i*b j)*(∫ x, F x*continuumLocalizedMode freq (u i) x*
        continuumLocalizedMode freq (u j) x) := by
  have hi (i j : Fin m) : Integrable (fun x => (a i*b j)*
      (F x*continuumLocalizedMode freq (u i) x*continuumLocalizedMode freq (u j) x)) :=
    (hI i j).const_mul _
  have he (x : Position) : F x*localizedLinearOrbital freq u a x*localizedLinearOrbital freq u b x =
      ∑ i, ∑ j, (a i*b j)*(F x*continuumLocalizedMode freq (u i) x*continuumLocalizedMode freq (u j) x) := by
    simp only [localizedLinearOrbital,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  simp only [integral_const_mul]

theorem correctedLocalizedMode_nuclear_error {freq D ε : ℝ} {m : ℕ}
    (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m*localizedOverlapBound D ≤ 1/2) (F : Position → ℝ)
    (hI : ∀ i j, Integrable (fun x => F x*continuumLocalizedMode freq (u i) x*
      continuumLocalizedMode freq (u j) x))
    (herror : ∀ i j, |∫ x, F x*continuumLocalizedMode freq (u i) x*
      continuumLocalizedMode freq (u j) x| ≤ ε) (i j : Fin m) :
    Integrable (fun x => F x*correctedLocalizedMode freq u i x*correctedLocalizedMode freq u j x) ∧
      |∫ x, F x*correctedLocalizedMode freq u i x*correctedLocalizedMode freq u j x| ≤
        4*(m:ℝ)^2*ε := by
  refine ⟨localizedLinearOrbital_weighted_integrable freq u F hI _ _,?_⟩
  rw [correctedLocalizedMode,correctedLocalizedMode,localizedLinearOrbital_weighted_pairing freq u F hI]
  have hb (p q : Fin m) : |(correctedLocalizedCoefficients u i p*correctedLocalizedCoefficients u j q)*
      (∫ x, F x*continuumLocalizedMode freq (u p) x*continuumLocalizedMode freq (u q) x)| ≤ 4*ε := by
    rw [abs_mul,abs_mul]
    have hc := mul_le_mul (correctedLocalizedCoefficients_entries u hsep hs i p).2
      (correctedLocalizedCoefficients_entries u hsep hs j q).2 (abs_nonneg _) (by norm_num)
    have he := mul_le_mul hc (herror p q) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2*2)
    simpa only [show (2:ℝ)*2=4 by norm_num] using he
  calc
    _ ≤ ∑ p : Fin m, ∑ q : Fin m, |(correctedLocalizedCoefficients u i p*correctedLocalizedCoefficients u j q)*
        (∫ x, F x*continuumLocalizedMode freq (u p) x*continuumLocalizedMode freq (u q) x)| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun p _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _p : Fin m, ∑ _q : Fin m, 4*ε :=
      Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ => hb p q))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end ContinuumCoulomb

end

end OAI
