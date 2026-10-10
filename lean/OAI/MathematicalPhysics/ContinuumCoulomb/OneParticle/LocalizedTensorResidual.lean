import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.SpinTensorResidual
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedFockStates
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CorrectedManufacturedResidual

namespace OAI

/-! The actual corrected manufactured orbital residuals, lifted to both spin
components and all electron coordinates, satisfy a polynomial L2 estimate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def localizedSpinResidual (rho H S freq scale : ℝ) {m : ℕ}
    (u : Fin (m+1) → PlanarPosition) (j : Fin ((2*m+1)+1)) : Position → Fin 2 → ℂ :=
  realSpinOrbital (correctedManufacturedResidual rho H S freq scale u
    ((HubbardGlobal.siteModes m).symm j).1) ((HubbardGlobal.siteModes m).symm j).2

theorem localizedSpinResidual_memLp {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition) {η : ℝ} (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η) (j : Fin ((2*m+1)+1)) (s : Fin 2) :
    MemLp (fun x => localizedSpinResidual rho H S freq scale u j x s) 2 :=
  realSpinOrbital_memLp _
    (correctedManufacturedResidual_memLp hrho hH hS hfreq scale u hη hcoeff _) _ s

theorem localizedSpinResidual_sum_norm {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition) {η : ℝ} (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η) :
    (∑ j, ∫ x, ‖Coulomb.flatSpinOrbital (localizedSpinResidual rho H S freq scale u j) x‖^2
      ∂Coulomb.spinSpaceMeasure) =
      2*∑ i, ∫ x, correctedManufacturedResidual rho H S freq scale u i x^2 := by
  simp only [localizedSpinResidual,flatRealSpinOrbital_norm_sq _
    (correctedManufacturedResidual_memLp hrho hH hS hfreq scale u hη hcoeff _)]
  rw [(HubbardGlobal.siteModes m).symm.sum_comp
    (fun p : Fin (m+1) × Fin 2 => ∫ x, correctedManufacturedResidual rho H S freq scale u p.1 x^2)]
  simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,← Finset.mul_sum]
  norm_num

theorem localizedTensorResidual_L2_bound {rho H S freq η D R : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (scale : ℝ) {m n : ℕ} (u : Fin (m+1) → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : (m+1:ℕ)*localizedOverlapBound D ≤ 1/2) (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η)
    (c : (Fin (n+1) → Fin ((2*m+1)+1)) → ℂ) :
    (∫ x, ‖tensorTotalReplacement (fun j => Coulomb.flatSpinOrbital (localizedSpinMode freq u j))
      (fun j => Coulomb.flatSpinOrbital (localizedSpinResidual rho H S freq scale u j)) c x‖^2
      ∂(Measure.pi fun _ : Fin (n+1) => Coulomb.spinSpaceMeasure)) ≤
      (n+1:ℝ)^2*(8*(m+1:ℕ)^2*∑ j, manufacturedOrbitalSquaredError rho H S freq η D R u j)*
        Coulomb.mass (finiteTensorState (localizedSpinMode freq u)
          (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hfreq u)
          (localizedSpinMode_partial_memLp hfreq u) c) := by
  have h := spinTensorResidual_L2_bound (localizedSpinMode freq u)
    (localizedSpinResidual rho H S freq scale u) (localizedSpinMode_C1 freq u)
    (localizedSpinMode_memLp hfreq u) (localizedSpinMode_partial_memLp hfreq u)
    (localizedSpinResidual_memLp hrho hH.le hS.le hfreq scale u hη hcoeff)
    (fun a b => by
      have h := localizedSpinMode_inner hfreq u hsep hs a b
      by_cases hab : a=b <;> simpa only [hab,ite_true,ite_false] using h) c
  rw [localizedSpinResidual_sum_norm hrho hH.le hS.le hfreq scale u hη hcoeff] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Coulomb.mass_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    correctedManufacturedResidual_square_bound hrho hH hS hfreq hR hRH hRS
      scale u hsep hs hη hcoeff i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at he
  nlinarith only [he]

end ContinuumCoulomb

end

end OAI
