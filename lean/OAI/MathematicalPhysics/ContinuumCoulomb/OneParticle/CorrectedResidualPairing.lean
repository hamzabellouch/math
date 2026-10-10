import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CorrectedManufacturedResidual
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteOrbitalLaplacian
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedWeakResidual
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RealOrbitalResidual

namespace OAI

/-! Actual corrected-orbital mixed forms inherit the manufactured residual
bound on every state in the full one-electron weak-H1 domain. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def oneElectronCorrectedMode (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (i : Fin m) (x : Configuration 1) : ℝ :=
  correctedLocalizedMode freq u i (oneElectronCoordinates x)

theorem oneElectronCorrectedMode_C2 (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (i : Fin m) : ContDiff ℝ 2 (oneElectronCorrectedMode freq u i) :=
  ((localizedLinearOrbital_C7 freq u (correctedLocalizedCoefficients u i)).of_le (by norm_num)).comp oneElectronCoordinates.contDiff

theorem oneElectronCorrectedMode_memLp {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) : MemLp (oneElectronCorrectedMode freq u i) 2 :=
  (correctedLocalizedMode_memLp hfreq u i).comp_measurePreserving oneElectronCoordinates.measurePreserving

theorem oneElectronCorrectedMode_partial_memLp {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) (a : Fin 1 × Fin 3) :
    MemLp (configurationRealPartial (oneElectronCorrectedMode freq u i) a) 2 := by
  have he : configurationRealPartial (oneElectronCorrectedMode freq u i) a =
      (fun x => ∑ j, correctedLocalizedCoefficients u i j*
        configurationRealPartial (oneElectronLocalizedMode freq (u j)) a x) :=
    funext (configurationRealPartial_sum _ _
      (fun j => (oneElectronLocalizedMode_C2 freq (u j)).of_le (by norm_num)) a)
  rw [he]
  exact memLp_finsetSum Finset.univ (fun j _ =>
    (oneElectronLocalizedMode_partial_memLp hfreq (u j) a).const_mul _)

theorem correctedManufacturedResidual_eq {rho freq : ℝ}
    (hrelation : freq^2 = 4*Real.pi*rho) (H S scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) (x : Configuration 1) :
    correctedManufacturedResidual rho H S freq scale u i (oneElectronCoordinates x) =
      -(1/2:ℝ)*configurationRealLaplacian (oneElectronCorrectedMode freq u i) x+
      manufacturedSlabPotential rho H S freq scale u (oneElectronCoordinates x)*
        oneElectronCorrectedMode freq u i x-
      ((-1/2:ℝ)+freq/2)*oneElectronCorrectedMode freq u i x := by
  have hlap := configurationRealLaplacian_sum (correctedLocalizedCoefficients u i)
    (fun j => oneElectronLocalizedMode freq (u j)) (fun j => oneElectronLocalizedMode_C2 freq (u j)) x
  have he (j : Fin m) := manufacturedOrbitalResidual_eq hrelation H S scale u j (oneElectronCoordinates x)
  simp_rw [← oneElectronLocalizedMode_laplacian] at he
  change (∑ j, correctedLocalizedCoefficients u i j*
    manufacturedOrbitalResidual rho H S freq scale u j (oneElectronCoordinates x)) = _
  change configurationRealLaplacian (oneElectronCorrectedMode freq u i) x = _ at hlap
  rw [hlap]
  change _ = -(1/2:ℝ)*(∑ j, correctedLocalizedCoefficients u i j*
    configurationRealLaplacian (oneElectronLocalizedMode freq (u j)) x)+
    manufacturedSlabPotential rho H S freq scale u (oneElectronCoordinates x)*
      (∑ j, correctedLocalizedCoefficients u i j*oneElectronLocalizedMode freq (u j) x)-
    ((-1/2:ℝ)+freq/2)*(∑ j, correctedLocalizedCoefficients u i j*oneElectronLocalizedMode freq (u j) x)
  simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [he j]
  simp only [oneElectronLocalizedMode]
  ring

theorem correctedModePairing_square_bound
    (hdensity : PublishedSobolevSmoothDensity) {rho H S freq δ D R : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (hrelation : freq^2 = 4*Real.pi*rho) (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hs : m*localizedOverlapBound D ≤ 1/2)
    (hδ : 0 ≤ δ) (hcoeff : ∀ j, 0 ≤ localizedCounterterm freq u j/scale ∧
      localizedCounterterm freq u j/scale ≤ δ) (i : Fin m)
    (v : Coulomb.H1Vector 1) (s : SpinConfiguration 1) :
    ‖realOrbitalPairing (fun x => manufacturedSlabPotential rho H S freq scale u (oneElectronCoordinates x))
      ((-1/2:ℝ)+freq/2) (oneElectronCorrectedMode freq u i) v s‖^2 ≤
      (4*(m:ℝ)*(∑ j, manufacturedOrbitalSquaredError rho H S freq δ D R u j))*
        (∫ x, ‖v.value s x‖^2) := by
  have hφ := oneElectronCorrectedMode_memLp hfreq u i
  obtain ⟨B,hB⟩ := manufacturedSlabPotential_bounded hrho hH.le hS freq scale u
  have hV : MemLp (fun x : Configuration 1 =>
      manufacturedSlabPotential rho H S freq scale u (oneElectronCoordinates x)*
        oneElectronCorrectedMode freq u i x) 2 := by
    apply hφ.of_le_mul (c := B)
      ((((manufacturedSlabPotential_continuous hrho hH.le hS.le freq scale u).comp
        oneElectronCoordinates.continuous).mul (oneElectronCorrectedMode_C2 freq u i).continuous).aestronglyMeasurable)
    filter_upwards [] with x
    change ‖manufacturedSlabPotential rho H S freq scale u (oneElectronCoordinates x)*
      oneElectronCorrectedMode freq u i x‖ ≤ _
    rw [norm_mul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  have hm := (correctedManufacturedResidual_memLp hrho hH.le hS.le hfreq scale u hδ hcoeff i).comp_measurePreserving oneElectronCoordinates.measurePreserving
  have hb := realOrbitalPairing_square_bound hdensity _ _ _ _ (oneElectronCorrectedMode_C2 freq u i)
    hφ (oneElectronCorrectedMode_partial_memLp hfreq u i) hV hm
    (correctedManufacturedResidual_eq hrelation H S scale u i) v s
  have hint : (∫ x : Configuration 1,
      correctedManufacturedResidual rho H S freq scale u i (oneElectronCoordinates x)^2) =
      ∫ x, correctedManufacturedResidual rho H S freq scale u i x^2 :=
    oneElectronCoordinates_integral (fun x => correctedManufacturedResidual rho H S freq scale u i x^2)
  simp only [Function.comp_def] at hb
  rw [hint] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right
    (correctedManufacturedResidual_square_bound hrho hH hS hfreq hR hRH hRS scale u hsep hs hδ hcoeff i)
    (integral_nonneg (fun _ => sq_nonneg _)))

end ContinuumCoulomb

end

end OAI
