import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoordinateLaplacian
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedOrbitalResidual
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabRegularity
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedModeDerivatives

namespace OAI

/-! The differential residual is an actual weak-H1 kinetic/potential
pairing identity. This is the bridge used for the off-diagonal form bound. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def oneElectronLocalizedMode (freq : ℝ) (u : PlanarPosition) (x : Configuration 1) : ℝ :=
  continuumLocalizedMode freq u (oneElectronCoordinates x)

theorem oneElectronLocalizedMode_C2 (freq : ℝ) (u : PlanarPosition) :
    ContDiff ℝ 2 (oneElectronLocalizedMode freq u) :=
  ((continuumLocalizedMode_C7 freq u).of_le (by norm_num)).comp oneElectronCoordinates.contDiff

theorem oneElectronLocalizedMode_memLp {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) :
    MemLp (oneElectronLocalizedMode freq u) 2 :=
  (continuumLocalizedMode_memLp hfreq u).comp_measurePreserving oneElectronCoordinates.measurePreserving

theorem oneElectronLocalizedMode_partial (freq : ℝ) (u : PlanarPosition)
    (a : Fin 1 × Fin 3) (x : Configuration 1) :
    configurationRealPartial (oneElectronLocalizedMode freq u) a x =
      fderiv ℝ (continuumLocalizedMode freq u) (oneElectronCoordinates x)
        (oneElectronCoordinates (EuclideanSpace.single a 1)) := by
  exact congrArg (fun L : Configuration 1 →L[ℝ] ℝ => L (EuclideanSpace.single a 1))
    (((continuumLocalizedMode_C7 freq u).differentiable (by norm_num) _).hasFDerivAt.comp x
      oneElectronCoordinates.toContinuousLinearEquiv.hasFDerivAt).fderiv

theorem oneElectronLocalizedMode_partial_memLp {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (a : Fin 1 × Fin 3) :
    MemLp (configurationRealPartial (oneElectronLocalizedMode freq u) a) 2 := by
  have he : configurationRealPartial (oneElectronLocalizedMode freq u) a =
      (fun x => fderiv ℝ (continuumLocalizedMode freq u) (oneElectronCoordinates x)
        (oneElectronCoordinates (EuclideanSpace.single a 1))) :=
    funext (oneElectronLocalizedMode_partial freq u a)
  rw [he]
  exact (continuumLocalizedMode_fderiv_memLp hfreq u _).comp_measurePreserving
    oneElectronCoordinates.measurePreserving

theorem oneElectronLocalizedMode_laplacian (freq : ℝ) (u : PlanarPosition) (x : Configuration 1) :
    configurationRealLaplacian (oneElectronLocalizedMode freq u) x =
      splitLaplacian (localizedMode freq u) (positionSplitCoordinates (oneElectronCoordinates x)) :=
  oneElectron_split_laplacian _ ((localizedMode_C7 freq u).of_le (by norm_num)) x

private theorem manufactured_mode_product_memLp {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 < S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (j : Fin m) :
    MemLp (fun x : Configuration 1 => manufacturedSlabPotential rho H S freq scale u
      (oneElectronCoordinates x)*oneElectronLocalizedMode freq (u j) x) 2 := by
  obtain ⟨B,hB⟩ := manufacturedSlabPotential_bounded hrho hH hS freq scale u
  apply (oneElectronLocalizedMode_memLp hfreq (u j)).of_le_mul (c := B)
    ((((manufacturedSlabPotential_continuous hrho hH hS.le freq scale u).comp
      oneElectronCoordinates.continuous).mul (oneElectronLocalizedMode_C2 freq (u j)).continuous).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖manufacturedSlabPotential rho H S freq scale u (oneElectronCoordinates x)*
    oneElectronLocalizedMode freq (u j) x‖ ≤ _
  rw [norm_mul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)

theorem oneElectronLocalizedMode_laplacian_memLp {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 < S) (hfreq : 0 < freq)
    (hrelation : freq^2 = 4*Real.pi*rho) (scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (j : Fin m) :
    MemLp (configurationRealLaplacian (oneElectronLocalizedMode freq (u j))) 2 := by
  have hR := (manufacturedOrbitalResidual_memLp hrho hH hS.le hfreq scale u hδ hcoeff j).comp_measurePreserving oneElectronCoordinates.measurePreserving
  have hV := manufactured_mode_product_memLp hrho hH hS hfreq scale u j
  have hE := (oneElectronLocalizedMode_memLp hfreq (u j)).const_mul ((-1/2:ℝ)+freq/2)
  have he : configurationRealLaplacian (oneElectronLocalizedMode freq (u j)) =
      (fun x => 2*(manufacturedSlabPotential rho H S freq scale u (oneElectronCoordinates x)*
        oneElectronLocalizedMode freq (u j) x-
        ((-1/2:ℝ)+freq/2)*oneElectronLocalizedMode freq (u j) x-
        manufacturedOrbitalResidual rho H S freq scale u j (oneElectronCoordinates x))) := by
    funext x
    rw [oneElectronLocalizedMode_laplacian]
    have h := manufacturedOrbitalResidual_eq hrelation H S scale u j (oneElectronCoordinates x)
    change _ = 2*(_*continuumLocalizedMode freq (u j) _-
      ((-1/2:ℝ)+freq/2)*continuumLocalizedMode freq (u j) _-_)
    linarith
  rw [he]
  exact ((hV.sub hE).sub hR).const_mul 2


theorem manufacturedOrbitalResidual_weak_identity
    (hdensity : PublishedSobolevSmoothDensity) {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 < S) (hfreq : 0 < freq)
    (hrelation : freq^2 = 4*Real.pi*rho) (scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (j : Fin m)
    (v : Coulomb.H1Vector 1) (s : SpinConfiguration 1) :
    (1/2:ℂ)*(∑ a, ∫ x, v.gradient s a x*
      (configurationRealPartial (oneElectronLocalizedMode freq (u j)) a x : ℂ))+
      (∫ x, v.value s x*(manufacturedSlabPotential rho H S freq scale u
        (oneElectronCoordinates x)*oneElectronLocalizedMode freq (u j) x : ℝ))-
      (((-1/2:ℝ)+freq/2):ℂ)*(∫ x, v.value s x*(oneElectronLocalizedMode freq (u j) x : ℂ)) =
      ∫ x, v.value s x*(manufacturedOrbitalResidual rho H S freq scale u j
        (oneElectronCoordinates x) : ℂ) := by
  let φ := oneElectronLocalizedMode freq (u j)
  have hLap := oneElectronLocalizedMode_laplacian_memLp hrho hH hS hfreq hrelation scale u hδ hcoeff j
  have hi := weakH1_laplacian_pairing hdensity φ (oneElectronLocalizedMode_C2 freq (u j))
    (oneElectronLocalizedMode_partial_memLp hfreq (u j)) hLap v s
  have hLI := (v.value_L2 s).integrable_mul hLap.ofReal
  have hVI := (v.value_L2 s).integrable_mul
    (manufactured_mode_product_memLp hrho hH hS hfreq scale u j).ofReal
  have hPI := (v.value_L2 s).integrable_mul (oneElectronLocalizedMode_memLp hfreq (u j)).ofReal
  have he (x : Configuration 1) :
      v.value s x*(manufacturedOrbitalResidual rho H S freq scale u j
        (oneElectronCoordinates x) : ℂ) =
      (-1/2:ℂ)*(v.value s x*(configurationRealLaplacian φ x : ℂ))+
      v.value s x*(manufacturedSlabPotential rho H S freq scale u
        (oneElectronCoordinates x)*φ x : ℝ)-
      (((-1/2:ℝ)+freq/2):ℂ)*(v.value s x*(φ x : ℂ)) := by
    have h := manufacturedOrbitalResidual_eq hrelation H S scale u j (oneElectronCoordinates x)
    rw [← oneElectronLocalizedMode_laplacian] at h
    dsimp only [φ]
    rw [h]
    push_cast
    simp only [oneElectronLocalizedMode]
    ring
  simp_rw [he]
  have hsub := integral_sub ((hLI.const_mul (-1/2:ℂ)).add hVI)
    (hPI.const_mul (((-1/2:ℝ)+freq/2):ℂ))
  have hadd := integral_add (hLI.const_mul (-1/2:ℂ)) hVI
  simp only [Pi.add_apply,Pi.mul_apply] at hsub hadd
  dsimp only [φ] at hi ⊢
  rw [hadd,integral_const_mul,integral_const_mul] at hsub
  rw [hi]
  let A : ℂ := ∫ x, v.value s x*(configurationRealLaplacian (oneElectronLocalizedMode freq (u j)) x : ℂ)
  let B : ℂ := ∫ x, v.value s x*(manufacturedSlabPotential rho H S freq scale u
    (oneElectronCoordinates x)*oneElectronLocalizedMode freq (u j) x : ℝ)
  let C : ℂ := ∫ x, v.value s x*(oneElectronLocalizedMode freq (u j) x : ℂ)
  let E : ℂ := (((-1/2:ℝ)+freq/2):ℂ)
  change _ = (-1/2:ℂ)*A+B-E*C at hsub
  change (1/2:ℂ)*(-A)+B-E*C = _
  calc
    _ = (-1/2:ℂ)*A+B-E*C := by ring
    _ = _ := hsub.symm

end ContinuumCoulomb

end

end OAI
