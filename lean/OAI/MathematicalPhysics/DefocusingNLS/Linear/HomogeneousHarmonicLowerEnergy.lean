import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLowerOrder
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicPairEnergy

namespace OAI

/-! A smooth harmonic channel of a high-order vector has every intermediate top energy. -/

open Set MeasureTheory
open scoped ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneous_harmonic_pair_lower_topL2 (a : ℝ) (N J : ℕ)
    (ha : 0<a) (ha1 : a<1) (hk : 8<(N : ℝ)) (hJ : 8<(J : ℝ)) (hJN : J≤N)
    (u : HomogeneousY a N × HomogeneousY a N) (Y : E → ℂ)
    (hY : ∀ x : E, x≠0 → ContDiffAt ℝ ∞ Y x)
    (hf : ContDiffOn ℝ ∞
      (harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM a N ha ha1 hk u.1 x)) (Ioi 0))
    (hg : ContDiffOn ℝ ∞
      (harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM a N ha ha1 hk u.2 x)) (Ioi 0)) :
    let A := fun f : HomogeneousY a N =>
      harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM a N ha ha1 hk f x)
    IntegrableOn (fun r => r^11*‖iteratedDeriv J (A u.1) r‖^2) (Ioi 0) ∧
    IntegrableOn (fun r => r^11*‖iteratedDeriv J (A u.2) r‖^2) (Ioi 0) := by
  obtain ⟨v,hv⟩ := exists_homogeneousLowerOrder a J N ha ha1 hJ (by exact_mod_cast hJN) u.1
  obtain ⟨w,hw⟩ := exists_homogeneousLowerOrder a J N ha ha1 hJ (by exact_mod_cast hJN) u.2
  have hfv : (fun x => homogeneousPhysicalCLM a J ha ha1 hJ v x) =
      (fun x => homogeneousPhysicalCLM a N ha ha1 hk u.1 x) := funext hv
  have hgw : (fun x => homogeneousPhysicalCLM a J ha ha1 hJ w x) =
      (fun x => homogeneousPhysicalCLM a N ha ha1 hk u.2 x) := funext hw
  have hf' := hf
  have hg' := hg
  rw [← hfv] at hf'
  rw [← hgw] at hg'
  have h := homogeneous_harmonic_pair_topL2 a J ha ha1 hJ (v,w) Y hY hf' hg'
  dsimp only at h ⊢
  simpa only [hfv,hgw] using h

end DefocusingNLS

end OAI
