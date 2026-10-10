import Mathlib
import OAI.Analysis.Conductivity.Fourier.PeriodicBandCompactness
import OAI.Analysis.Conductivity.Walls.EndingJoinCutoff

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def delayedInitialTensor (lam k J R : ℝ) (x : Coord3) : Mat3 :=
  fun i j => pureModeTensor (initialConnectorAngular (lam/k) (1/2) J (k*(x 0-R))) 1
    (angularAxisSwap i) (angularAxisSwap j)

lemma delayedInitialTensor_smooth (lam k J R : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (delayedInitialTensor lam k J R) := by
  have hq : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x : Coord3 => initialConnectorAngular (lam/k) (1/2) J (k*(x 0-R))) :=
    (initialConnectorAngular_smooth _ _ _).comp (contDiff_const.mul ((contDiff_apply ℝ ℝ 0).sub contDiff_const))
  have hh := pureModeTensor_smooth hq (1:Fin 3)
  apply contDiff_pi.mpr; intro i
  apply contDiff_pi.mpr; intro j
  exact contDiff_pi.mp (contDiff_pi.mp hh (angularAxisSwap i)) (angularAxisSwap j)

lemma delayedInitialTensor_symm (lam k J R : ℝ) (x : Coord3) :
    (delayedInitialTensor lam k J R x).IsSymm := by
  ext i j
  exact congrFun (congrFun (pureModeTensor_symm _ _) (angularAxisSwap i)) (angularAxisSwap j)

lemma delayedEndingTensor_initial {lam k J L K R : ℝ} (x : Coord3) (hx : k*(x 0-R)<J+2) :
    delayedEndingTensor lam k J L K R x=delayedInitialTensor lam k J R x := by
  ext i j
  change finiteEndingTensor (lam/k) J L K (permutedDilation angularAxisSwap k (x-Pi.single 0 R))
    (angularAxisSwap i) (angularAxisSwap j)=_
  have ht : (permutedDilation angularAxisSwap k (x-Pi.single 0 R)) 0=k*(x 0-R) := by
    simp [permutedDilation,angularAxisSwap_apply]
  rw [finiteEndingTensor,ht,ite_eq_left hx]
  rfl

def endingJoinMiddleTensor (s : Fin 3 → ℝ) (lam k J : ℝ) (x : Coord3) : Symmetric3 :=
  ⟨(1-endingJoinCutoff (x 0)) • flatBackgroundTensor s+
    endingJoinCutoff (x 0) • delayedInitialTensor lam k J 7 x,
    ((flatBackgroundTensor_symm s).smul _).add ((delayedInitialTensor_symm _ _ _ _ _).smul _)⟩

lemma endingJoinMiddleTensor_smooth (s : Fin 3 → ℝ) (lam k J : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => (endingJoinMiddleTensor s lam k J x).val) := by
  have hχ := endingJoinCutoff_smooth.comp (contDiff_apply ℝ ℝ (0:Fin 3))
  exact ((contDiff_const.sub hχ).smul contDiff_const).add (hχ.smul (delayedInitialTensor_smooth _ _ _ _))

lemma endingJoinMiddle_regular_ae (s : Fin 3 → ℝ) (lam J : ℝ) {k : ℝ} (hk : k≠0) :
    ∀ᵐ x : Coord3,x∈regularRegion (wallCoordinatePair (pureWallMode 1 lam k))
      (endingJoinMiddleTensor s lam k J) univ := by
  have hu : ContDiff ℝ (↑(⊤:ℕ∞)) (wallCoordinatePair (pureWallMode 1 lam k)) :=
    wallCoordinatePair_smooth (pureWallMode_smooth _ _ _)
  have hh := regularRegion_ae_of_simple_minor hu (endingJoinMiddleTensor_smooth s lam k J) isOpen_univ
    (fun x _ hx => (pureMode_pairMinor_noncritical (by norm_num : (1:ℝ)≠0) hk x).resolve_left (not_not.mpr hx))
  filter_upwards [hh] with x hx
  exact hx (mem_univ _)

lemma wallCoordinatePair_pure (lam k : ℝ) (x : Coord3) :
    wallCoordinatePair (pureWallMode 1 lam k) x=![x 0,exp (-lam*x 0)*cos (k*x 2)] := by
  simp [wallCoordinatePair,pureWallMode,boxCoordinates_apply]

end ScalarConductivity

end
end

end OAI
