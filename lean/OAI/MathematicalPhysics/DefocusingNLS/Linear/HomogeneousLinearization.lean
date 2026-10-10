import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousNonlinearity
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPotentialPicard

namespace OAI

/-! # Actual pointwise linearized potential on the homogeneous space -/

open Set
open scoped ZeroAtInfty

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousPointEvaluation (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (y : E) : HomogeneousY a k →L[ℂ] ℂ where
  toFun f := homogeneousPhysicalCLM a k ha ha1 hk f y
  map_add' f g := by simp only [map_add, ZeroAtInftyContinuousMap.add_apply]
  map_smul' c f := by simp only [map_smul, ZeroAtInftyContinuousMap.smul_apply, RingHom.id_apply]
  cont := ((BoundedContinuousFunction.evalCLM ℂ y).continuous.comp
    ZeroAtInftyContinuousMap.isometry_toBCF.continuous).comp
      (homogeneousPhysicalCLM a k ha ha1 hk).continuous

theorem homogeneousOddPower_fderiv_physical (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (q v : HomogeneousY a k) (y : E) :
    homogeneousPhysicalCLM a k ha ha1 hk (fderiv ℝ (homogeneousOddPower a k ha ha1 hk m) q v) y =
      oddPowerDerivative m (homogeneousPhysicalCLM a k ha ha1 hk q y)
        (homogeneousPhysicalCLM a k ha ha1 hk v y) := by
  let L := (homogeneousPointEvaluation a k ha ha1 hk y).restrictScalars ℝ
  have hL (f : HomogeneousY a k) : L f = homogeneousPhysicalCLM a k ha ha1 hk f y := rfl
  have hN := ((contDiff_homogeneousOddPower a k ha ha1 hk m).differentiable (by simp) q).hasFDerivAt
  have hleft := L.hasFDerivAt.comp q hN
  have hright := (hasFDerivAt_oddPowerNonlinearity m (L q)).comp q L.hasFDerivAt
  have heq : (fun f : HomogeneousY a k => L (homogeneousOddPower a k ha ha1 hk m f)) =
      (fun f : HomogeneousY a k => oddPowerNonlinearity m (L f)) := by
    funext f
    simpa only [hL] using homogeneousOddPower_physical a k ha ha1 hk m f y
  have hderiv : L.comp (fderiv ℝ (homogeneousOddPower a k ha ha1 hk m) q) =
      (oddPowerDerivative m (L q)).comp L := by
    apply hleft.unique
    simpa only [Function.comp_def, ← heq] using hright
  have h := congrArg (fun T : HomogeneousY a k →L[ℝ] ℂ => T v) hderiv
  simpa only [ContinuousLinearMap.comp_apply, hL] using h

/-- The Schrödinger linearization is a bounded real operator on the actual Y space. -/
noncomputable def homogeneousLinearizedPotential (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (q : HomogeneousY a k) :
    HomogeneousY a k →L[ℝ] HomogeneousY a k :=
  (-Complex.I : ℂ) • fderiv ℝ (homogeneousOddPower a k ha ha1 hk m) q

theorem homogeneousLinearizedPotential_physical (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (q v : HomogeneousY a k) (y : E) :
    homogeneousPhysicalCLM a k ha ha1 hk (homogeneousLinearizedPotential a k ha ha1 hk m q v) y =
      -Complex.I * oddPowerDerivative m (homogeneousPhysicalCLM a k ha ha1 hk q y)
        (homogeneousPhysicalCLM a k ha ha1 hk v y) := by
  simp only [homogeneousLinearizedPotential, smul_apply, map_smul,
    ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul, homogeneousOddPower_fderiv_physical]

/-- The previously constructed finite-slab flow applies to the actual profile linearization. -/
theorem existsUnique_homogeneousLinearized_finiteSlab (a b k T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T) (m : ℕ)
    (q u₀ : HomogeneousY a k) :
    ∃! u : C(Icc (0 : ℝ) T, HomogeneousY a k), ∀ t : Icc (0 : ℝ) T,
      u t = homogeneousFreeOperator a b k t ha ha1 hk u₀ +
        homogeneousDuhamel a b k ha ha1 hk t
          (homogeneousPotentialHistory T hT (homogeneousLinearizedPotential a k ha ha1 hk m q) u) :=
  existsUnique_homogeneousPotential_finiteSlab a b k T ha ha1 hk hT
    (homogeneousLinearizedPotential a k ha ha1 hk m q) u₀

end DefocusingNLS

end OAI
