import OAI.Analysis.CircleDomains.Topology.PhysicalPlaneCoordinates
import Mathlib.Analysis.Calculus.FDeriv.Mul

namespace OAI

/-! The actual two-coordinate map and its differential, for composing
saved smooth barriers with Sobolev coordinates. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def planePair (a b : ℝ) : EuclideanPlane :=
  a • EuclideanSpace.single (0 : Fin 2) 1+b • EuclideanSpace.single (1 : Fin 2) 1

 @[simp] theorem planePair_zero (a b : ℝ) : planePair a b 0 = a := by
  simp [planePair]

 @[simp] theorem planePair_one (a b : ℝ) : planePair a b 1 = b := by
  simp [planePair]

 theorem planePair_coordinates (x : EuclideanPlane) : planePair (x 0) (x 1) = x := by
  ext i
  fin_cases i <;> simp

 theorem planePair_covector (L : EuclideanPlane →L[ℝ] ℝ) (a b : ℝ) :
    L (planePair a b) = a*L (EuclideanSpace.single (0 : Fin 2) 1)+
      b*L (EuclideanSpace.single (1 : Fin 2) 1) := by
  simp only [planePair, map_add, map_smul, smul_eq_mul]

 theorem continuous_planePair {X : Type*} [TopologicalSpace X] {a b : X → ℝ}
    (ha : Continuous a) (hb : Continuous b) : Continuous (fun x => planePair (a x) (b x)) :=
  (ha.smul continuous_const).add (hb.smul continuous_const)

 theorem contDiff_planePair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → ℝ} {n : WithTop ℕ∞} (ha : ContDiff ℝ n a) (hb : ContDiff ℝ n b) :
    ContDiff ℝ n (fun x => planePair (a x) (b x)) :=
  (ha.smul contDiff_const).add (hb.smul contDiff_const)

 theorem hasFDerivAt_planePair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → ℝ} {Da Db : E →L[ℝ] ℝ} {x : E}
    (ha : HasFDerivAt a Da x) (hb : HasFDerivAt b Db x) :
    HasFDerivAt (fun y => planePair (a y) (b y))
      (Da.smulRight (EuclideanSpace.single (0 : Fin 2) 1)+
       Db.smulRight (EuclideanSpace.single (1 : Fin 2) 1)) x :=
  (ha.smul_const _).add (hb.smul_const _)

 theorem fderiv_planePair_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → ℝ} {Φ : EuclideanPlane → ℝ} {x : E}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hΦ : DifferentiableAt ℝ Φ (planePair (a x) (b x))) (v : E) :
    fderiv ℝ (fun y => Φ (planePair (a y) (b y))) x v =
      fderiv ℝ Φ (planePair (a x) (b x)) (EuclideanSpace.single (0 : Fin 2) 1)*fderiv ℝ a x v+
      fderiv ℝ Φ (planePair (a x) (b x)) (EuclideanSpace.single (1 : Fin 2) 1)*fderiv ℝ b x v := by
  have ht := hΦ.hasFDerivAt.comp x (hasFDerivAt_planePair ha.hasFDerivAt hb.hasFDerivAt)
  change fderiv ℝ (Φ ∘ fun y => planePair (a y) (b y)) x v = _
  rw [ht.fderiv]
  simp only [ContinuousLinearMap.comp_apply, add_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, smul_eq_mul]
  ring

end CircleDomainRigidity

end

end OAI
