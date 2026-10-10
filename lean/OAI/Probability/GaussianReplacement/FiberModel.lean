import OAI.Probability.GaussianReplacement.FiberBlock

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory





def fiberObservationLaw (d k : ℕ) : Measure ((Rows k d×(Fin k→ℝ))×Sphere d) :=
  ((gaussianRows k d).prod (uniformSphere d)).map
    (fun z => ((z.1,label z.1 (z.2:Vector d)),z.2))

lemma measurable_fiberObservationMap {d k : ℕ} :
    Measurable (fun z : Rows k d×Sphere d => ((z.1,label z.1 (z.2:Vector d)),z.2)) :=
  (measurable_fst.prodMk measurable_own_label).prodMk measurable_snd

instance uniformSphere_finite (d : ℕ) : IsFiniteMeasure (uniformSphere d) := by
  constructor
  unfold uniformSphere
  rw [Measure.smul_apply, smul_eq_mul]
  exact lt_of_le_of_lt (ENNReal.inv_mul_le_one _) ENNReal.one_lt_top

instance fiberObservationLaw_finite (d k : ℕ) : IsFiniteMeasure (fiberObservationLaw d k) := by
  unfold fiberObservationLaw
  infer_instance

lemma sphere_standardBorel (d : ℕ) : StandardBorelSpace (Sphere d) :=
  Metric.isClosed_sphere.measurableSet.standardBorel

def sphericalFiberKernel (d k : ℕ) [sphereNonempty : Nonempty (Sphere d)] :
    Kernel (Rows k d×(Fin k→ℝ)) (Sphere d) :=
  @Measure.condKernel (Rows k d×(Fin k→ℝ)) (Sphere d) _ _
    (sphere_standardBorel d) sphereNonempty
    (fiberObservationLaw d k) (fiberObservationLaw_finite d k)

instance sphericalFiberKernel_markov (d k : ℕ) [Nonempty (Sphere d)] :
    IsMarkovKernel (sphericalFiberKernel d k) := by
  unfold sphericalFiberKernel
  infer_instance


def fiberTwoPointLeft (d k : ℕ) [Nonempty (Sphere d)] : Measure (Rows k d×(Sphere d×Sphere d)) :=
  ((((gaussianRows k d).prod (uniformSphere d)).withDensity
    (fun z => exactDensity (uniformSphere d) z.1 (label z.1 (z.2:Vector d)))) ⊗ₘ
    ((sphericalFiberKernel d k).comap (fun z => (z.1,label z.1 (z.2:Vector d)))
      (measurable_fst.prodMk measurable_own_label))).map
    (fun z => (z.1.1,(z.1.2,z.2)))


def perpendicularRow {d : ℕ} (v g : Vector d) : Vector d :=
  letI : NormedAddCommGroup (Vector d) := PiLp.normedAddCommGroup 2 (fun _ : Fin d => ℝ)
  letI : InnerProductSpace ℝ (Vector d) := PiLp.innerProductSpace (fun _ : Fin d => ℝ)
  g - (⟪v,g⟫ / ‖v‖^2) • v

lemma measurable_perpendicularRow {d : ℕ} :
    Measurable (fun z : Vector d×Vector d => perpendicularRow z.1 z.2) := by
  unfold perpendicularRow
  fun_prop

def perpendicularRowsKernel (d k : ℕ) : Kernel (Sphere d×Sphere d) (Rows k d) :=
  dependentMapKernel (Kernel.const (Sphere d×Sphere d) (gaussianRows k d))
    (fun z => fun i => perpendicularRow ((z.1.1:Vector d)-(z.1.2:Vector d)) (z.2 i))


def fiberTwoPointConstant (k : ℕ) : ℝ≥0∞ :=
  letI : OfNat ℝ 2 := @instOfNatAtLeastTwo ℝ 2 Real.instNatCast inferInstance
  letI : Mul ℝ := Real.instMul
  letI : Inv ℝ := Real.instInv
  letI : Pow ℝ ℕ := @NPow.toPow ℝ Real.instMonoid.toNPow
  ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹ ^ k)

def fiberDistanceWeight {d : ℕ} (k : ℕ) (z : Sphere d×Sphere d) : ℝ≥0∞ :=
  (ENNReal.ofReal ‖(z.1:Vector d)-(z.2:Vector d)‖)⁻¹ ^ k


def fiberTwoPointRight (d k : ℕ) : Measure (Rows k d×(Sphere d×Sphere d)) :=
  letI : IsScalarTower ℝ≥0∞ ℝ≥0∞ ℝ≥0∞ := Semigroup.isScalarTower
  fiberTwoPointConstant k •
    Measure.map (Prod.swap : (Sphere d×Sphere d)×Rows k d → Rows k d×(Sphere d×Sphere d))
      (Measure.compProd
        (Measure.withDensity (Measure.prod (uniformSphere d) (uniformSphere d))
          (fiberDistanceWeight k))
        (perpendicularRowsKernel d k))


def FiberTwoPointMain : Prop :=
  ∀ (d k : ℕ) (_hk : 1 ≤ k) (hkd : k < d-1),
    letI : IsProbabilityMeasure (uniformSphere d) :=
      uniformSphere_probability_of_pos (by omega)
    letI : Nonempty (Sphere d) := nonempty_of_isProbabilityMeasure (uniformSphere d)
    IsFiniteMeasure (fiberTwoPointLeft d k) ∧ IsFiniteMeasure (fiberTwoPointRight d k) ∧
      fiberTwoPointLeft d k = fiberTwoPointRight d k



end CurrentProjection

end

end OAI
