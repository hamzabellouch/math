import OAI.MathematicalPhysics.Boltzmann.Branching.TranslatedCoreKernel
import OAI.MathematicalPhysics.Boltzmann.Jets.FreeCoreMismatch
import OAI.MathematicalPhysics.Boltzmann.Jets.PeriodicJetFamilies

namespace OAI

section

/-! # Measurable regions selecting the unique main periodic core -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

def mainCoreRegion (s₀ η r : ℝ) (N : ℕ) (i : Label) : Set SpaceTime :=
  {z | i.annulus < N ∧ r*z.1 ≤ 1/32 ∧
    r • z.2 ∈ spatialEnlargement s₀ η (r*z.1) i}

theorem measurableSet_mainCoreRegion (s₀ η r : ℝ) (N : ℕ) (i : Label) :
    MeasurableSet (mainCoreRegion s₀ η r N i) := by
  by_cases hi : i.annulus < N
  · have hE : MeasurableSet (JetGeometry.enlargement η (JetGeometry.jetScale s₀ η i.annulus)
        i.positive) := Metric.isClosed_cthickening.measurableSet
    have hy : MeasurableSet {z : SpaceTime |
        VelocityWeight.transverse (r • z.2)-transverseShift i.lattice ∈
          JetGeometry.enlargement η (JetGeometry.jetScale s₀ η i.annulus) i.positive} :=
      hE.preimage (by fun_prop)
    have hz : MeasurableSet {z : SpaceTime |
        |VelocityWeight.axial (r • z.2)-axialShift i.lattice| ≤ 1/8+2*(r*z.1)+1/16} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    have ht : MeasurableSet {z : SpaceTime | r*z.1 ≤ 1/32} :=
      measurableSet_le (by fun_prop) measurable_const
    simp only [mainCoreRegion,hi,true_and]
    exact ht.inter (hy.inter hz)
  · simp [mainCoreRegion,hi]

theorem mainCoreRegion_unique {s₀ η r : ℝ} {N : ℕ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    {i j : Label} {z : SpaceTime}
    (hi : z ∈ mainCoreRegion s₀ η r N i) (hj : z ∈ mainCoreRegion s₀ η r N j) : i = j :=
  common_point_label hs₀ hsmax hη hηmax hi.2.1 hi.2.2 hj.2.2

def mainCoreKernel (s₀ η r : ℝ) (N : ℕ) (K : Label → Kernel SpaceTime Velocity) :
    Kernel SpaceTime Velocity := by
  classical
  exact Kernel.sum (fun i => Kernel.piecewise (measurableSet_mainCoreRegion s₀ η r N i) (K i) 0)

instance mainCoreKernel_sFinite (s₀ η r : ℝ) (N : ℕ) (K : Label → Kernel SpaceTime Velocity)
    [∀ i, IsSFiniteKernel (K i)] : IsSFiniteKernel (mainCoreKernel s₀ η r N K) := by
  classical
  unfold mainCoreKernel
  infer_instance

theorem mainCoreKernel_eq {s₀ η r : ℝ} {N : ℕ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (K : Label → Kernel SpaceTime Velocity) {z : SpaceTime} {i : Label}
    (hi : z ∈ mainCoreRegion s₀ η r N i) : mainCoreKernel s₀ η r N K z = K i z := by
  classical
  apply Measure.ext
  intro E hE
  rw [mainCoreKernel,Kernel.sum_apply' _ _ hE,tsum_eq_single i]
  · simp [Kernel.piecewise_apply',hi]
  · intro j hji
    have hj : z ∉ mainCoreRegion s₀ η r N j :=
      fun hj => hji (mainCoreRegion_unique hs₀ hsmax hη hηmax hj hi)
    simp [Kernel.piecewise_apply',hj]

theorem mainCoreKernel_eq_zero (s₀ η r : ℝ) (N : ℕ) (K : Label → Kernel SpaceTime Velocity)
    (z : SpaceTime) (hz : ∀ i, z ∉ mainCoreRegion s₀ η r N i) :
    mainCoreKernel s₀ η r N K z = 0 := by
  classical
  apply Measure.ext
  intro E hE
  rw [mainCoreKernel,Kernel.sum_apply' _ _ hE]
  simp [Kernel.piecewise_apply',hz]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A retained collision away from the transverse origin has a positive scale -/

noncomputable section

open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem transverse_dilated_origin {r : ℝ} (hr : r ≠ 0) (x : Velocity) (k : Lattice) :
    transverse (r • x)-transverseShift k = r • transverse (x-r⁻¹ • latticeVector k) := by
  apply (WithLp.ext_iff 2).mpr
  funext i
  change r*x i.castSucc-(k i.castSucc : ℝ) = r*(x i.castSucc-r⁻¹*(k i.castSucc : ℝ))
  field_simp

theorem mainCoreRegion_scale_radius {s₀ η r : ℝ} {N : ℕ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : 0 < r)
    {z : Published.SpaceTime} {i : Label} (hi : z ∈ mainCoreRegion s₀ η r N i) :
    JetGeometry.jetScale s₀ η i.annulus/r < ‖transverse (z.2-r⁻¹ • latticeVector i.lattice)‖ ∧
      ‖transverse (z.2-r⁻¹ • latticeVector i.lattice)‖ <
        Real.exp η*(JetGeometry.jetScale s₀ η i.annulus/r) := by
  have hs : 0 < JetGeometry.jetScale s₀ η i.annulus := DatumBounds.scale_pos hs₀ _
  have he := JetGeometry.enlargement_subset_annulus hη hs i.positive hi.2.2.1
  simp only [Set.mem_ofPred_eq] at he
  rw [transverse_dilated_origin hr.ne',norm_smul,Real.norm_eq_abs,abs_of_pos hr] at he
  constructor
  · exact (div_lt_iff₀ hr).mpr (by nlinarith [he.1])
  · have h := (lt_div_iff₀ hr).mpr (show
        ‖transverse (z.2-r⁻¹ • latticeVector i.lattice)‖*r <
          Real.exp η*JetGeometry.jetScale s₀ η i.annulus by nlinarith [he.2])
    simpa only [mul_div_assoc] using h

theorem mainCoreRegion_retained_scale_window {s₀ η r ρ R : ℝ} {N : ℕ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : 0 < r)
    {z : Published.SpaceTime} {i : Label} (hi : z ∈ mainCoreRegion s₀ η r N i)
    (hlow : ρ ≤ ‖transverse (z.2-r⁻¹ • latticeVector i.lattice)‖)
    (hhigh : ‖transverse (z.2-r⁻¹ • latticeVector i.lattice)‖ ≤ R) :
    ρ/Real.exp η < JetGeometry.jetScale s₀ η i.annulus/r ∧
      JetGeometry.jetScale s₀ η i.annulus/r < R := by
  have he := mainCoreRegion_scale_radius hs₀ hη hr hi
  constructor
  · apply (div_lt_iff₀ (Real.exp_pos η)).mpr
    nlinarith [he.2]
  · exact he.1.trans_le hhigh

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
