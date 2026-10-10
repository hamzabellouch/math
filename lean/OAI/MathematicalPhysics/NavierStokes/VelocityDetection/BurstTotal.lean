import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicMildContDiffScalar
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicComparison
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.BurstBlock
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TimeBlocks

namespace OAI

noncomputable section
namespace VelocityDetection.BurstTotal
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open ChartRouting BurstSchedule Periodization SpatialCalculus
variable (A : RoutingData) (ν : ℝ)

theorem localTime_before (hν : 0 ≤ ν) (k : ℕ) {t : ℝ} (ht : t ≤ (k:ℝ)+1) :
    localTime A ν k t ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (duration_pos A ν hν k).le

theorem localTime_after (hν : 0 ≤ ν) (k : ℕ) {t : ℝ} (ht : (k:ℝ)+2 ≤ t) :
    1 ≤ localTime A ν k t := by
  apply (le_div_iff₀ (duration_pos A ν hν k)).mpr
  linarith [duration_small A ν hν k]

def fieldFamily (hν : 0 ≤ ν) : TimeBlocks.Family (n := 2) (E := Coord 2) where
  term := BurstBlock.field A ν
  smooth := BurstBlock.contDiff_field A ν
  before := fun k _ ht => BurstBlock.field_zero A ν k (Or.inl (localTime_before A ν hν k ht))
  after := fun k _ ht => BurstBlock.field_zero A ν k (Or.inr (localTime_after A ν hν k ht))

def sourceFamily (hν : 0 ≤ ν) (q : ℕ) : TimeBlocks.Family (n := 2) (E := ℝ) where
  term := BurstBlock.source A ν q
  smooth := BurstBlock.contDiff_source A ν q
  before := fun k _ ht => BurstBlock.source_zero A ν q k (Or.inl (localTime_before A ν hν k ht))
  after := fun k _ ht => BurstBlock.source_zero A ν q k (Or.inr (localTime_after A ν hν k ht))

def field : VectorField 2 := fun t X => ∑' k : ℕ, BurstBlock.field A ν k t X

def source (q : ℕ) : ScalarField 2 := fun t X => ∑' k : ℕ, BurstBlock.source A ν q k t X

@[fun_prop] theorem contDiff_field (hν : 0 ≤ ν) : ContDiff ℝ ∞ (uncurry (field A ν)) :=
  TimeBlocks.contDiff_total (fieldFamily A ν hν)

@[fun_prop] theorem contDiff_source (hν : 0 ≤ ν) (q : ℕ) : ContDiff ℝ ∞ (uncurry (source A ν q)) :=
  TimeBlocks.contDiff_total (sourceFamily A ν hν q)

theorem field_periodic (hν : 0 ≤ ν) (t : ℝ) : FactorsThrough (field A ν t) PeriodicSpace.cover :=
  TimeBlocks.periodic (fieldFamily A ν hν) (BurstBlock.field_periodic A ν) t

theorem source_periodic (hν : 0 ≤ ν) (q : ℕ) (t : ℝ) :
    FactorsThrough (source A ν q t) PeriodicSpace.cover :=
  TimeBlocks.periodic (sourceFamily A ν hν q) (fun _ t => periodic_extend _ t) t

theorem field_rest (hν : 0 ≤ ν) {t : ℝ} (ht : t ≤ 1) : field A ν t = 0 :=
  TimeBlocks.at_rest (fieldFamily A ν hν) ht

theorem source_rest (hν : 0 ≤ ν) (q : ℕ) {t : ℝ} (ht : t ≤ 1) : source A ν q t = 0 :=
  TimeBlocks.at_rest (sourceFamily A ν hν q) ht

theorem field_divergence (hν : 0 ≤ ν) (t : ℝ) (X : Coord 2) : divergence (field A ν) t X = 0 := by
  obtain ⟨L,hL⟩ := exists_nat_gt t
  have he := TimeBlocks.eq_finite (fieldFamily A ν hν) (L := L) (by linarith : t ≤ (L:ℝ)+1)
  have hr : divergence (field A ν) t X =
      divergence (fun r Y => ∑ k ∈ Finset.range L, BurstBlock.field A ν k r Y) t X := by
    unfold divergence spatialD
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    funext s
    exact congrFun (congrFun he (update X i s)) i
  rw [hr,divergence_sum]
  · exact Finset.sum_eq_zero (fun k _ => BurstBlock.divergence_field A ν k t X)
  · intro k _ s
    exact contDiff_slice (BurstBlock.contDiff_field A ν k) s

theorem field_at_block (hν : 0 ≤ ν) (k : ℕ) {t : ℝ}
    (ht : t ∈ Icc ((k:ℝ)+1) ((k:ℝ)+2)) : field A ν t = BurstBlock.field A ν k t :=
  TimeBlocks.eq_term (fieldFamily A ν hν) k ht

def driftData (hν : 0 ≤ ν) (i : Fin 2) : PeriodicMild.PeriodicData where
  scalar := fun t X => field A ν t X i
  smooth := (contDiff_apply ℝ ℝ i).comp (contDiff_field A ν hν)
  periodic := fun t _ _ h => congrFun (field_periodic A ν hν t h) i

def sourceData (hν : 0 ≤ ν) (q : ℕ) : PeriodicMild.PeriodicData where
  scalar := source A ν q
  smooth := contDiff_source A ν hν q
  periodic := source_periodic A ν hν q

def scalar (hν : 0 < ν) (q : ℕ) : ScalarField 2 :=
  PeriodicMild.scalar hν (driftData A ν hν.le) (sourceData A ν hν.le q)

theorem contDiff_scalar (hν : 0 < ν) (q : ℕ) : ContDiff ℝ ∞ (uncurry (scalar A ν hν q)) := by
  apply PeriodicMild.contDiff_scalar
  intro t ht X
  exact congrFun (source_rest A ν hν.le q (by linarith)) X

theorem scalar_periodic (hν : 0 < ν) (q : ℕ) (t : ℝ) :
    FactorsThrough (scalar A ν hν q t) PeriodicSpace.cover :=
  PeriodicMild.periodic_scalar hν (driftData A ν hν.le) (sourceData A ν hν.le q) t

theorem scalar_initial (hν : 0 < ν) (q : ℕ) (X : Coord 2) : scalar A ν hν q 0 X = 0 :=
  PeriodicMild.scalar_zero hν (driftData A ν hν.le) (sourceData A ν hν.le q) X

theorem scalar_equation (hν : 0 < ν) (q : ℕ) {t : ℝ} (ht : 0 ≤ t) (X : Coord 2) :
    timeD (scalar A ν hν q) t X + advection (field A ν) (scalar A ν hν q) t X =
      ν*laplacian (scalar A ν hν q) t X+source A ν q t X :=
  PeriodicMild.scalar_equation hν (driftData A ν hν.le) (sourceData A ν hν.le q)
    (fun t _ X => field_divergence A ν hν.le t X) ht X

theorem scalar_residual (hν : 0 < ν) (q : ℕ) {t : ℝ} (ht : 0 ≤ t) (X : Coord 2) :
    PeriodicComparison.residual ν (field A ν) (scalar A ν hν q) t X = source A ν q t X := by
  unfold PeriodicComparison.residual
  rw [← JointCalculus.timeD_eq_deriv ht X ((contDiff_scalar A ν hν q).differentiable (by simp) (t,X)),
    scalar_equation A ν hν q ht X]
  ring

end VelocityDetection.BurstTotal
end

end OAI
