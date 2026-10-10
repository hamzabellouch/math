import OAI.Geometry.SurfaceImmersion.Correction.PreparedCorrection
import OAI.Geometry.SurfaceImmersion.Correction.CorrectionScaleControl

namespace OAI

/-! A single adaptive transition, with all admissibility conditions preserved. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open ExactCorrection WeightedEstimates
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance adaptiveFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance adaptiveFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance adaptiveDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance adaptiveDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance adaptiveSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance adaptiveSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
variable {g : SmoothMetric M} {F : M → Space} {d : CorrectionGeometry g F}

namespace PreparedCorrection
variable (c : PreparedCorrection d)

def stageRadius (t : ℝ) (n : ℕ) : ℝ :=
  c.ρ/8+c.ρ*(∑ i ∈ Finset.range n, correctionScale t i)

structure Stage (t : ℝ) (n : ℕ) where
  order : ℕ
  map : M → Space
  smooth : ContMDiff planeModel spaceModel ∞ map
  scale_small : correctionScale t n < c.ε order
  input : d.A.InputBound (correctionScale t n) (correctionInputOrder order) c.budget map
    (normalizedTensorDefect g.inner ((correctionScale t n)^(correctionOrder order : ℝ)) map)
  near : d.A.WeightedBound 1 2 (c.stageRadius t n) (map-F)
  metric : ∀ x, ‖d.A.tensorEncode (normalizedTensorDefect g.inner
    ((correctionScale t n)^(correctionOrder order : ℝ)) map) x-
    d.A.tensorEncode g.inner x‖ ≤ c.a/8

namespace Stage
variable {c} {t : ℝ} {n : ℕ}

def defect (s : c.Stage t n) : ∀ p : M, CovariantTwoTensor p :=
  normalizedTensorDefect g.inner ((correctionScale t n)^(correctionOrder s.order : ℝ)) s.map

lemma finiteInput (s : c.Stage t n) (ht : 0 < t) (htsmall : t ≤ 1/32) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ d.A.InputBound (correctionScale t n) m C s.map s.defect := by
  exact d.A.exists_input_bound (correctionScale_pos ht n).le
    ((correctionScale_le_initial ht.le htsmall n).trans (by linarith)) m s.smooth
    (d.A.normalizedTensorDefect_smooth g.contMDiff _ s.smooth)

def size (s : c.Stage t n) (m : ℕ) : ℝ :=
  d.A.inputSize (correctionScale t n) m s.map s.defect

def CanAdvance (s : c.Stage t n) : Prop :=
  correctionScale t n < c.ε (s.order+1) ∧
  c.baseline+c.N s.order (correctionInputOrder (s.order+1))*
    (correctionScale t n)^(1/5 : ℝ)*(1+s.size (correctionInputOrder (s.order+1))) ≤ c.budget

end Stage

structure Transition {t : ℝ} {n : ℕ} (s : c.Stage t n) where
  next : c.Stage t (n+1)
  increment : M → Space
  smooth : ContMDiff planeModel spaceModel ∞ increment
  map_eq : next.map = s.map+increment
  order_eq : next.order = if s.CanAdvance then s.order+1 else s.order
  small : ∀ m ≤ correctionOrder s.order/2,
    d.A.WeightedBound 1 m (c.ρ*correctionScale t n) increment
  recurrence : ∀ m C, 0 ≤ C →
    d.A.InputBound (correctionScale t n) m C s.map s.defect →
    d.A.InputBound (correctionScale t (n+1)) m
      (c.baseline+c.N s.order m*(correctionScale t n)^(1/5 : ℝ)*(1+C)) next.map next.defect

/-- At every stage the order can be held. It is increased as soon as the next
finite input bound and the next geometric threshold permit it. -/
theorem transition_nonempty (hF : ContMDiff planeModel spaceModel ∞ F)
    {t : ℝ} (ht : 0 < t) (htsmall : t ≤ 1/32) {n : ℕ} (s : c.Stage t n) :
    Nonempty (c.Transition s) := by
  classical
  let k := if s.CanAdvance then s.order+1 else s.order
  have hk : s.order ≤ k ∧ k ≤ s.order+1 := by dsimp [k]; split_ifs <;> omega
  have htime := correctionScale_pos ht n
  have htime1 : correctionScale t n ≤ 1 :=
    (correctionScale_le_initial ht.le htsmall n).trans (by linarith)
  have hnext : correctionScale t (n+1) ≤ correctionScale t n := by
    exact (scale_step_le_half htime.le
      ((correctionScale_le_initial ht.le htsmall n).trans htsmall)).trans (by linarith)
  have hnear : d.A.WeightedBound 1 2 (c.ρ/4) (s.map-F) := by
    intro i
    exact (s.near i).mono_const (correction_displacement_budget ht.le htsmall c.ρ_pos.le n)
  obtain ⟨U,hU,hsmall,herror,hinput⟩ := c.step s.order s.map s.smooth
    (correctionScale t n) htime s.scale_small (correctionOrder k)
    (by unfold correctionOrder; omega) (by unfold correctionOrder; omega)
    s.input hnear s.metric
  have he : (correctionScale t n)^((6/5 : ℝ)*(correctionOrder k : ℝ)) =
      (correctionScale t (n+1))^(correctionOrder k : ℝ) := by
    rw [correctionScale,← Real.rpow_mul htime.le]
  have hε : correctionScale t (n+1) < c.ε k := by
    dsimp [k]
    split_ifs with h
    · exact hnext.trans_lt h.1
    · exact hnext.trans_lt s.scale_small
  have hin : d.A.InputBound (correctionScale t (n+1)) (correctionInputOrder k)
      c.budget (s.map+U)
      (normalizedTensorDefect g.inner
        ((correctionScale t (n+1))^(correctionOrder k : ℝ)) (s.map+U)) := by
    by_cases hadv : s.CanAdvance
    · have hk' : k = s.order+1 := ite_eq_left hadv
      obtain ⟨C,hC,hCb⟩ := s.finiteInput ht htsmall (correctionInputOrder (s.order+1))
      have hsize := d.A.inputSize_bound ⟨C,hC,hCb⟩
      have hnsize := d.A.inputSize_nonneg ⟨C,hC,hCb⟩
      have hh := hinput (correctionInputOrder (s.order+1)) _ hnsize hsize
      rw [he] at hh
      rw [hk'] at hh ⊢
      exact d.A.inputBound_mono_const hh hadv.2
    · have hk' : k = s.order := ite_eq_right hadv
      have hh := hinput (correctionInputOrder s.order) c.budget c.budget_pos.le s.input
      rw [he] at hh
      rw [hk'] at hh ⊢
      exact d.A.inputBound_mono_const hh (c.preserve s.order _ htime s.scale_small).1
  have hmet : ∀ x, ‖d.A.tensorEncode (normalizedTensorDefect g.inner
      ((correctionScale t (n+1))^(correctionOrder k : ℝ)) (s.map+U)) x-
      d.A.tensorEncode g.inner x‖ ≤ c.a/8 := by
    have hL := c.L_nonneg s.order
    have hB := c.budget_pos
    have hb := d.A.tensorEncode_bound
      ((d.A.normalizedTensorDefect_smooth g.contMDiff _ (s.smooth.add hU)).sub_section g.contMDiff)
      (Real.rpow_pos_of_pos htime _) (by positivity) herror
    intro x
    have hh := hb.norm_le (mem_univ x)
    rw [he] at hh
    simpa only [d.A.tensorEncode_sub,Pi.sub_apply] using
      hh.trans (c.preserve s.order _ htime s.scale_small).2
  have hmap : d.A.WeightedBound 1 2 (c.stageRadius t (n+1)) (s.map+U-F) := by
    have hu := hsmall 2 (by unfold correctionOrder; omega)
    have hb := d.A.weightedBound_add (s.smooth.sub hF) hU zero_le_one s.near hu
    have heq : s.map+U-F = (s.map-F)+U := by abel
    rw [heq]
    convert hb using 1
    simp only [stageRadius,Finset.sum_range_succ]
    ring
  refine ⟨⟨⟨k,s.map+U,s.smooth.add hU,hε,hin,hmap,hmet⟩,U,hU,rfl,rfl,hsmall,?_⟩⟩
  intro m C hC hb
  have hh := hinput m C hC hb
  rw [he] at hh
  exact hh

end PreparedCorrection
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
