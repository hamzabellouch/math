import OAI.Analysis.KadisonKastler.NonsingularBoundary
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Topology.ContinuousMap.Bounded.Normed

namespace OAI

/-! # The scalar boundary mean on actual L-infinity classes

The source is the bounded family of L-infinity sections indexed by the
countable discrete group. Multiplication and nonsingular pullback are
defined on the actual almost-everywhere classes. The scalar
conditional-expectation property includes the module and action identities.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {D : Type*} [MeasurableSpace D] {μ : Measure D}

abbrev ScalarLInfinity (μ : Measure D) := Lp ℂ ⊤ μ

/-- Constant scalar functions as actual L-infinity classes. -/
def scalarInfinityConst (μ : Measure D) (z : ℂ) : ScalarLInfinity μ :=
  (memLp_top_const z).toLp (fun _ => z)

theorem scalarInfinityConst_ae (z : ℂ) :
    scalarInfinityConst μ z =ᵐ[μ] fun _ => z := MemLp.coeFn_toLp _

/-- The essential norm bounds any representative almost everywhere. -/
theorem scalarInfinity_ae_norm_le (f : ScalarLInfinity μ) :
    ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖f‖ := by
  simpa only [← Lp.norm_def, ← toReal_eLpNorm] using
    ae_le_lpNorm_exponent_top (Lp.memLp f)

/-- Pointwise multiplication descends to L-infinity classes. -/
def scalarInfinityMul (f g : ScalarLInfinity μ) : ScalarLInfinity μ :=
  ((Lp.memLp f).mul (Lp.memLp g)).toLp (fun x => f x * g x)

theorem scalarInfinityMul_ae (f g : ScalarLInfinity μ) :
    scalarInfinityMul f g =ᵐ[μ] fun x => f x * g x := MemLp.coeFn_toLp _

theorem norm_scalarInfinityMul_le (f g : ScalarLInfinity μ) :
    ‖scalarInfinityMul f g‖ ≤ ‖f‖ * ‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [scalarInfinityMul_ae f g, scalarInfinity_ae_norm_le f] with x hfg hf
  rw [hfg, norm_mul]
  exact mul_le_mul_of_nonneg_right hf (norm_nonneg _)

theorem scalarInfinityMul_add_left (f g h : ScalarLInfinity μ) :
    scalarInfinityMul (f + g) h = scalarInfinityMul f h + scalarInfinityMul g h := by
  apply Lp.ext
  filter_upwards [scalarInfinityMul_ae (f + g) h, scalarInfinityMul_ae f h,
    scalarInfinityMul_ae g h, Lp.coeFn_add f g,
    Lp.coeFn_add (scalarInfinityMul f h) (scalarInfinityMul g h)] with x ha hb hc hd he
  simp only [Pi.add_apply] at hd he
  rw [ha, hd, he, hb, hc, add_mul]

theorem scalarInfinityMul_smul_left (c : ℂ) (f g : ScalarLInfinity μ) :
    scalarInfinityMul (c • f) g = c • scalarInfinityMul f g := by
  apply Lp.ext
  filter_upwards [scalarInfinityMul_ae (c • f) g, scalarInfinityMul_ae f g,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (scalarInfinityMul f g)] with x ha hb hc hd
  simp only [Pi.smul_apply] at hc hd
  rw [ha, hc, hd, hb, smul_mul_assoc]

theorem scalarInfinityMul_comm (f g : ScalarLInfinity μ) :
    scalarInfinityMul f g = scalarInfinityMul g f := by
  apply Lp.ext
  filter_upwards [scalarInfinityMul_ae f g, scalarInfinityMul_ae g f] with x hf hg
  rw [hf, hg, mul_comm]

theorem scalarInfinityMul_const_one (f : ScalarLInfinity μ) :
    scalarInfinityMul (scalarInfinityConst μ 1) f = f := by
  apply Lp.ext
  filter_upwards [scalarInfinityMul_ae (scalarInfinityConst μ 1) f,
    scalarInfinityConst_ae (μ := μ) 1] with x hm h1
  rw [hm, h1, one_mul]

section Pullback

variable [IsFiniteMeasure μ] {E : Type*} [MeasurableSpace E]
  {ν : Measure E} [IsFiniteMeasure ν]

omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
/-- Nonsingular pullback preserves essential boundedness. -/
theorem memLp_scalarInfinity_comp (f : ScalarLInfinity ν) (T : D → E)
    (hT : Measure.QuasiMeasurePreserving T μ ν) : MemLp (fun x => f (T x)) ⊤ μ :=
  memLp_top_of_bound ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving hT)
    ‖f‖ (hT.ae (scalarInfinity_ae_norm_le f))

def scalarInfinityPullback (T : D → E) (hT : Measure.QuasiMeasurePreserving T μ ν)
    (f : ScalarLInfinity ν) : ScalarLInfinity μ :=
  (memLp_scalarInfinity_comp f T hT).toLp (fun x => f (T x))

omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
theorem scalarInfinityPullback_ae (T : D → E)
    (hT : Measure.QuasiMeasurePreserving T μ ν) (f : ScalarLInfinity ν) :
    scalarInfinityPullback T hT f =ᵐ[μ] fun x => f (T x) := MemLp.coeFn_toLp _

omit [IsFiniteMeasure ν] in
theorem norm_scalarInfinityPullback_le (T : D → E)
    (hT : Measure.QuasiMeasurePreserving T μ ν) (f : ScalarLInfinity ν) :
    ‖scalarInfinityPullback T hT f‖ ≤ ‖f‖ := by
  have hb : ∀ᵐ x ∂μ, ‖scalarInfinityPullback T hT f x‖ ≤ ‖f‖ := by
    filter_upwards [scalarInfinityPullback_ae T hT f,
      hT.ae (scalarInfinity_ae_norm_le f)] with x hx hb
    rwa [hx]
  simpa using Lp.norm_le_of_ae_bound (norm_nonneg f) hb

def scalarInfinityPullbackL (T : D → E) (hT : Measure.QuasiMeasurePreserving T μ ν) :
    ScalarLInfinity ν →L[ℂ] ScalarLInfinity μ :=
  LinearMap.mkContinuous
    { toFun := scalarInfinityPullback T hT
      map_add' f g := by
        apply Lp.ext
        filter_upwards [scalarInfinityPullback_ae T hT (f + g),
          scalarInfinityPullback_ae T hT f, scalarInfinityPullback_ae T hT g,
          hT.ae (Lp.coeFn_add f g),
          Lp.coeFn_add (scalarInfinityPullback T hT f) (scalarInfinityPullback T hT g)]
          with x ha hb hc hd he
        simp only [Pi.add_apply] at hd he
        rw [ha, he, hb, hc, hd]
      map_smul' c f := by
        simp only [RingHom.id_apply]
        apply Lp.ext
        filter_upwards [scalarInfinityPullback_ae T hT (c • f),
          scalarInfinityPullback_ae T hT f, hT.ae (Lp.coeFn_smul c f),
          Lp.coeFn_smul c (scalarInfinityPullback T hT f)] with x ha hb hc hd
        simp only [Pi.smul_apply] at hc hd
        rw [ha, hd, hb, hc] }
    1 (fun f => by simpa using norm_scalarInfinityPullback_le T hT f)

end Pullback

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable [IsFiniteMeasure μ]

/-- The scalar module action on a bounded family of L-infinity sections. -/
def scalarBoundaryModule (b : ScalarLInfinity μ) (F : G →ᵇ ScalarLInfinity μ) :
    G →ᵇ ScalarLInfinity μ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun t => scalarInfinityMul b (F t)) (‖b‖ * ‖F‖) (fun t =>
      (norm_scalarInfinityMul_le b (F t)).trans
        (mul_le_mul_of_nonneg_left (F.norm_coe_le_norm t) (norm_nonneg b)))

/-- Simultaneous inverse translation of the group and boundary coordinates. -/
def scalarBoundaryTranslate (α : NonsingularAction G D μ) (g : G)
    (F : G →ᵇ ScalarLInfinity μ) : G →ᵇ ScalarLInfinity μ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun t => scalarInfinityPullback (α.toPerm g⁻¹) (α.quasi g⁻¹) (F (g⁻¹ * t)))
    ‖F‖ (fun _t => (norm_scalarInfinityPullback_le _ _ _).trans (F.norm_coe_le_norm _))

/-- Scalar equivariant conditional expectation in the section model of
L-infinity(G × D). These are the exact structural scalar conclusions
of Adams–Elliott–Giordano, Theorem 3.4; existence is not asserted here. -/
structure ScalarBoundaryMean (α : NonsingularAction G D μ) where
  toCLM : (G →ᵇ ScalarLInfinity μ) →L[ℂ] ScalarLInfinity μ
  map_one : toCLM (BoundedContinuousFunction.const G (scalarInfinityConst μ 1)) =
    scalarInfinityConst μ 1
  norm_le : ∀ F, ‖toCLM F‖ ≤ ‖F‖
  positive : ∀ F, (∀ g, ∀ᵐ x ∂μ, (F g x).im = 0 ∧ 0 ≤ (F g x).re) →
    ∀ᵐ x ∂μ, (toCLM F x).im = 0 ∧ 0 ≤ (toCLM F x).re
  module_map : ∀ b F, toCLM (scalarBoundaryModule b F) = scalarInfinityMul b (toCLM F)
  equivariant : ∀ g F, toCLM (scalarBoundaryTranslate α g F) =
    scalarInfinityPullback (α.toPerm g⁻¹) (α.quasi g⁻¹) (toCLM F)


omit [Group G] [IsFiniteMeasure μ] in
/-- Multiplying the constant-one family recovers the constant family. -/
theorem scalarBoundaryModule_const_one (b : ScalarLInfinity μ) :
    scalarBoundaryModule b (BoundedContinuousFunction.const G (scalarInfinityConst μ 1)) =
      BoundedContinuousFunction.const G b := by
  apply BoundedContinuousFunction.ext
  intro t
  change scalarInfinityMul b (scalarInfinityConst μ 1) = b
  rw [scalarInfinityMul_comm, scalarInfinityMul_const_one]

/-- The scalar conditional expectation fixes all boundary sections. -/
theorem ScalarBoundaryMean.fixed {α : NonsingularAction G D μ}
    (m : ScalarBoundaryMean α) (b : ScalarLInfinity μ) :
    m.toCLM (BoundedContinuousFunction.const G b) = b := by
  have h := m.module_map b (BoundedContinuousFunction.const G (scalarInfinityConst μ 1))
  rw [scalarBoundaryModule_const_one, m.map_one, scalarInfinityMul_comm,
    scalarInfinityMul_const_one] at h
  exact h

end

end KadisonKastler

end OAI
