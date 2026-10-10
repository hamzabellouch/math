import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingDuhamelLinear
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingDuhamelContinuity
import Mathlib.Topology.CompactOpen

namespace OAI

/-! # Joint scale and forcing continuity of the finite-slab Duhamel operator

The operator has a uniform finite-slab bound and is strongly continuous in
the starting radius.  These two properties give joint continuity in the
radius and the forcing path, without operator-norm continuity of the free
Schrödinger propagator.
-/

open Set Filter Topology

namespace DefocusingNLS

theorem continuous_operator_apply_of_uniform_bound
    {P E F : Type*} [TopologicalSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : P → E →L[ℝ] F) (C : ℝ) (hA : ∀ p, ‖A p‖ ≤ C)
    (hstrong : ∀ x : E, Continuous (fun p => A p x)) :
    Continuous (fun z : P × E => A z.1 z.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hzero : Tendsto (fun z : P × E => A z.1 (z.2 - p.2)) (𝓝 p) (𝓝 0) := by
    have hb (z : P × E) : ‖A z.1 (z.2 - p.2)‖ ≤ C * ‖z.2 - p.2‖ :=
      ((A z.1).le_opNorm (z.2 - p.2)).trans
        (mul_le_mul_of_nonneg_right (hA z.1) (norm_nonneg _))
    apply squeeze_zero_norm hb
    have hc : Continuous (fun z : P × E => C * ‖z.2 - p.2‖) :=
      ((continuous_snd.sub continuous_const).norm).const_mul C
    simpa only [sub_self, norm_zero, mul_zero] using (hc.continuousAt (x := p)).tendsto
  have hbase : Tendsto (fun z : P × E => A z.1 p.2) (𝓝 p) (𝓝 (A p.1 p.2)) :=
    ((hstrong p.2).comp continuous_fst).continuousAt.tendsto
  simpa only [ContinuousAt, map_sub, sub_add_cancel, zero_add] using hzero.add hbase

noncomputable def expandingForcingExtension (M : ℝ) (hM : 0 ≤ M)
    (f : C(Icc (0 : ℝ) M, FourierL2)) : ℝ → FourierL2 :=
  fun t => f (projIcc 0 M hM t)

theorem continuous_expandingForcingExtension (M : ℝ) (hM : 0 ≤ M)
    (f : C(Icc (0 : ℝ) M, FourierL2)) :
    Continuous (expandingForcingExtension M hM f) := f.continuous.comp continuous_projIcc

noncomputable def expandingDuhamelSlab (a b k L M : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hM : 0 ≤ M) :
    C(Icc (0 : ℝ) M, FourierL2) →L[ℝ] C(Icc (0 : ℝ) M, FourierL2) :=
  LinearMap.mkContinuous
    { toFun := fun f =>
        ⟨fun t => expandingDuhamel a b k L ha hk hL t (expandingForcingExtension M hM f), by
          let p : Icc (0 : ℝ) M → ExpandingFreeParameters :=
            fun t => (⟨L, hL⟩, ⟨t.1, t.2.1⟩)
          have hp : Continuous p :=
            continuous_const.prodMk (continuous_subtype_val.subtype_mk _)
          exact (continuous_expandingDuhamel a b k ha hk _
            (continuous_expandingForcingExtension M hM f)).comp hp⟩
      map_add' := by
        intro f g
        apply ContinuousMap.ext
        intro t
        exact expandingDuhamel_add a b k L ha hk hL t
          (expandingForcingExtension M hM f) (expandingForcingExtension M hM g)
          (continuous_expandingForcingExtension M hM f).continuousOn
          (continuous_expandingForcingExtension M hM g).continuousOn
      map_smul' := by
        intro c f
        apply ContinuousMap.ext
        intro t
        exact expandingDuhamel_real_smul a b k L ha hk hL t c
          (expandingForcingExtension M hM f) }
    M (by
      intro f
      apply (ContinuousMap.norm_le _ (mul_nonneg hM (norm_nonneg f))).2
      intro t
      apply (expandingDuhamel_norm_le_mul a b k L ha hk hL t ‖f‖ t.2.1
        (expandingForcingExtension M hM f)
        (continuous_expandingForcingExtension M hM f).continuousOn
        (fun τ _ => ContinuousMap.norm_coe_le_norm f _)).trans
      exact mul_le_mul_of_nonneg_right t.2.2 (norm_nonneg f))

@[simp] theorem expandingDuhamelSlab_apply (a b k L M : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hM : 0 ≤ M)
    (f : C(Icc (0 : ℝ) M, FourierL2)) (t : Icc (0 : ℝ) M) :
    expandingDuhamelSlab a b k L M ha hk hL hM f t =
      expandingDuhamel a b k L ha hk hL t (expandingForcingExtension M hM f) := rfl

theorem expandingDuhamelSlab_norm_le (a b k L M : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hM : 0 ≤ M) :
    ‖expandingDuhamelSlab a b k L M ha hk hL hM‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg hM (norm_nonneg f))).2
  intro t
  apply (expandingDuhamel_norm_le_mul a b k L ha hk hL t ‖f‖ t.2.1
    (expandingForcingExtension M hM f)
    (continuous_expandingForcingExtension M hM f).continuousOn
    (fun τ _ => ContinuousMap.norm_coe_le_norm f _)).trans
  exact mul_le_mul_of_nonneg_right t.2.2 (norm_nonneg f)

theorem continuous_expandingDuhamelSlab_strong (a b k M : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hM : 0 ≤ M)
    (f : C(Icc (0 : ℝ) M, FourierL2)) :
    Continuous (fun L : {L : ℝ // 1 ≤ L} => expandingDuhamelSlab a b k L.1 M ha hk L.2 hM f) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  let p : {L : ℝ // 1 ≤ L} × Icc (0 : ℝ) M → ExpandingFreeParameters :=
    fun z => (z.1, ⟨z.2.1, z.2.2.1⟩)
  have hp : Continuous p :=
    continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  exact (continuous_expandingDuhamel a b k ha hk _
    (continuous_expandingForcingExtension M hM f)).comp hp

theorem continuous_expandingDuhamelSlab (a b k M : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hM : 0 ≤ M) :
    Continuous (fun p : {L : ℝ // 1 ≤ L} × C(Icc (0 : ℝ) M, FourierL2) =>
      expandingDuhamelSlab a b k p.1.1 M ha hk p.1.2 hM p.2) :=
  continuous_operator_apply_of_uniform_bound
    (fun L : {L : ℝ // 1 ≤ L} => expandingDuhamelSlab a b k L.1 M ha hk L.2 hM) M
    (fun L => expandingDuhamelSlab_norm_le a b k L.1 M ha hk L.2 hM)
    (continuous_expandingDuhamelSlab_strong a b k M ha hk hM)

end DefocusingNLS

end OAI
