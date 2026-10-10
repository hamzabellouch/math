import OAI.Dynamics.TriangleBilliards.Koopman

namespace OAI

universe uH

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section

/-! Strongly continuous unitary dynamics and the closed generator graph.
All hypotheses here are structural flow properties; the billiard instance
is constructed from its geometric flow, not postulated. -/

open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section

namespace TriangularBilliards.Analysis

variable (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

structure HilbertFlow where
  act : ℝ → H →ₗᵢ[ℂ] H
  zero : ∀ u, act 0 u = u
  add : ∀ s t u, act (s + t) u = act s (act t u)
  continuous : ∀ u, Continuous (fun t => act t u)

namespace HilbertFlow

variable {H} (W : HilbertFlow H)

@[simp] lemma act_zero (u : H) : W.act 0 u = u := W.zero u

lemma act_neg (t : ℝ) (u : H) : W.act (-t) (W.act t u) = u := by
  rw [← W.add, neg_add_cancel, W.zero]

lemma inner_act (t : ℝ) (u v : H) : inner ℂ (W.act t u) (W.act t v) = inner ℂ u v :=
  (W.act t).inner_map_map u v

lemma continuous_joint : Continuous (fun tu : ℝ × H => W.act tu.1 tu.2) := by
  have h : Continuous (fun ut : H × ℝ => W.act ut.2 ut.1) :=
    continuous_prod_of_continuous_lipschitzWith _ 1 W.continuous
      (fun t => (W.act t).isometry.lipschitzWith)
  exact h.comp continuous_swap

/-- Conjugating by a second genuine unitary flow preserves all structural
properties. For billiards the second flow is angular rotation. -/
def conjugate (V : HilbertFlow H) (θ : ℝ) : HilbertFlow H where
  act t := (V.act θ).comp ((W.act t).comp (V.act (-θ)))
  zero u := by
    change V.act θ (W.act 0 (V.act (-θ) u)) = u
    rw [W.zero, ← V.add, add_neg_cancel, V.zero]
  add s t u := by
    change V.act θ (W.act (s + t) (V.act (-θ) u)) =
      V.act θ (W.act s (V.act (-θ) (V.act θ (W.act t (V.act (-θ) u)))))
    rw [← V.add, neg_add_cancel, V.zero, W.add]
  continuous u := (V.act θ).continuous.comp (W.continuous (V.act (-θ) u))

lemma conjugate_joint (V : HilbertFlow H) :
    Continuous (fun p : ℝ × ℝ × H => (W.conjugate V p.1).act p.2.1 p.2.2) := by
  change Continuous (fun p : ℝ × ℝ × H => V.act p.1 (W.act p.2.1 (V.act (-p.1) p.2.2)))
  exact V.continuous_joint.comp (continuous_fst.prodMk
    (W.continuous_joint.comp (continuous_snd.fst.prodMk
      (V.continuous_joint.comp (continuous_fst.neg.prodMk continuous_snd.snd)))))

variable [CompleteSpace H]

omit [CompleteSpace H] in
lemma intervalIntegrable (u : H) (a b : ℝ) :
    IntervalIntegrable (fun t => W.act t u) volume a b :=
  (W.continuous u).intervalIntegrable _ _

/-- Integration in time, as a genuine bounded linear operator. No
operator-norm continuity of the unitary group is presupposed. -/
def timeIntegral (a b : ℝ) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun u => ∫ t in a..b, W.act t u
      map_add' := fun u v => by
        simp only [map_add]
        exact intervalIntegral.integral_add (W.intervalIntegrable u a b) (W.intervalIntegrable v a b)
      map_smul' := fun r u => by
        simp only [map_smul, RingHom.id_apply]
        exact intervalIntegral.integral_smul r (fun t => W.act t u) }
    |b - a|
    (fun u => by
      calc
        ‖∫ t in a..b, W.act t u‖ ≤ ‖u‖ * |b - a| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => (W.act t).norm_map u |>.le)
        _ = |b - a| * ‖u‖ := mul_comm _ _)

omit [CompleteSpace H] in
@[simp] lemma timeIntegral_apply (a b : ℝ) (u : H) :
    W.timeIntegral a b u = ∫ t in a..b, W.act t u := rfl

/-- The generator domain encoded by the exact orbit integral identity.
This formulation makes weak closedness an immediate linear-test fact. -/
def HasGenerator (u v : H) : Prop :=
  ∀ t : ℝ, W.act t u - u = W.timeIntegral 0 t v

lemma HasGenerator.hasDerivAt {u v : H} (h : W.HasGenerator u v) (t : ℝ) :
    HasDerivAt (fun s => W.act s u) (W.act t v) t := by
  have hi := W.intervalIntegrable v 0 t
  have hd := intervalIntegral.integral_hasDerivAt_right hi
    (W.continuous v).stronglyMeasurable.stronglyMeasurableAtFilter (W.continuous v).continuousAt
  have he : (fun s => W.act s u) = (fun s => u + ∫ r in 0..s, W.act r v) := by
    funext s
    have hh := h s
    change W.act s u - u = ∫ r in 0..s, W.act r v at hh
    exact eq_add_of_sub_eq' hh
  rw [he]
  exact hd.const_add u

lemma hasGenerator_of_hasDerivAt {u v : H}
    (h : ∀ t, HasDerivAt (fun s => W.act s u) (W.act t v) t) : W.HasGenerator u v := by
  intro t
  rw [timeIntegral_apply, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => h s) (W.intervalIntegrable v 0 t), W.zero]

lemma generator_unique {u v v' : H} (h : W.HasGenerator u v) (h' : W.HasGenerator u v') :
    v = v' := by
  have he := (HasGenerator.hasDerivAt W h 0).unique (HasGenerator.hasDerivAt W h' 0)
  simpa only [W.zero] using he

lemma generator_skew {u v a b : H} (hu : W.HasGenerator u a) (hv : W.HasGenerator v b) :
    inner ℂ u b + inner ℂ a v = 0 := by
  have hd := (HasGenerator.hasDerivAt W hu 0).inner ℂ (HasGenerator.hasDerivAt W hv 0)
  have heq : (fun t => inner ℂ (W.act t u) (W.act t v)) = (fun _ : ℝ => inner ℂ u v) :=
    funext fun t => W.inner_act t u v
  rw [heq] at hd
  simpa only [W.zero] using hd.unique (hasDerivAt_const 0 (inner ℂ u v))

omit [CompleteSpace H] in
lemma generatorGraph_closed : IsClosed {p : H × H | W.HasGenerator p.1 p.2} := by
  have he : {p : H × H | W.HasGenerator p.1 p.2} =
      ⋂ t : ℝ, {p : H × H | W.act t p.1 - p.1 = W.timeIntegral 0 t p.2} := by
    ext p
    simp only [HasGenerator, mem_ofPred_eq, mem_iInter]
  rw [he]
  exact isClosed_iInter fun t => isClosed_eq
    (((W.act t).continuous.comp continuous_fst).sub continuous_fst)
    ((W.timeIntegral 0 t).continuous.comp continuous_snd)

omit [CompleteSpace H] in
lemma generatorGraph_convex : Convex ℝ {p : H × H | W.HasGenerator p.1 p.2} := by
  intro p hp q hq a b _ _ _ t
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    map_add]
  change ((W.act t).toLinearMap (a • p.1) + (W.act t).toLinearMap (b • q.1)) -
    (a • p.1 + b • q.1) = W.timeIntegral 0 t (a • p.2) + W.timeIntegral 0 t (b • q.2)
  rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
    ContinuousLinearMap.map_smul_of_tower, ContinuousLinearMap.map_smul_of_tower]
  rw [add_sub_add_comm, ← smul_sub, ← smul_sub]
  change a • (W.act t p.1 - p.1) + b • (W.act t q.1 - q.1) = _
  rw [hp t, hq t]

lemma timeIntegral_translate (a b τ : ℝ) (u : H) :
    W.act τ (W.timeIntegral a b u) = W.timeIntegral (τ + a) (τ + b) u := by
  simp only [timeIntegral_apply]
  rw [← (W.act τ).intervalIntegral_comp_comm]
  have he : (fun t => W.act τ (W.act t u)) = (fun t => W.act (τ + t) u) :=
    funext fun t => (W.add τ t u).symm
  rw [he]
  exact intervalIntegral.integral_comp_add_left (fun t => W.act t u) τ

/-- The finite negative-time average. -/
def negativeAverage (T : ℝ) : H →L[ℂ] H := (T⁻¹ : ℝ) • W.timeIntegral (-T) 0

omit [CompleteSpace H] in
lemma negativeAverage_eq (T : ℝ) (u : H) :
    W.negativeAverage T u = (T⁻¹ : ℝ) • ∫ t in 0..T, W.act (-t) u := by
  change (T⁻¹ : ℝ) • (∫ t in -T..0, W.act t u) =
    (T⁻¹ : ℝ) • ∫ t in 0..T, W.act (-t) u
  rw [intervalIntegral.integral_comp_neg (fun t => W.act t u)]
  simp only [neg_zero]

omit [CompleteSpace H] in
lemma negativeAverage_norm_le {T : ℝ} (hT : 0 < T) (u : H) :
    ‖W.negativeAverage T u‖ ≤ ‖u‖ := by
  rw [negativeAverage_eq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hT)]
  calc
    T⁻¹ * ‖∫ t in 0..T, W.act (-t) u‖ ≤ T⁻¹ * (‖u‖ * T) := by
      gcongr
      simpa only [sub_zero, abs_of_pos hT] using
        intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun t => W.act (-t) u) (a := 0) (b := T)
          (fun t _ => (W.act (-t)).norm_map u |>.le)
    _ = ‖u‖ := by field_simp

lemma timeIntegral_hasDerivAt_right (u : H) (a t : ℝ) :
    HasDerivAt (fun s => W.timeIntegral a s u) (W.act t u) t := by
  exact intervalIntegral.integral_hasDerivAt_right (W.intervalIntegrable u a t)
    (W.continuous u).stronglyMeasurable.stronglyMeasurableAtFilter (W.continuous u).continuousAt

lemma timeIntegral_hasDerivAt_translate (u : H) (a b t : ℝ) :
    HasDerivAt (fun s => W.timeIntegral (s + a) (s + b) u)
      (W.act (t + b) u - W.act (t + a) u) t := by
  have hb := (W.timeIntegral_hasDerivAt_right u 0 (t + b)).scomp t
    ((hasDerivAt_id t).add_const b)
  have ha := (W.timeIntegral_hasDerivAt_right u 0 (t + a)).scomp t
    ((hasDerivAt_id t).add_const a)
  have he : (fun s => W.timeIntegral (s + a) (s + b) u) =
      (fun s => W.timeIntegral 0 (s + b) u - W.timeIntegral 0 (s + a) u) := by
    funext s
    exact (intervalIntegral.integral_interval_sub_left
      (W.intervalIntegrable u 0 (s + b)) (W.intervalIntegrable u 0 (s + a))).symm
  rw [he]
  convert hb.sub ha using 1 <;> simp only [Function.comp_def, one_smul, id_eq, Pi.sub_def]

lemma negativeAverage_generator (T : ℝ) (u : H) :
    W.HasGenerator (W.negativeAverage T u) ((T⁻¹ : ℝ) • (u - W.act (-T) u)) := by
  apply W.hasGenerator_of_hasDerivAt
  intro t
  have he : (fun s => W.act s (W.negativeAverage T u)) =
      (fun s => (T⁻¹ : ℝ) • W.timeIntegral (s + -T) (s + 0) u) := by
    funext s
    change (W.act s).toLinearMap ((T⁻¹ : ℝ) • W.timeIntegral (-T) 0 u) = _
    rw [LinearMap.map_smul_of_tower]
    change (T⁻¹ : ℝ) • W.act s (W.timeIntegral (-T) 0 u) = _
    rw [W.timeIntegral_translate]
  rw [he]
  have hd := (W.timeIntegral_hasDerivAt_translate u (-T) 0 t).const_smul (T⁻¹ : ℝ)
  have hv : W.act t ((T⁻¹ : ℝ) • (u - W.act (-T) u)) =
      (T⁻¹ : ℝ) • (W.act (t + 0) u - W.act (t + -T) u) := by
    change (W.act t).toLinearMap ((T⁻¹ : ℝ) • (u - W.act (-T) u)) = _
    rw [LinearMap.map_smul_of_tower]
    change (T⁻¹ : ℝ) • W.act t (u - W.act (-T) u) = _
    rw [map_sub, ← W.add, add_zero]
  rw [hv]
  exact hd

omit [CompleteSpace H] in
lemma negativeAverage_generator_norm {T : ℝ} (hT : 0 < T) (u : H) :
    ‖(T⁻¹ : ℝ) • (u - W.act (-T) u)‖ ≤ 2 * ‖u‖ / T := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hT)]
  calc
    T⁻¹ * ‖u - W.act (-T) u‖ ≤ T⁻¹ * (‖u‖ + ‖W.act (-T) u‖) := by
      gcongr
      exact norm_sub_le _ _
    _ = 2 * ‖u‖ / T := by rw [(W.act (-T)).norm_map]; ring

lemma negativeAverage_invariant {u : H} (hu : ∀ t, W.act t u = u) {T : ℝ} (hT : T ≠ 0) :
    W.negativeAverage T u = u := by
  change (T⁻¹ : ℝ) • (∫ t in -T..0, W.act t u) = u
  simp_rw [hu]
  rw [intervalIntegral.integral_const, ← smul_assoc]
  simp only [sub_neg_eq_add, zero_add, smul_eq_mul, inv_mul_cancel₀ hT, one_smul]

lemma negativeAverage_dist_invariant {u : H} (hu : ∀ t, W.act t u = u)
    {T : ℝ} (hT : 0 < T) (a : H) :
    ‖W.negativeAverage T a - u‖ ≤ ‖a - u‖ := by
  calc
    ‖W.negativeAverage T a - u‖ = ‖W.negativeAverage T (a - u)‖ := by
      rw [map_sub, W.negativeAverage_invariant hu hT.ne']
    _ ≤ ‖a - u‖ := by
      exact W.negativeAverage_norm_le hT (a - u)

end HilbertFlow
end TriangularBilliards.Analysis

end
end
end
end
end

end OAI
