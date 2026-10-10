import Mathlib

namespace OAI

/-! Analytic Support. -/

section

 

noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology

namespace ProjectiveKaehler

 

def compactIntegral {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [OpensMeasurableSpace K] (μ : Measure K) [IsFiniteMeasure μ] :
    C(K, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := by
        intro f g
        exact integral_add
          (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))
          (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g))
      map_smul' := by
        intro c f
        exact integral_smul c f }
    (μ.real univ) (by
      intro f
      change ‖∫ x, f x ∂μ‖ ≤ μ.real univ * ‖f‖
      rw [mul_comm]
      exact norm_integral_le_of_norm_le_const
        (μ := μ) (ae_of_all _ fun x => f.norm_coe_le_norm x))

abbrev Angle := Icc (0 : ℝ) (2 * Real.pi)

def angleMeasure : Measure Angle := Measure.comap Subtype.val volume

instance : IsFiniteMeasure angleMeasure := by
  refine ⟨?_⟩
  rw [angleMeasure, Measure.comap_apply Subtype.val Subtype.val_injective
    (fun s hs => (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image.mpr hs)
    volume MeasurableSet.univ]
  simpa only [Set.image_univ, Subtype.range_coe_subtype, ofPred_mem_eq] using
    (measure_Icc_lt_top (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi))

abbrev Boundary (n : ℕ) := Fin n → Angle

def boundaryCons (n : ℕ) : C(Angle × Boundary n, Boundary (n + 1)) where
  toFun p := Fin.cons p.1 p.2
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using continuous_fst
    · exact (continuous_apply j).comp continuous_snd

 

def integrateFirst {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (L : C(K, ℂ) →L[ℂ] ℂ) : C(Angle × K, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ t, L (f.curry t) ∂angleMeasure
      map_add' := by
        intro f g
        change (∫ t, L ((f + g).curry t) ∂angleMeasure) = _
        have h : ∀ t, (f + g).curry t = f.curry t + g.curry t := fun _ => by
          ext; rfl
        simp_rw [h, map_add]
        apply integral_add
        · exact (L.continuous.comp f.curry.continuous).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        · exact (L.continuous.comp g.curry.continuous).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
      map_smul' := by
        intro c f
        have h : ∀ t, (c • f).curry t = c • f.curry t := fun _ => by
          ext; rfl
        simp_rw [h, map_smul]
        exact integral_smul c _ }
    (‖L‖ * angleMeasure.real univ) (by
      intro f
      calc
        ‖∫ t, L (f.curry t) ∂angleMeasure‖ ≤
            (‖L‖ * ‖f‖) * angleMeasure.real univ :=
          norm_integral_le_of_norm_le_const (ae_of_all _ fun t =>
            (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left
              (((f.curry t).norm_le (norm_nonneg f)).mpr
                (fun y => f.norm_coe_le_norm (t, y))) (norm_nonneg L)))
        _ = (‖L‖ * angleMeasure.real univ) * ‖f‖ := by ring)

 
def boundaryIntegral : (n : ℕ) → C(Boundary n, ℂ) →L[ℂ] ℂ
  | 0 => ContinuousMap.evalCLM ℂ (fun i => Fin.elim0 i)
  | n + 1 => (integrateFirst (boundaryIntegral n)).comp
      (ContinuousMap.compCLM ℂ ℂ (boundaryCons n))

@[simp] theorem boundaryIntegral_zero (f : C(Boundary 0, ℂ)) :
    boundaryIntegral 0 f = f (fun i => Fin.elim0 i) := rfl

@[simp] theorem boundaryIntegral_succ (n : ℕ) (f : C(Boundary (n + 1), ℂ)) :
    boundaryIntegral (n + 1) f =
      ∫ t, boundaryIntegral n ((f.comp (boundaryCons n)).curry t) ∂angleMeasure := rfl

 
def boundaryPoint {n : ℕ} (c : Fin n → ℂ) (R : ℝ) : C(Boundary n, Fin n → ℂ) where
  toFun t i := circleMap (c i) R (t i).val
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact (continuous_circleMap _ _).comp (continuous_subtype_val.comp (continuous_apply i))

 

def denominator {n : ℕ} (c : Fin n → ℂ) (R : ℝ) (i : Fin n)
    (z : Fin n → ℂ) : C(Boundary n, ℂ) :=
  ⟨fun t => circleMap (c i) R (t i).val - z i, by
    exact ((continuous_circleMap _ _).comp
      (continuous_subtype_val.comp (continuous_apply i))).sub continuous_const⟩

lemma analyticAt_denominator {n : ℕ} (c : Fin n → ℂ) (R : ℝ) (i : Fin n)
    (z : Fin n → ℂ) : AnalyticAt ℂ (denominator c R i) z := by
  have h : denominator c R i = fun w => denominator c R i 0 -
      (ContinuousLinearMap.const ℂ (Boundary n)) (w i) := by
    funext w
    ext t
    simp [denominator]
  rw [h]
  have hi : AnalyticAt ℂ (fun w : Fin n → ℂ => w i) z :=
    (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt z
  exact analyticAt_const.sub
    (AnalyticAt.comp (f := fun w : Fin n → ℂ => w i)
      ((ContinuousLinearMap.const ℂ (Boundary n)).analyticAt (z i)) hi)

lemma isUnit_denominator {n : ℕ} {c z : Fin n → ℂ} {R : ℝ} (hR : 0 < R)
    (hz : z ∈ Metric.ball c R) (i : Fin n) : IsUnit (denominator c R i z) := by
  apply (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr
  intro t he
  rw [ball_pi c hR] at hz
  have hi : z i ∈ Metric.ball (c i) R := hz i (Set.mem_univ i)
  have hs := circleMap_mem_sphere (c i) hR.le (t i).val
  have he' : circleMap (c i) R (t i).val = z i := sub_eq_zero.mp he
  rw [he'] at hs
  exact (ne_of_lt hi) hs

lemma analyticAt_inverseDenominator {n : ℕ} {c z : Fin n → ℂ} {R : ℝ}
    (hR : 0 < R) (hz : z ∈ Metric.ball c R) (i : Fin n) :
    AnalyticAt ℂ (fun w => Ring.inverse (denominator c R i w)) z := by
  have h : AnalyticAt ℂ Ring.inverse (denominator c R i z) := by
    simpa only [IsUnit.unit_spec] using
      (analyticAt_inverse (𝕜 := ℂ) (isUnit_denominator hR hz i).unit)
  exact h.comp (analyticAt_denominator c R i z)

lemma inverseDenominator_apply {n : ℕ} {c z : Fin n → ℂ} {R : ℝ}
    (hR : 0 < R) (hz : z ∈ Metric.ball c R) (i : Fin n) (t : Boundary n) :
    Ring.inverse (denominator c R i z) t = (circleMap (c i) R (t i).val - z i)⁻¹ := by
  have h := congrArg (fun F : C(Boundary n, ℂ) => F t)
    (Ring.mul_inverse_cancel (denominator c R i z) (isUnit_denominator hR hz i))
  change (circleMap (c i) R (t i).val - z i) * _ = 1 at h
  exact eq_inv_of_mul_eq_one_right h

lemma boundaryPoint_mem_closedBall {n : ℕ} (c : Fin n → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (t : Boundary n) : boundaryPoint c R t ∈ Metric.closedBall c R := by
  rw [closedBall_pi c hR]
  intro i _
  exact circleMap_mem_closedBall (c i) hR (t i).val

def boundaryValue {n : ℕ} {c : Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R)
    {f : (Fin n → ℂ) → ℂ} (hf : ContinuousOn f (Metric.closedBall c R)) :
    C(Boundary n, ℂ) :=
  ⟨fun t => f (boundaryPoint c R t),
    hf.comp_continuous (boundaryPoint c R).continuous (boundaryPoint_mem_closedBall c hR)⟩

def boundarySpeed {n : ℕ} (R : ℝ) : C(Boundary n, ℂ) :=
  ∏ i : Fin n, ⟨fun t => circleMap 0 R (t i).val * I, by
    exact ((continuous_circleMap 0 R).comp
      (continuous_subtype_val.comp (continuous_apply i))).mul continuous_const⟩

def cauchyTransform {n : ℕ} (c : Fin n → ℂ) (R : ℝ) (F : C(Boundary n, ℂ))
    (z : Fin n → ℂ) : ℂ :=
  boundaryIntegral n (boundarySpeed R * (∏ i, Ring.inverse (denominator c R i z)) * F)

lemma analyticAt_cauchyTransform {n : ℕ} {c z : Fin n → ℂ} {R : ℝ}
    (hR : 0 < R) (hz : z ∈ Metric.ball c R) (F : C(Boundary n, ℂ)) :
    AnalyticAt ℂ (cauchyTransform c R F) z := by
  have hp : AnalyticAt ℂ (fun w => ∏ i, Ring.inverse (denominator c R i w)) z :=
    Finset.analyticAt_fun_prod Finset.univ (fun i _ => analyticAt_inverseDenominator hR hz i)
  have h : AnalyticAt ℂ (fun w => boundarySpeed R *
      (∏ i, Ring.inverse (denominator c R i w)) * F) z :=
    (analyticAt_const.mul hp).mul analyticAt_const
  exact AnalyticAt.comp (f := fun w => boundarySpeed R *
      (∏ i, Ring.inverse (denominator c R i w)) * F)
    ((boundaryIntegral n).analyticAt _) h

abbrev circleKernel (c : ℂ) (R : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (circleMap 0 R t * I) * (circleMap c R t - z)⁻¹

lemma cauchyIntegrand_apply {n : ℕ} {c z : Fin n → ℂ} {R : ℝ}
    (hR : 0 < R) (hz : z ∈ Metric.ball c R) (F : C(Boundary n, ℂ)) (t : Boundary n) :
    (boundarySpeed (n := n) R * (∏ i, Ring.inverse (denominator c R i z)) * F) t =
      (∏ i, circleKernel (c i) R (z i) (t i).val) * F t := by
  simp only [ContinuousMap.mul_apply, boundarySpeed, ContinuousMap.prod_apply,
    ContinuousMap.coe_mk, inverseDenominator_apply hR hz]
  rw [← Finset.prod_mul_distrib]

lemma circleCauchy {c z : ℂ} {R : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.closedBall c R)) (hz : z ∈ Metric.ball c R) :
    (∫ t : Angle, circleKernel c R z t.val * f (circleMap c R t.val) ∂angleMeasure) =
      (2 * Real.pi * I) * f z := by
  have h := hf.circleIntegral_sub_inv_smul hz
  rw [circleIntegral_def_Icc] at h
  rw [angleMeasure, integral_subtype_comap (s := Angle) measurableSet_Icc
    (fun t => circleKernel c R z t * f (circleMap c R t))]
  simpa only [deriv_circleMap, smul_eq_mul, mul_assoc] using h

lemma differentiable_cons_left {n : ℕ} (y : Fin n → ℂ) :
    Differentiable ℂ (fun a : ℂ => (Fin.cons a y : Fin (n + 1) → ℂ)) := by
  apply differentiable_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

lemma differentiable_cons_right {n : ℕ} (a : ℂ) :
    Differentiable ℂ (fun y : Fin n → ℂ => (Fin.cons a y : Fin (n + 1) → ℂ)) := by
  apply differentiable_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · exact (ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).differentiable

lemma cons_mem_closedBall {n : ℕ} {c : Fin (n + 1) → ℂ} {R : ℝ}
    (hR : 0 ≤ R) {a : ℂ} {y : Fin n → ℂ}
    (ha : a ∈ Metric.closedBall (c 0) R)
    (hy : y ∈ Metric.closedBall (Fin.tail c) R) :
    Fin.cons a y ∈ Metric.closedBall c R := by
  rw [closedBall_pi c hR]
  rw [closedBall_pi (Fin.tail c) hR] at hy
  intro i _
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ha
  · exact hy j (Set.mem_univ j)

lemma tail_mem_ball {n : ℕ} {c z : Fin (n + 1) → ℂ} {R : ℝ}
    (hR : 0 < R) (hz : z ∈ Metric.ball c R) :
    Fin.tail z ∈ Metric.ball (Fin.tail c) R := by
  rw [ball_pi c hR] at hz
  rw [ball_pi (Fin.tail c) hR]
  exact fun i _ => hz i.succ (Set.mem_univ _)

lemma boundaryPoint_cons {n : ℕ} (c : Fin (n + 1) → ℂ) (R : ℝ)
    (a : Angle) (t : Boundary n) :
    boundaryPoint c R (Fin.cons a t) =
      Fin.cons (circleMap (c 0) R a.val) (boundaryPoint (Fin.tail c) R t) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

 

lemma boundaryIntegral_cauchy (n : ℕ) {c z : Fin n → ℂ} {R : ℝ}
    {f : (Fin n → ℂ) → ℂ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall c R)) (hz : z ∈ Metric.ball c R)
    (F : C(Boundary n, ℂ))
    (hF : ∀ t, F t = (∏ i, circleKernel (c i) R (z i) (t i).val) *
      f (boundaryPoint c R t)) :
    boundaryIntegral n F = (2 * Real.pi * I) ^ n * f z := by
  induction n with
  | zero =>
    rw [boundaryIntegral_zero, hF]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, pow_zero]
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    have hz0 : z 0 ∈ Metric.ball (c 0) R := by
      rw [ball_pi c hR] at hz
      exact hz 0 (Set.mem_univ _)
    have hzt := tail_mem_ball hR hz
    rw [boundaryIntegral_succ]
    have inner : ∀ a : Angle,
        boundaryIntegral n ((F.comp (boundaryCons n)).curry a) =
          (2 * Real.pi * I) ^ n *
            (circleKernel (c 0) R (z 0) a.val *
              f (Fin.cons (circleMap (c 0) R a.val) (Fin.tail z))) := by
      intro a
      apply ih (c := Fin.tail c) (z := Fin.tail z)
        (f := fun y => circleKernel (c 0) R (z 0) a.val *
          f (Fin.cons (circleMap (c 0) R a.val) y))
      · exact (hf.comp (differentiable_cons_right _).differentiableOn
          (fun y hy => cons_mem_closedBall hR.le
            (circleMap_mem_closedBall (c 0) hR.le a.val) hy)).const_mul _
      · exact hzt
      · intro t
        change F (Fin.cons a t) = _
        rw [hF, Fin.prod_univ_succ, boundaryPoint_cons]
        simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail]
        ring
    simp_rw [inner]
    rw [integral_const_mul]
    have hslice : DifferentiableOn ℂ (fun a => f (Fin.cons a (Fin.tail z)))
        (Metric.closedBall (c 0) R) :=
      hf.comp (differentiable_cons_left _).differentiableOn
        (fun a ha => cons_mem_closedBall hR.le ha (Metric.ball_subset_closedBall hzt))
    rw [circleCauchy hslice hz0, Fin.cons_self_tail, pow_succ]
    ring

lemma cauchyTransform_eq {n : ℕ} {c z : Fin n → ℂ} {R : ℝ}
    {f : (Fin n → ℂ) → ℂ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall c R)) (hz : z ∈ Metric.ball c R) :
    cauchyTransform c R (boundaryValue hR.le hf.continuousOn) z =
      (2 * Real.pi * I) ^ n * f z := by
  apply boundaryIntegral_cauchy n hR hf hz
  intro t
  exact cauchyIntegrand_apply hR hz _ t

lemma analyticAt_of_differentiableOn_closedBall {n : ℕ} {c z : Fin n → ℂ} {R : ℝ}
    {f : (Fin n → ℂ) → ℂ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall c R)) (hz : z ∈ Metric.ball c R) :
    AnalyticAt ℂ f z := by
  have h : AnalyticAt ℂ (fun w => ((2 * Real.pi * I) ^ n)⁻¹ *
      cauchyTransform c R (boundaryValue hR.le hf.continuousOn) w) z :=
    analyticAt_const.mul (analyticAt_cauchyTransform hR hz _)
  apply h.congr
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  rw [cauchyTransform_eq hR hf hw]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n Complex.two_pi_I_ne_zero), one_mul]

 

theorem analyticOnNhd_of_differentiableOn {n : ℕ} {s : Set (Fin n → ℂ)}
    {f : (Fin n → ℂ) → ℂ} (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) :
    AnalyticOnNhd ℂ f s := by
  intro z hz
  obtain ⟨R, hR, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hz)
  exact analyticAt_of_differentiableOn_closedBall hR (hf.mono hsub)
    (Metric.mem_ball_self hR)

 
theorem analyticOnNhd_pi_of_differentiableOn {n m : ℕ} {s : Set (Fin n → ℂ)}
    {f : (Fin n → ℂ) → (Fin m → ℂ)} (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) :
    AnalyticOnNhd ℂ f s := by
  intro z hz
  apply analyticAt_pi_iff.mpr
  intro i
  have hi : DifferentiableOn ℂ (fun w => f w i) s :=
    (ContinuousLinearMap.proj i : (Fin m → ℂ) →L[ℂ] ℂ).differentiable.comp_differentiableOn hf
  exact analyticOnNhd_of_differentiableOn hs hi z hz

theorem contDiffOn_real_pi_of_differentiableOn {n m : ℕ} {s : Set (Fin n → ℂ)}
    {f : (Fin n → ℂ) → (Fin m → ℂ)} (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) :
    ContDiffOn ℝ ⊤ f s := by
  intro z hz
  exact ((analyticOnNhd_pi_of_differentiableOn hs hf z hz).contDiffAt.restrict_scalars ℝ).contDiffWithinAt

end ProjectiveKaehler

 

noncomputable section
open Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise

namespace ProjectiveKaehler

variable {m n : ℕ}

 
def mass (x : Fin m → ℂ) : ℂ := star x ⬝ᵥ x

lemma mass_ne_zero {x : Fin m → ℂ} (hx : x ≠ 0) : mass x ≠ 0 := by
  simpa only [mass, ne_eq, dotProduct_star_self_eq_zero] using hx

lemma mass_pos {x : Fin m → ℂ} (hx : x ≠ 0) : 0 < mass x :=
  lt_of_le_of_ne (dotProduct_star_self_nonneg x) (Ne.symm (mass_ne_zero hx))

@[simp] lemma star_mass (x : Fin m → ℂ) : star (mass x) = mass x := by
  exact (Matrix.star_dotProduct x x).symm

 
def horizontal (x : Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  1 - (mass x)⁻¹ • vecMulVec x (star x)

lemma horizontal_mulVec (x u : Fin m → ℂ) :
    horizontal x *ᵥ u = u - ((mass x)⁻¹ * (star x ⬝ᵥ u)) • x := by
  simp [horizontal, sub_mulVec, smul_mulVec, vecMulVec_mulVec, smul_smul]

lemma horizontal_mulVec_eq_zero_iff (x u : Fin m → ℂ) :
    horizontal x *ᵥ u = 0 ↔ u = ((mass x)⁻¹ * (star x ⬝ᵥ u)) • x := by
  rw [horizontal_mulVec, sub_eq_zero]

lemma horizontal_self {x : Fin m → ℂ} (hx : x ≠ 0) : horizontal x *ᵥ x = 0 := by
  rw [horizontal_mulVec]
  change x - ((mass x)⁻¹ * mass x) • x = 0
  rw [inv_mul_cancel₀ (mass_ne_zero hx), one_smul, sub_self]

lemma horizontal_eq_conjTranspose (x : Fin m → ℂ) : (horizontal x)ᴴ = horizontal x := by
  simp [horizontal, conjTranspose_sub, conjTranspose_smul, conjTranspose_vecMulVec]

lemma horizontal_idempotent {x : Fin m → ℂ} (hx : x ≠ 0) :
    horizontal x * horizontal x = horizontal x := by
  have hu : ∀ u, horizontal x *ᵥ (horizontal x *ᵥ u) = horizontal x *ᵥ u := by
    intro u
    have h := congrArg (horizontal x).mulVec (horizontal_mulVec x u)
    simpa only [mulVec_sub, mulVec_smul, horizontal_self hx, smul_zero, sub_zero] using h
  apply Matrix.ext_of_mulVec_single
  intro j
  simpa only [mulVec_mulVec] using hu (Pi.single j 1)

 

def fsMatrix (x : Fin m → ℂ) (D : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (mass x)⁻¹ • ((horizontal x * D)ᴴ * (horizontal x * D))

lemma fsMatrix_posDef {x : Fin m → ℂ} {D : Matrix (Fin m) (Fin n) ℂ}
    (hx : x ≠ 0) (hD : Function.Injective (horizontal x * D).mulVec) :
    (fsMatrix x D).PosDef := by
  exact (Matrix.PosDef.conjTranspose_mul_self _ hD).smul (inv_pos.mpr (mass_pos hx))

lemma fsMatrix_eq {x : Fin m → ℂ} (hx : x ≠ 0) (D : Matrix (Fin m) (Fin n) ℂ) :
    fsMatrix x D = (mass x)⁻¹ • (Dᴴ * horizontal x * D) := by
  unfold fsMatrix
  congr 1
  rw [conjTranspose_mul, horizontal_eq_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (horizontal x) (horizontal x) D, horizontal_idempotent hx,
    ← Matrix.mul_assoc]

@[simp] lemma mass_smul (a : ℂ) (x : Fin m → ℂ) :
    mass (a • x) = (star a * a) * mass x := by
  simp only [mass, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

lemma horizontal_smul {a : ℂ} (ha : a ≠ 0) {x : Fin m → ℂ} (_hx : x ≠ 0) :
    horizontal (a • x) = horizontal x := by
  unfold horizontal
  rw [mass_smul, star_smul, smul_vecMulVec, vecMulVec_smul, smul_smul, smul_smul]
  congr 2
  have hs : star a ≠ 0 := star_ne_zero.mpr ha
  field_simp

lemma horizontal_gauge {x : Fin m → ℂ} (hx : x ≠ 0) (a : ℂ)
    (D : Matrix (Fin m) (Fin n) ℂ) (r : Fin n → ℂ) :
    horizontal x * (a • D + vecMulVec x r) = a • (horizontal x * D) := by
  rw [Matrix.mul_add, Matrix.mul_smul, mul_vecMulVec, horizontal_self hx]
  simp

 

lemma fsMatrix_gauge {a : ℂ} (ha : a ≠ 0) {x : Fin m → ℂ} (hx : x ≠ 0)
    (D : Matrix (Fin m) (Fin n) ℂ) (r : Fin n → ℂ) :
    fsMatrix (a • x) (a • D + vecMulVec x r) = fsMatrix x D := by
  simp only [fsMatrix, mass_smul, horizontal_smul ha hx, horizontal_gauge hx,
    conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  have hs : star a ≠ 0 := star_ne_zero.mpr ha
  field_simp

lemma fsMatrix_comp {k : ℕ} (x : Fin m → ℂ) (D : Matrix (Fin m) (Fin n) ℂ)
    (L : Matrix (Fin n) (Fin k) ℂ) :
    fsMatrix x (D * L) = Lᴴ * fsMatrix x D * L := by
  simp only [fsMatrix, ← Matrix.mul_assoc (horizontal x) D L, conjTranspose_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [Matrix.mul_assoc]

lemma fsMatrix_pair {x : Fin m → ℂ} (hx : x ≠ 0) (D : Matrix (Fin m) (Fin n) ℂ)
    (u v : Fin n → ℂ) :
    star u ⬝ᵥ (fsMatrix x D *ᵥ v) =
      (mass x)⁻¹ * (star (D *ᵥ u) ⬝ᵥ (D *ᵥ v)) - (mass x)⁻¹ ^ 2 *
        ((star (D *ᵥ u) ⬝ᵥ x) * (star x ⬝ᵥ (D *ᵥ v))) := by
  rw [fsMatrix_eq hx D, smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  rw [horizontal_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  ring

 
def jacobianMatrix (f : (Fin n → ℂ) → (Fin m → ℂ)) (z : Fin n → ℂ) :
    Matrix (Fin m) (Fin n) ℂ := LinearMap.toMatrix' (fderiv ℂ f z).toLinearMap

@[simp] lemma jacobianMatrix_mulVec (f : (Fin n → ℂ) → (Fin m → ℂ))
    (z v : Fin n → ℂ) : jacobianMatrix f z *ᵥ v = fderiv ℂ f z v :=
  LinearMap.toMatrix'_mulVec _ _

lemma normalized_derivative {f : (Fin n → ℂ) → (Fin m → ℂ)} {z : Fin n → ℂ}
    (hf : DifferentiableAt ℂ f z) {a : Fin m} (ha : f z a ≠ 0)
    (v : Fin n → ℂ) (b : Fin m) :
    fderiv ℂ (fun w j => f w j / f w a) z v b =
      (fderiv ℂ f z v b * f z a - f z b * fderiv ℂ f z v a) / (f z a)^2 := by
  have hd (i : Fin m) : HasFDerivAt (fun w => f w i)
      ((ContinuousLinearMap.proj i).comp (fderiv ℂ f z)) z :=
    (ContinuousLinearMap.proj i : (Fin m → ℂ) →L[ℂ] ℂ).hasFDerivAt.comp z hf.hasFDerivAt
  have hdiv (i : Fin m) := (hd i).mul ((hasDerivAt_inv ha).comp_hasFDerivAt z (hd a))
  simp only [Pi.mul_def, Function.comp_def] at hdiv
  simp only [div_eq_mul_inv]
  rw [fderiv_pi (fun i => (hdiv i).differentiableAt)]
  change fderiv ℂ (fun w => f w b * (f w a)⁻¹) z v = _
  rw [(hdiv b).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  field_simp
  ring

 

lemma fsMatrix_posDef_of_immersion {f : (Fin n → ℂ) → (Fin m → ℂ)} {z : Fin n → ℂ}
    (hf : DifferentiableAt ℂ f z) (hx : f z ≠ 0)
    (hImm : ∃ a, f z a ≠ 0 ∧
      Function.Injective (fderiv ℂ (fun w b => f w b / f w a) z)) :
    (fsMatrix (f z) (jacobianMatrix f z)).PosDef := by
  apply fsMatrix_posDef hx
  obtain ⟨a, ha, hImm⟩ := hImm
  have hk : ∀ v, (horizontal (f z) * jacobianMatrix f z) *ᵥ v = 0 → v = 0 := by
    intro v hv
    rw [← mulVec_mulVec, jacobianMatrix_mulVec, horizontal_mulVec_eq_zero_iff] at hv
    have hn : fderiv ℂ (fun w b => f w b / f w a) z v = 0 := by
      ext b
      rw [normalized_derivative hf ha, hv]
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      ring
    apply hImm
    simpa only [map_zero] using hn
  intro u v huv
  apply sub_eq_zero.mp
  apply hk
  rw [mulVec_sub, huv, sub_self]

end ProjectiveKaehler

namespace Anticanonical

abbrev Coordinates (d : ℕ) := Fin d → ℂ

 
def coordinateOverlap {X : Type*} [TopologicalSpace X] {d : ℕ}
    (e e' : OpenPartialHomeomorph X (Coordinates d)) : Set (Coordinates d) :=
  e.target ∩ e.symm ⁻¹' e'.source

 

structure ComplexAtlas (d : ℕ) (X : Type*) [TopologicalSpace X] where
  count : ℕ
  chart : Fin count → OpenPartialHomeomorph X (Coordinates d)
  covers : ∀ x : X, ∃ i, x ∈ (chart i).source
  holomorphic : ∀ i j, DifferentiableOn ℂ ((chart j) ∘ (chart i).symm)
    (coordinateOverlap (chart i) (chart j))

namespace ComplexAtlas

variable {d : ℕ} {X : Type*} [TopologicalSpace X] (A : ComplexAtlas d X)

 
def transition (i j : Fin A.count) : Coordinates d → Coordinates d :=
  A.chart j ∘ (A.chart i).symm

 

def jacobian (i j : Fin A.count) (x : X) : ℂ :=
  Matrix.det (LinearMap.toMatrix'
    (fderiv ℂ (A.transition i j) (A.chart i x)).toLinearMap)

 

structure ProjectiveEmbedding where
  ambientDimension : ℕ
  map : X → Projectivization ℂ (Fin (ambientDimension + 1) → ℂ)
  injective : Function.Injective map
  lift : Fin A.count → Coordinates d → (Fin (ambientDimension + 1) → ℂ)
  holomorphic_lift : ∀ i, DifferentiableOn ℂ (lift i) (A.chart i).target
  lift_ne_zero : ∀ i z, z ∈ (A.chart i).target → lift i z ≠ 0
  represents : ∀ i z (hz : z ∈ (A.chart i).target),
    map ((A.chart i).symm z) = Projectivization.mk ℂ (lift i z) (lift_ne_zero i z hz)
  immersion : ∀ i z, z ∈ (A.chart i).target →
    ∃ a : Fin (ambientDimension + 1), lift i z a ≠ 0 ∧
      Function.Injective (fderiv ℂ (fun w b ↦ lift i w b / lift i w a) z)

end ComplexAtlas
end Anticanonical
namespace Anticanonical.ComplexAtlas

open Filter Topology

variable {d : ℕ} {X : Type*} [TopologicalSpace X] (A : ComplexAtlas d X)

lemma isOpen_coordinateOverlap (i j : Fin A.count) :
    IsOpen (coordinateOverlap (A.chart i) (A.chart j)) :=
  ((A.chart i).symm.trans (A.chart j)).open_source

lemma coordinate_mem_overlap (i j : Fin A.count) {x : X}
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source) :
    A.chart i x ∈ coordinateOverlap (A.chart i) (A.chart j) := by
  refine ⟨(A.chart i).mapsTo hi, ?_⟩
  change (A.chart i).symm (A.chart i x) ∈ (A.chart j).source
  simpa only [(A.chart i).left_inv hi] using hj

lemma transition_at (i j : Fin A.count) {x : X} (hi : x ∈ (A.chart i).source) :
    A.transition i j (A.chart i x) = A.chart j x := by
  simp only [transition, Function.comp_apply, (A.chart i).left_inv hi]

lemma differentiableAt_transition (i j : Fin A.count) {x : X}
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source) :
    DifferentiableAt ℂ (A.transition i j) (A.chart i x) :=
  (A.holomorphic i j).differentiableAt
    ((A.isOpen_coordinateOverlap i j).mem_nhds (A.coordinate_mem_overlap i j hi hj))

end Anticanonical.ComplexAtlas
namespace Anticanonical.ComplexAtlas

open Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise

variable {d : ℕ} {X : Type*} [TopologicalSpace X] (A : ComplexAtlas d X)

def derivativeMatrix (i j : Fin A.count) (x : X) : Matrix (Fin d) (Fin d) ℂ :=
  LinearMap.toMatrix' (fderiv ℂ (A.transition i j) (A.chart i x)).toLinearMap

 

def fundamentalForm (g : Matrix (Fin d) (Fin d) ℂ)
    (u v : Coordinates d) : ℝ :=
  (star u ⬝ᵥ (g *ᵥ v)).im

 

structure KaehlerMetric where
  matrix : Fin A.count → Coordinates d → Matrix (Fin d) (Fin d) ℂ
  smooth : ∀ i, ContDiffOn ℝ ⊤ (matrix i) (A.chart i).target
  positive : ∀ i z, z ∈ (A.chart i).target → (matrix i z).PosDef
  compatibility : ∀ i j x, x ∈ (A.chart i).source → x ∈ (A.chart j).source →
    matrix i (A.chart i x) =
      (A.derivativeMatrix i j x)ᴴ * matrix j (A.chart j x) * A.derivativeMatrix i j x
  closed : ∀ i z, z ∈ (A.chart i).target → ∀ u v w : Coordinates d,
    fderiv ℝ (fun y ↦ fundamentalForm (matrix i y) v w) z u +
      fderiv ℝ (fun y ↦ fundamentalForm (matrix i y) w u) z v +
      fderiv ℝ (fun y ↦ fundamentalForm (matrix i y) u v) z w = 0

end Anticanonical.ComplexAtlas

namespace ProjectiveKaehler
open Set Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise

variable {d m n k : ℕ} {s : Set (Fin d → ℂ)}

lemma smooth_conj {f : (Fin d → ℂ) → ℂ} (hf : ContDiffOn ℝ ⊤ f s) :
    ContDiffOn ℝ ⊤ (fun z => star (f z)) s :=
  Complex.conjCLE.contDiff.comp_contDiffOn hf

lemma smooth_mass {f : (Fin d → ℂ) → (Fin m → ℂ)} (hf : ContDiffOn ℝ ⊤ f s) :
    ContDiffOn ℝ ⊤ (fun z => mass (f z)) s := by
  change ContDiffOn ℝ ⊤ (fun z => ∑ i, star (f z i) * f z i) s
  apply ContDiffOn.sum
  intro i _
  exact (smooth_conj (contDiffOn_pi.mp hf i)).mul (contDiffOn_pi.mp hf i)

lemma smooth_horizontal {f : (Fin d → ℂ) → (Fin m → ℂ)}
    (hf : ContDiffOn ℝ ⊤ f s) (hne : ∀ z ∈ s, f z ≠ 0) :
    ContDiffOn ℝ ⊤ (fun z => horizontal (f z)) s := by
  have hi := (smooth_mass hf).inv fun z hz => mass_ne_zero (hne z hz)
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  exact contDiffOn_const.sub (hi.mul ((contDiffOn_pi.mp hf i).mul
    (smooth_conj (contDiffOn_pi.mp hf j))))

lemma smooth_matrix_mul {F : (Fin d → ℂ) → Matrix (Fin m) (Fin n) ℂ}
    {G : (Fin d → ℂ) → Matrix (Fin n) (Fin k) ℂ}
    (hF : ContDiffOn ℝ ⊤ F s) (hG : ContDiffOn ℝ ⊤ G s) :
    ContDiffOn ℝ ⊤ (fun z => F z * G z) s := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  change ContDiffOn ℝ ⊤ (fun z => ∑ l, F z i l * G z l j) s
  apply ContDiffOn.sum
  intro l _
  exact (contDiffOn_pi.mp (contDiffOn_pi.mp hF i) l).mul
    (contDiffOn_pi.mp (contDiffOn_pi.mp hG l) j)

lemma smooth_conjTranspose {F : (Fin d → ℂ) → Matrix (Fin m) (Fin n) ℂ}
    (hF : ContDiffOn ℝ ⊤ F s) : ContDiffOn ℝ ⊤ (fun z => (F z)ᴴ) s := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  exact smooth_conj (contDiffOn_pi.mp (contDiffOn_pi.mp hF j) i)

lemma smooth_fsMatrix {f : (Fin d → ℂ) → (Fin m → ℂ)}
    {D : (Fin d → ℂ) → Matrix (Fin m) (Fin n) ℂ}
    (hf : ContDiffOn ℝ ⊤ f s) (hD : ContDiffOn ℝ ⊤ D s) (hne : ∀ z ∈ s, f z ≠ 0) :
    ContDiffOn ℝ ⊤ (fun z => fsMatrix (f z) (D z)) s := by
  have hQ := smooth_matrix_mul (smooth_horizontal hf hne) hD
  exact ((smooth_mass hf).inv (fun z hz => mass_ne_zero (hne z hz))).smul
    (smooth_matrix_mul (smooth_conjTranspose hQ) hQ)

lemma smooth_jacobianMatrix {f : (Fin d → ℂ) → (Fin m → ℂ)}
    (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) :
    ContDiffOn ℝ ⊤ (jacobianMatrix f) s := by
  have hd : ContDiffOn ℂ ⊤ (fderiv ℂ f) s :=
    (analyticOnNhd_pi_of_differentiableOn hs hf).fderiv.contDiffOn hs.uniqueDiffOn
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  have hc : ContDiffOn ℂ ⊤ (fun z => fderiv ℂ f z (Pi.single j 1)) s :=
    hd.clm_apply contDiffOn_const
  exact (contDiffOn_pi.mp hc i).restrict_scalars ℝ

end ProjectiveKaehler

namespace Anticanonical.ComplexAtlas
open ProjectiveKaehler
open scoped ComplexOrder Matrix.Norms.Elementwise
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

 
def ProjectiveEmbedding.backgroundMatrix (P : A.ProjectiveEmbedding) (i : Fin A.count)
    (z : Coordinates d) : Matrix (Fin d) (Fin d) ℂ :=
  fsMatrix (P.lift i z) (jacobianMatrix (P.lift i) z)

lemma ProjectiveEmbedding.backgroundMatrix_smooth (P : A.ProjectiveEmbedding) (i : Fin A.count) :
    ContDiffOn ℝ ⊤ (P.backgroundMatrix i) (A.chart i).target := by
  exact smooth_fsMatrix
    (contDiffOn_real_pi_of_differentiableOn (A.chart i).open_target (P.holomorphic_lift i))
    (smooth_jacobianMatrix (A.chart i).open_target (P.holomorphic_lift i))
    (P.lift_ne_zero i)

lemma ProjectiveEmbedding.backgroundMatrix_positive (P : A.ProjectiveEmbedding)
    (i : Fin A.count) {z : Coordinates d} (hz : z ∈ (A.chart i).target) :
    (P.backgroundMatrix i z).PosDef := by
  exact fsMatrix_posDef_of_immersion
    ((P.holomorphic_lift i).differentiableAt ((A.chart i).open_target.mem_nhds hz))
    (P.lift_ne_zero i z hz) (P.immersion i z hz)

end Anticanonical.ComplexAtlas

namespace ProjectiveKaehler
open Filter Topology Matrix
variable {m n k : ℕ}

lemma jacobianMatrix_comp {f : (Fin n → ℂ) → (Fin m → ℂ)}
    {g : (Fin k → ℂ) → (Fin n → ℂ)} {z : Fin k → ℂ}
    (hf : DifferentiableAt ℂ f (g z)) (hg : DifferentiableAt ℂ g z) :
    jacobianMatrix (f ∘ g) z = jacobianMatrix f (g z) * jacobianMatrix g z := by
  unfold jacobianMatrix
  rw [fderiv_comp z hf hg]
  exact LinearMap.toMatrix'_comp _ _

lemma jacobianMatrix_smul {f : (Fin n → ℂ) → (Fin m → ℂ)}
    {c : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hc : DifferentiableAt ℂ c z) (hf : DifferentiableAt ℂ f z) :
    jacobianMatrix (fun w => c w • f w) z = c z • jacobianMatrix f z +
      vecMulVec (f z) (fun j => fderiv ℂ c z (Pi.single j 1)) := by
  change LinearMap.toMatrix' (fderiv ℂ (c • f) z).toLinearMap = _
  rw [fderiv_smul hc hf]
  ext i j
  simp [LinearMap.toMatrix'_apply, jacobianMatrix, vecMulVec, mul_comm]

 

lemma fsMatrix_eq_of_eventually_proportional
    {f g : (Fin n → ℂ) → (Fin m → ℂ)} {z : Fin n → ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z)
    (hfn : f z ≠ 0) (hgn : g z ≠ 0)
    (hp : ∀ᶠ w in 𝓝 z, ∃ c : ℂ, c • g w = f w) :
    fsMatrix (f z) (jacobianMatrix f z) = fsMatrix (g z) (jacobianMatrix g z) := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, g z a ≠ 0 := by
    by_contra h
    push Not at h
    exact hgn (funext h)
  let c : (Fin n → ℂ) → ℂ := fun w => f w a / g w a
  have hd : DifferentiableAt ℂ c z := by
    simpa only [c, div_eq_mul_inv, Pi.mul_def, Pi.inv_def] using
      (differentiableAt_pi.mp hf a).mul ((differentiableAt_pi.mp hg a).inv ha)
  have he : f =ᶠ[𝓝 z] (fun w => c w • g w) := by
    filter_upwards [hp, (differentiableAt_pi.mp hg a).continuousAt.eventually_ne ha] with w hw hwa
    obtain ⟨b, hb⟩ := hw
    have hwa' : f w a = b * g w a := by
      simpa only [Pi.smul_apply, smul_eq_mul] using (congrFun hb a).symm
    have hc : c w = b := by simp [c, hwa', hwa]
    rw [hc, hb]
  have hc : c z ≠ 0 := by
    intro h
    apply hfn
    simpa only [h, zero_smul] using he.self_of_nhds
  have hJ : jacobianMatrix f z = jacobianMatrix (fun w => c w • g w) z := by
    unfold jacobianMatrix
    rw [he.fderiv_eq]
  rw [he.self_of_nhds, hJ, jacobianMatrix_smul hd hg]
  exact fsMatrix_gauge hc hgn _ _

end ProjectiveKaehler

namespace Anticanonical.ComplexAtlas
open ProjectiveKaehler Filter Topology Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma ProjectiveEmbedding.backgroundMatrix_compatibility (P : A.ProjectiveEmbedding)
    (i j : Fin A.count) (x : X) (hi : x ∈ (A.chart i).source)
    (hj : x ∈ (A.chart j).source) :
    P.backgroundMatrix i (A.chart i x) =
      (A.derivativeMatrix i j x)ᴴ * P.backgroundMatrix j (A.chart j x) *
        A.derivativeMatrix i j x := by
  let z := A.chart i x
  have hzi : z ∈ (A.chart i).target := (A.chart i).mapsTo hi
  have hzj : A.transition i j z ∈ (A.chart j).target := by
    rw [A.transition_at i j hi]
    exact (A.chart j).mapsTo hj
  have hdi := (P.holomorphic_lift i).differentiableAt ((A.chart i).open_target.mem_nhds hzi)
  have hdj := (P.holomorphic_lift j).differentiableAt ((A.chart j).open_target.mem_nhds hzj)
  have hdt := A.differentiableAt_transition i j hi hj
  have he := fsMatrix_eq_of_eventually_proportional hdi (hdj.comp z hdt)
    (P.lift_ne_zero i z hzi) (P.lift_ne_zero j _ hzj) ?_
  · change fsMatrix (P.lift i z) (jacobianMatrix (P.lift i) z) = _
    rw [he, jacobianMatrix_comp hdj hdt, fsMatrix_comp]
    simp only [Function.comp_apply, A.transition_at i j hi, derivativeMatrix,
      jacobianMatrix, backgroundMatrix, z]
  · filter_upwards [(A.isOpen_coordinateOverlap i j).mem_nhds
        (A.coordinate_mem_overlap i j hi hj)] with w hw
    have hwj : A.transition i j w ∈ (A.chart j).target := (A.chart j).mapsTo hw.2
    have heq : (A.chart j).symm (A.transition i j w) = (A.chart i).symm w :=
      (A.chart j).left_inv hw.2
    have hproj : Projectivization.mk ℂ (P.lift i w) (P.lift_ne_zero i w hw.1) =
        Projectivization.mk ℂ (P.lift j (A.transition i j w)) (P.lift_ne_zero j _ hwj) := by
      rw [← P.represents i w hw.1, ← P.represents j _ hwj, heq]
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp hproj
    exact ⟨(c : ℂ), hc⟩

end Anticanonical.ComplexAtlas

 

noncomputable section
namespace ProjectiveKaehler.Closedness
open Matrix Filter Topology
open scoped ComplexOrder Matrix.Norms.Elementwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {m : ℕ}

def pair (x y : Fin m → ℂ) : ℂ := star x ⬝ᵥ y

@[simp] lemma star_pair (x y : Fin m → ℂ) : star (pair x y) = pair y x := by
  simp [pair, dotProduct, star_sum, star_mul, mul_comm]

lemma pair_self_ne_zero {x : Fin m → ℂ} (hx : x ≠ 0) : pair x x ≠ 0 := by
  simpa only [pair, ne_eq, dotProduct_star_self_eq_zero] using hx

lemma smooth_pair {f g : E → (Fin m → ℂ)} {z : E}
    (hf : ContDiffAt ℝ ⊤ f z) (hg : ContDiffAt ℝ ⊤ g z) :
    ContDiffAt ℝ ⊤ (fun y => pair (f y) (g y)) z := by
  unfold pair dotProduct
  apply ContDiffAt.sum
  intro i _
  exact (Complex.conjCLE.contDiff.contDiffAt.comp z (contDiffAt_pi.mp hf i)).mul
    (contDiffAt_pi.mp hg i)

lemma fderiv_pair_apply {f g : E → (Fin m → ℂ)} {z : E}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (u : E) :
    fderiv ℝ (fun y => pair (f y) (g y)) z u =
      pair (fderiv ℝ f z u) (g z) + pair (f z) (fderiv ℝ g z u) := by
  have h (i : Fin m) := (differentiableAt_pi.mp hf i).hasFDerivAt.star.mul
    (differentiableAt_pi.mp hg i).hasFDerivAt
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => h i)
  simp only [Pi.mul_def] at hs
  change fderiv ℝ (fun y => ∑ i, star (f y i) * g y i) z u = _
  rw [hs.fderiv]
  simp only [_root_.sum_apply, Finset.sum_add_distrib, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  simp only [fderiv_apply hf, fderiv_apply hg]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  change (∑ i, star (f z i) * fderiv ℝ g z u i) +
    (∑ i, g z i * star (fderiv ℝ f z u i)) = _
  simp only [pair, dotProduct, Pi.star_apply]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

lemma fderiv_eval_derivative {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {z : E} (hf : ContDiffAt ℝ ⊤ f z) (u v : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) z u = fderiv ℝ (fderiv ℝ f) z u v := by
  rw [fderiv_clm_apply ((hf.fderiv_right (m := ⊤) (by simp)).differentiableAt (by simp))
    (differentiableAt_const v)]
  simp

lemma second_derivative_symmetric {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {z : E} (hf : ContDiffAt ℝ ⊤ f z) (u v : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) z u =
      fderiv ℝ (fun y => fderiv ℝ f y u) z v := by
  rw [fderiv_eval_derivative hf, fderiv_eval_derivative hf]
  exact hf.isSymmSndFDerivAt (by simp) u v

 
def beta (f : E → (Fin m → ℂ)) (w y : E) : ℝ :=
  ((pair (f y) (f y))⁻¹ * pair (f y) (fderiv ℝ f y w)).im

lemma smooth_beta {f : E → (Fin m → ℂ)} {z : E} (hf : ContDiffAt ℝ ⊤ f z)
    (hne : f z ≠ 0) (w : E) : ContDiffAt ℝ ⊤ (beta f w) z := by
  have hd := (hf.fderiv_right (m := ⊤) (by simp)).clm_apply (contDiffAt_const (c := w))
  exact Complex.imCLM.contDiff.contDiffAt.comp z
    (((smooth_pair hf hf).inv (pair_self_ne_zero hne)).mul (smooth_pair hf hd))

lemma fderiv_inv_complex_apply {q : E → ℂ} {z : E}
    (hq : DifferentiableAt ℝ q z) (hn : q z ≠ 0) (u : E) :
    fderiv ℝ (fun y => (q y)⁻¹) z u = -(q z)⁻¹ ^ 2 * fderiv ℝ q z u := by
  have h := ((hasDerivAt_inv hn).hasFDerivAt.restrictScalars ℝ).comp z hq.hasFDerivAt
  simp only [Function.comp_def] at h
  rw [h.fderiv]
  simp [ContinuousLinearMap.comp_apply, inv_pow, mul_comm]

lemma fderiv_im_apply {q : E → ℂ} {z : E}
    (hq : DifferentiableAt ℝ q z) (u : E) :
    fderiv ℝ (fun y => (q y).im) z u = (fderiv ℝ q z u).im := by
  have h := Complex.imCLM.hasFDerivAt.comp z hq.hasFDerivAt
  exact congrArg (fun l : E →L[ℝ] ℝ => l u) h.fderiv

lemma fderiv_beta {f : E → (Fin m → ℂ)} {z : E} (hf : ContDiffAt ℝ ⊤ f z)
    (hne : f z ≠ 0) (u w : E) :
    fderiv ℝ (beta f w) z u =
      (-(pair (f z) (f z))⁻¹ ^ 2 *
        (pair (fderiv ℝ f z u) (f z) + pair (f z) (fderiv ℝ f z u)) *
          pair (f z) (fderiv ℝ f z w) +
        (pair (f z) (f z))⁻¹ *
          (pair (fderiv ℝ f z u) (fderiv ℝ f z w) +
            pair (f z) (fderiv ℝ (fderiv ℝ f) z u w))).im := by
  have hD : ContDiffAt ℝ ⊤ (fun y => fderiv ℝ f y w) z :=
    (hf.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hQ := (smooth_pair hf hf).differentiableAt (by simp)
  have hR := (smooth_pair hf hD).differentiableAt (by simp)
  have hI := hQ.inv (pair_self_ne_zero hne)
  unfold beta
  have hP : DifferentiableAt ℝ (fun y => (pair (f y) (f y))⁻¹ *
      pair (f y) (fderiv ℝ f y w)) z := by
    simpa only [Pi.mul_def, Pi.inv_def] using hI.mul hR
  rw [fderiv_im_apply hP]
  have hM := fderiv_mul hI hR
  simp only [Pi.mul_def, Pi.inv_def] at hM
  rw [hM]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [fderiv_inv_complex_apply hQ (pair_self_ne_zero hne)]
  rw [fderiv_pair_apply (hf.differentiableAt (by simp)) (hf.differentiableAt (by simp)),
    fderiv_pair_apply (hf.differentiableAt (by simp)) (hD.differentiableAt (by simp)),
    fderiv_eval_derivative hf]
  congr 1
  ring

lemma anti_beta_algebra (r a b c t : ℂ) (hr : star r = r) :
    (-r ^ 2 * (star a + a) * b + r * (c + t)).im -
      (-r ^ 2 * (star b + b) * a + r * (star c + t)).im =
        2 * (r * c - r ^ 2 * (star a * b)).im := by
  rw [← Complex.sub_im]
  have h : (-r ^ 2 * (star a + a) * b + r * (c + t)) -
      (-r ^ 2 * (star b + b) * a + r * (star c + t)) =
      (r * c - r ^ 2 * (star a * b)) - star (r * c - r ^ 2 * (star a * b)) := by
    simp only [star_sub, star_mul, star_pow, star_star, hr]
    ring
  rw [h]
  simp only [Complex.sub_im, Complex.star_def, Complex.conj_im]
  ring

 

def omega (f : E → (Fin m → ℂ)) (v w y : E) : ℝ :=
  ((pair (f y) (f y))⁻¹ * pair (fderiv ℝ f y v) (fderiv ℝ f y w) -
    (pair (f y) (f y))⁻¹ ^ 2 *
      (pair (fderiv ℝ f y v) (f y) * pair (f y) (fderiv ℝ f y w))).im

lemma beta_antisym {f : E → (Fin m → ℂ)} {z : E} (hf : ContDiffAt ℝ ⊤ f z)
    (hne : f z ≠ 0) (v w : E) :
    fderiv ℝ (beta f w) z v - fderiv ℝ (beta f v) z w = 2 * omega f v w z := by
  rw [fderiv_beta hf hne, fderiv_beta hf hne,
    (hf.isSymmSndFDerivAt (by simp) w v)]
  unfold omega
  rw [← star_pair (f z) (fderiv ℝ f z v),
    ← star_pair (f z) (fderiv ℝ f z w),
    ← star_pair (fderiv ℝ f z v) (fderiv ℝ f z w)]
  apply anti_beta_algebra
  simp

lemma cyclic_antisym_derivative {b : E → E → ℝ} {z : E}
    (hb : ∀ v, ContDiffAt ℝ ⊤ (b v) z) (u v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (b w) y v - fderiv ℝ (b v) y w) z u +
      fderiv ℝ (fun y => fderiv ℝ (b u) y w - fderiv ℝ (b w) y u) z v +
      fderiv ℝ (fun y => fderiv ℝ (b v) y u - fderiv ℝ (b u) y v) z w = 0 := by
  have hd (a c : E) : DifferentiableAt ℝ (fun y => fderiv ℝ (b a) y c) z :=
    (((hb a).fderiv_right (m := ⊤) (by simp)).clm_apply contDiffAt_const).differentiableAt
      (by simp)
  simp only [fderiv_fun_sub (hd _ _) (hd _ _), _root_.sub_apply]
  rw [second_derivative_symmetric (hb w) u v, second_derivative_symmetric (hb v) u w,
    second_derivative_symmetric (hb u) v w]
  ring

lemma smooth_omega {f : E → (Fin m → ℂ)} {z : E} (hf : ContDiffAt ℝ ⊤ f z)
    (hne : f z ≠ 0) (v w : E) : ContDiffAt ℝ ⊤ (omega f v w) z := by
  have hD (a : E) : ContDiffAt ℝ ⊤ (fun y => fderiv ℝ f y a) z :=
    (hf.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hI := (smooth_pair hf hf).inv (pair_self_ne_zero hne)
  exact Complex.imCLM.contDiff.contDiffAt.comp z
    ((hI.mul (smooth_pair (hD v) (hD w))).sub
      ((hI.pow 2).mul ((smooth_pair (hD v) hf).mul (smooth_pair hf (hD w)))))

 

lemma omega_closed {f : E → (Fin m → ℂ)} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ⊤ f U) (hne : ∀ y ∈ U, f y ≠ 0)
    {z : E} (hz : z ∈ U) (u v w : E) :
    fderiv ℝ (omega f v w) z u + fderiv ℝ (omega f w u) z v +
      fderiv ℝ (omega f u v) z w = 0 := by
  have hfc := hf.contDiffAt (hU.mem_nhds hz)
  have hbc (a : E) := smooth_beta hfc (hne z hz) a
  have he (a b c : E) :
      fderiv ℝ (fun y => fderiv ℝ (beta f b) y a - fderiv ℝ (beta f a) y b) z c =
        2 * fderiv ℝ (omega f a b) z c := by
    have heq : (fun y => fderiv ℝ (beta f b) y a - fderiv ℝ (beta f a) y b)
        =ᶠ[𝓝 z] (fun y => 2 * omega f a b y) := by
      filter_upwards [hU.mem_nhds hz] with y hy
      exact beta_antisym (hf.contDiffAt (hU.mem_nhds hy)) (hne y hy) a b
    rw [heq.fderiv_eq, fderiv_const_mul
      ((smooth_omega hfc (hne z hz) a b).differentiableAt (by simp))]
    rfl
  have hc := cyclic_antisym_derivative hbc u v w
  rw [he, he, he] at hc
  linarith

end ProjectiveKaehler.Closedness

namespace ProjectiveKaehler
open Anticanonical.ComplexAtlas Matrix
variable {m n : ℕ}

lemma fundamentalForm_fs_eq_omega {f : (Fin n → ℂ) → (Fin m → ℂ)}
    {z : Fin n → ℂ} (hf : DifferentiableAt ℂ f z) (hne : f z ≠ 0) (v w : Fin n → ℂ) :
    fundamentalForm (fsMatrix (f z) (jacobianMatrix f z)) v w =
      Closedness.omega f v w z := by
  have hd (a : Fin n → ℂ) : fderiv ℝ f z a = fderiv ℂ f z a := by
    rw [(hf.hasFDerivAt.restrictScalars ℝ).fderiv]
    rfl
  unfold fundamentalForm
  rw [fsMatrix_pair hne]
  simp only [jacobianMatrix_mulVec, Closedness.omega, Closedness.pair, mass, hd]

end ProjectiveKaehler

namespace Anticanonical.ComplexAtlas
open ProjectiveKaehler Filter Topology Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma ProjectiveEmbedding.backgroundMatrix_closed (P : A.ProjectiveEmbedding)
    (i : Fin A.count) {z : Coordinates d} (hz : z ∈ (A.chart i).target)
    (u v w : Coordinates d) :
    fderiv ℝ (fun y => fundamentalForm (P.backgroundMatrix i y) v w) z u +
      fderiv ℝ (fun y => fundamentalForm (P.backgroundMatrix i y) w u) z v +
      fderiv ℝ (fun y => fundamentalForm (P.backgroundMatrix i y) u v) z w = 0 := by
  have hs := contDiffOn_real_pi_of_differentiableOn (A.chart i).open_target
    (P.holomorphic_lift i)
  have he (a b : Coordinates d) :
      (fun y => fundamentalForm (P.backgroundMatrix i y) a b)
        =ᶠ[𝓝 z] Closedness.omega (P.lift i) a b := by
    filter_upwards [(A.chart i).open_target.mem_nhds hz] with y hy
    exact fundamentalForm_fs_eq_omega
      ((P.holomorphic_lift i).differentiableAt ((A.chart i).open_target.mem_nhds hy))
      (P.lift_ne_zero i y hy) a b
  rw [(he v w).fderiv_eq, (he w u).fderiv_eq, (he u v).fderiv_eq]
  exact Closedness.omega_closed (A.chart i).open_target hs (P.lift_ne_zero i) hz u v w

 

def ProjectiveEmbedding.backgroundKaehlerMetric (P : A.ProjectiveEmbedding) : A.KaehlerMetric where
  matrix := P.backgroundMatrix
  smooth := P.backgroundMatrix_smooth
  positive := fun i _ hz => P.backgroundMatrix_positive i hz
  compatibility := P.backgroundMatrix_compatibility
  closed := fun i _ hz => P.backgroundMatrix_closed i hz

theorem ProjectiveEmbedding.nonemptyKaehlerMetric (P : A.ProjectiveEmbedding) :
    Nonempty A.KaehlerMetric := ⟨P.backgroundKaehlerMetric⟩

end Anticanonical.ComplexAtlas

 

namespace Anticanonical.SourceSmooth
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
open Matrix
variable {d : ℕ} {X : Type*} [TopologicalSpace X]

 

def levi (φ : Coordinates d → ℝ) (z v : Coordinates d) : ℝ :=
  (fderiv ℝ (fderiv ℝ φ) z v) v +
    (fderiv ℝ (fderiv ℝ φ) z (Complex.I • v)) (Complex.I • v)

 
structure SemipositiveAnticanonicalMetric (A : ComplexAtlas d X) where
  weight : Fin A.count → Coordinates d → ℝ
  smooth : ∀ i, ContDiffOn ℝ ∞ (weight i) (A.chart i).target
  compatibility : ∀ i j x, x ∈ (A.chart i).source → x ∈ (A.chart j).source →
    weight j (A.chart j x) =
      weight i (A.chart i x) + Real.log (‖A.jacobian i j x‖ ^ 2)
  semipositive : ∀ i z, z ∈ (A.chart i).target →
    ∀ v : Coordinates d, 0 ≤ levi (weight i) z v

 
structure KaehlerMetric (A : ComplexAtlas d X) where
  matrix : Fin A.count → Coordinates d → Matrix (Fin d) (Fin d) ℂ
  smooth : ∀ i, ContDiffOn ℝ ∞ (matrix i) (A.chart i).target
  positive : ∀ i z, z ∈ (A.chart i).target → (matrix i z).PosDef
  compatibility : ∀ i j x, x ∈ (A.chart i).source → x ∈ (A.chart j).source →
    matrix i (A.chart i x) =
      (A.derivativeMatrix i j x)ᴴ * matrix j (A.chart j x) * A.derivativeMatrix i j x
  closed : ∀ i z, z ∈ (A.chart i).target → ∀ u v w : Coordinates d,
    fderiv ℝ (fun y ↦ ComplexAtlas.fundamentalForm (matrix i y) v w) z u +
      fderiv ℝ (fun y ↦ ComplexAtlas.fundamentalForm (matrix i y) w u) z v +
      fderiv ℝ (fun y ↦ ComplexAtlas.fundamentalForm (matrix i y) u v) z w = 0

namespace KaehlerMetric
variable {A : ComplexAtlas d X}
def volumeCoefficient (g : KaehlerMetric A) (i : Fin A.count) (z : Coordinates d) : ℝ :=
  (g.matrix i z).det.re

def ricciPotential (g : KaehlerMetric A) (i : Fin A.count) (z : Coordinates d) : ℝ :=
  -Real.log (g.volumeCoefficient i z)

def ricciQuadratic (g : KaehlerMetric A) (i : Fin A.count) (z v : Coordinates d) : ℝ :=
  levi (g.ricciPotential i) z v
end KaehlerMetric

 

def PrescribedRicci : Prop :=
  ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] (A : ComplexAtlas d X),
    Nonempty A.ProjectiveEmbedding →
    ∀ h : SemipositiveAnticanonicalMetric A,
      ∃ g : KaehlerMetric A, ∀ i z, z ∈ (A.chart i).target →
        ∀ v : Coordinates d, g.ricciQuadratic i z v = levi (h.weight i) z v

end Anticanonical.SourceSmooth

namespace Anticanonical.SourceSmooth
open scoped ContDiff
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

 

def projectiveBackground (P : A.ProjectiveEmbedding) : KaehlerMetric A where
  matrix := P.backgroundMatrix
  smooth := fun i => (P.backgroundMatrix_smooth i).of_le (by simp)
  positive := fun i _ hz => P.backgroundMatrix_positive i hz
  compatibility := P.backgroundMatrix_compatibility
  closed := fun i _ hz => P.backgroundMatrix_closed i hz

end Anticanonical.SourceSmooth

 

noncomputable section
namespace PotentialKaehler
open Matrix
open scoped Matrix.Norms.Elementwise ComplexOrder ContDiff

variable {n : ℕ}
abbrev V (n : ℕ) := Fin n → ℂ
abbrev RealBilinear (n : ℕ) := V n →L[ℝ] V n →L[ℝ] ℝ

 

def hermitianPart (B : RealBilinear n) (u v : V n) : ℂ :=
  ⟨(B u v + B (Complex.I • u) (Complex.I • v)) / 4,
    (B (Complex.I • u) v - B u (Complex.I • v)) / 4⟩

lemma complex_smul_decompose (a : ℂ) (v : V n) :
    a • v = a.re • v + a.im • (Complex.I • v) := by
  ext i
  change a * v i = a.re • v i + a.im • (Complex.I * v i)
  rw [Complex.real_smul, Complex.real_smul, ← mul_assoc, ← add_mul, Complex.re_add_im]

lemma hermitianPart_add_left (B : RealBilinear n) (u u' v : V n) :
    hermitianPart B (u + u') v = hermitianPart B u v + hermitianPart B u' v := by
  apply Complex.ext <;> simp [hermitianPart, smul_add, map_add] <;> ring

lemma hermitianPart_add_right (B : RealBilinear n) (u v v' : V n) :
    hermitianPart B u (v + v') = hermitianPart B u v + hermitianPart B u v' := by
  apply Complex.ext <;> simp [hermitianPart, smul_add, map_add] <;> ring

lemma hermitianPart_real_smul_left (B : RealBilinear n) (a : ℝ) (u v : V n) :
    hermitianPart B (a • u) v = a • hermitianPart B u v := by
  apply Complex.ext <;> simp [hermitianPart, smul_comm Complex.I a, map_smul, smul_eq_mul] <;> ring

lemma hermitianPart_real_smul_right (B : RealBilinear n) (a : ℝ) (u v : V n) :
    hermitianPart B u (a • v) = a • hermitianPart B u v := by
  apply Complex.ext <;> simp [hermitianPart, smul_comm Complex.I a, map_smul, smul_eq_mul] <;> ring

lemma hermitianPart_I_left (B : RealBilinear n) (u v : V n) :
    hermitianPart B (Complex.I • u) v = -Complex.I * hermitianPart B u v := by
  apply Complex.ext <;> simp [hermitianPart, smul_smul, Complex.I_mul_I, map_neg] <;> ring

lemma hermitianPart_I_right (B : RealBilinear n) (u v : V n) :
    hermitianPart B u (Complex.I • v) = Complex.I * hermitianPart B u v := by
  apply Complex.ext <;> simp [hermitianPart, smul_smul, Complex.I_mul_I, map_neg] <;> ring

lemma hermitianPart_smul_left (B : RealBilinear n) (a : ℂ) (u v : V n) :
    hermitianPart B (a • u) v = star a * hermitianPart B u v := by
  rw [complex_smul_decompose, hermitianPart_add_left,
    hermitianPart_real_smul_left, hermitianPart_real_smul_left, hermitianPart_I_left]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

lemma hermitianPart_smul_right (B : RealBilinear n) (a : ℂ) (u v : V n) :
    hermitianPart B u (a • v) = a * hermitianPart B u v := by
  rw [complex_smul_decompose, hermitianPart_add_right,
    hermitianPart_real_smul_right, hermitianPart_real_smul_right, hermitianPart_I_right]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  ring

 
def hermitianPartForm (B : RealBilinear n) : V n →ₗ⋆[ℂ] V n →ₗ[ℂ] ℂ where
  toFun u :=
    { toFun := hermitianPart B u
      map_add' := hermitianPart_add_right B u
      map_smul' := fun a v => hermitianPart_smul_right B a u v }
  map_add' u u' := by
    apply LinearMap.ext
    intro v
    exact hermitianPart_add_left B u u' v
  map_smul' a u := by
    apply LinearMap.ext
    intro v
    exact hermitianPart_smul_left B a u v

lemma hermitianPart_star (B : RealBilinear n) (hB : ∀ u v, B u v = B v u) (u v : V n) :
    star (hermitianPart B u v) = hermitianPart B v u := by
  apply Complex.ext <;> simp [hermitianPart, hB u v, hB (Complex.I • u) (Complex.I • v),
    hB (Complex.I • u) v, hB u (Complex.I • v)]
  ring

def hermitianPartMatrix (B : RealBilinear n) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix₂ (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n)) (hermitianPartForm B)

lemma hermitianPartMatrix_apply (B : RealBilinear n) (i j : Fin n) :
    hermitianPartMatrix B i j = hermitianPart B (Pi.single i 1) (Pi.single j 1) := by
  simp [hermitianPartMatrix, LinearMap.toMatrix₂_apply, hermitianPartForm]

lemma hermitianPartMatrix_pair (B : RealBilinear n) (u v : V n) :
    star u ⬝ᵥ (hermitianPartMatrix B *ᵥ v) = hermitianPart B u v := by
  simpa [hermitianPartMatrix, hermitianPartForm] using
    (star_dotProduct_toMatrix₂_mulVec (B := hermitianPartForm B) (Pi.basisFun ℂ (Fin n)) u v)

lemma hermitianPartMatrix_hermitian (B : RealBilinear n) (hB : ∀ u v, B u v = B v u) :
    (hermitianPartMatrix B).IsHermitian := by
  apply (LinearMap.isSymm_iff_isHermitian_toMatrix (Pi.basisFun ℂ (Fin n))).mp
  exact ⟨hermitianPart_star B hB⟩

 
def potentialMatrix (φ : V n → ℝ) (z : V n) : Matrix (Fin n) (Fin n) ℂ :=
  hermitianPartMatrix (fderiv ℝ (fderiv ℝ φ) z)

lemma potentialMatrix_hermitian {φ : V n → ℝ} {z : V n}
    (hφ : ContDiffAt ℝ ∞ φ z) : (potentialMatrix φ z).IsHermitian := by
  apply hermitianPartMatrix_hermitian
  exact hφ.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞); exact WithTop.coe_le_coe.mpr le_top)

lemma smooth_hermitianPart {B : V n → RealBilinear n} {z : V n}
    (hB : ContDiffAt ℝ ∞ B z) (u v : V n) :
    ContDiffAt ℝ ∞ (fun y => hermitianPart (B y) u v) z := by
  have hs (a b : V n) : ContDiffAt ℝ ∞ (fun y => B y a b) z :=
    (hB.clm_apply contDiffAt_const).clm_apply contDiffAt_const
  have hr := ((hs u v).add (hs (Complex.I • u) (Complex.I • v))).div_const 4
  have hi := ((hs (Complex.I • u) v).sub (hs u (Complex.I • v))).div_const 4
  simpa only [hermitianPart, Complex.mk_eq_add_mul_I, Function.comp_def, Complex.ofRealCLM_apply] using
    (Complex.ofRealCLM.contDiff.contDiffAt.comp z hr).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp z hi).mul (contDiffAt_const (c := Complex.I)))

lemma potentialMatrix_smooth {φ : V n → ℝ} {z : V n}
    (hφ : ContDiffAt ℝ ∞ φ z) : ContDiffAt ℝ ∞ (potentialMatrix φ) z := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simpa only [potentialMatrix, hermitianPartMatrix_apply] using
    smooth_hermitianPart ((hφ.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp))
      (Pi.single i 1) (Pi.single j 1)

section Derivatives
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma fderiv_eval_derivative {f : E → F} {z : E} (hf : ContDiffAt ℝ ∞ f z) (u v : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) z u = fderiv ℝ (fderiv ℝ f) z u v := by
  rw [fderiv_clm_apply ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    (differentiableAt_const v)]
  simp

lemma second_derivative_symmetric {f : E → F} {z : E}
    (hf : ContDiffAt ℝ ∞ f z) (u v : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) z u =
      fderiv ℝ (fun y => fderiv ℝ f y u) z v := by
  rw [fderiv_eval_derivative hf, fderiv_eval_derivative hf]
  exact hf.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞); exact WithTop.coe_le_coe.mpr le_top) u v

lemma cyclic_antisym_derivative {b : E → E → ℝ} {z : E}
    (hb : ∀ v, ContDiffAt ℝ ∞ (b v) z) (u v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (b w) y v - fderiv ℝ (b v) y w) z u +
      fderiv ℝ (fun y => fderiv ℝ (b u) y w - fderiv ℝ (b w) y u) z v +
      fderiv ℝ (fun y => fderiv ℝ (b v) y u - fderiv ℝ (b u) y v) z w = 0 := by
  have hd (a c : E) : DifferentiableAt ℝ (fun y => fderiv ℝ (b a) y c) z :=
    (((hb a).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt
      (by simp)
  simp only [fderiv_fun_sub (hd _ _) (hd _ _), _root_.sub_apply]
  rw [second_derivative_symmetric (hb w) u v, second_derivative_symmetric (hb v) u w,
    second_derivative_symmetric (hb u) v w]
  ring
end Derivatives

 
def potentialPrimitive (φ : V n → ℝ) (v z : V n) : ℝ :=
  -(fderiv ℝ φ z (Complex.I • v)) / 4

def potentialForm (φ : V n → ℝ) (u v z : V n) : ℝ :=
  (star u ⬝ᵥ (potentialMatrix φ z *ᵥ v)).im

lemma potentialPrimitive_smooth {φ : V n → ℝ} {z : V n}
    (hφ : ContDiffAt ℝ ∞ φ z) (v : V n) :
    ContDiffAt ℝ ∞ (potentialPrimitive φ v) z :=
  (((hφ.fderiv_right (by simp)).clm_apply contDiffAt_const).neg).div_const 4

lemma potentialPrimitive_derivative {φ : V n → ℝ} {z : V n}
    (hφ : ContDiffAt ℝ ∞ φ z) (u v : V n) :
    fderiv ℝ (potentialPrimitive φ v) z u =
      -(fderiv ℝ (fderiv ℝ φ) z u (Complex.I • v)) / 4 := by
  have hd := ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply
    (contDiffAt_const (c := Complex.I • v))).differentiableAt (by simp)
  unfold potentialPrimitive
  simp only [div_eq_mul_inv]
  have hm := fderiv_mul_const (hd.neg) (4 : ℝ)⁻¹
  simp only [Pi.neg_apply] at hm
  rw [hm]
  rw [fderiv_neg]
  simp only [_root_.smul_apply, _root_.neg_apply, smul_eq_mul,
    fderiv_eval_derivative hφ]
  ring

lemma potentialPrimitive_antisym {φ : V n → ℝ} {z : V n}
    (hφ : ContDiffAt ℝ ∞ φ z) (u v : V n) :
    fderiv ℝ (potentialPrimitive φ v) z u -
      fderiv ℝ (potentialPrimitive φ u) z v = potentialForm φ u v z := by
  rw [potentialPrimitive_derivative hφ, potentialPrimitive_derivative hφ]
  simp only [potentialForm, potentialMatrix, hermitianPartMatrix_pair, hermitianPart]
  rw [hφ.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞); exact WithTop.coe_le_coe.mpr le_top) v (Complex.I • u)]
  ring

lemma potentialMatrix_closed {φ : V n → ℝ} {U : Set (V n)}
    (hU : IsOpen U) (hφ : ContDiffOn ℝ ∞ φ U) {z : V n} (hz : z ∈ U)
    (u v w : V n) :
    fderiv ℝ (potentialForm φ v w) z u + fderiv ℝ (potentialForm φ w u) z v +
      fderiv ℝ (potentialForm φ u v) z w = 0 := by
  have he (a b : V n) :
      (fun y => fderiv ℝ (potentialPrimitive φ b) y a -
        fderiv ℝ (potentialPrimitive φ a) y b) =ᶠ[nhds z] potentialForm φ a b := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact potentialPrimitive_antisym (hφ.contDiffAt (hU.mem_nhds hy)) a b
  have hc := cyclic_antisym_derivative
    (fun a => potentialPrimitive_smooth (hφ.contDiffAt (hU.mem_nhds hz)) a) u v w
  rwa [(he _ _).fderiv_eq, (he _ _).fderiv_eq, (he _ _).fderiv_eq] at hc

section ChainRule
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma eventually_differentiableAt {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] {f : E → F} {z : E}
    (hf : ContDiffAt 𝕜 ∞ f z) :
    ∀ᶠ y in nhds z, DifferentiableAt 𝕜 f y := by
  have h1 : ContDiffAt 𝕜 1 f z := (contDiffAt_infty.mp hf) 1
  exact (h1.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)

lemma second_derivative_comp {f : E → F} {g : F → G} {z : E}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g (f z)) (u v : E) :
    fderiv ℝ (fderiv ℝ (g ∘ f)) z u v =
      fderiv ℝ (fderiv ℝ g) (f z) (fderiv ℝ f z u) (fderiv ℝ f z v) +
        fderiv ℝ g (f z) (fderiv ℝ (fderiv ℝ f) z u v) := by
  have hfd := hf.differentiableAt (by simp)
  have hgd := hg.differentiableAt (by simp)
  have hDf := (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hDg := (hg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have he : fderiv ℝ (g ∘ f) =ᶠ[nhds z] fun y =>
      (fderiv ℝ g (f y)).comp (fderiv ℝ f y) := by
    filter_upwards [eventually_differentiableAt hf,
      hf.continuousAt.tendsto.eventually (eventually_differentiableAt hg)] with y hy hy'
    exact fderiv_comp y hy' hy
  rw [he.fderiv_eq]
  have hm := fderiv_clm_comp (hDg.comp z hfd) hDf
  simp only [Function.comp_def] at hm
  rw [hm]
  have hc := fderiv_comp z hDg hfd
  simp only [Function.comp_def] at hc
  rw [hc]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  exact add_comm _ _
end ChainRule

lemma fderiv_complex_smul {m : ℕ} {f : V n → V m} {z : V n}
    (hf : DifferentiableAt ℂ f z) (a : ℂ) (v : V n) :
    fderiv ℝ f z (a • v) = a • fderiv ℝ f z v := by
  rw [hf.fderiv_restrictScalars (𝕜 := ℝ)]
  exact map_smul (fderiv ℂ f z) a v

lemma second_derivative_complex_smul_right {m : ℕ} {f : V n → V m} {z : V n}
    (hf : ContDiffAt ℂ ∞ f z) (a : ℂ) (u v : V n) :
    fderiv ℝ (fderiv ℝ f) z u (a • v) =
      a • fderiv ℝ (fderiv ℝ f) z u v := by
  have hr := hf.restrict_scalars ℝ
  have hd := ((hr.fderiv_right (m := ∞) (by simp)).clm_apply
    (contDiffAt_const (c := v))).differentiableAt (by simp)
  have he : (fun y => fderiv ℝ f y (a • v)) =ᶠ[nhds z]
      (fun y => a • fderiv ℝ f y v) := by
    filter_upwards [eventually_differentiableAt hf] with y hy
    exact fderiv_complex_smul hy a v
  have he' := congrArg (fun l : V n →L[ℝ] V m => l u) he.fderiv_eq
  rw [fderiv_eval_derivative hr] at he'
  have hs : fderiv ℝ (fun y => a • fderiv ℝ f y v) z =
      a • fderiv ℝ (fun y => fderiv ℝ f y v) z := fderiv_const_smul hd a
  rw [hs] at he'
  simpa only [_root_.smul_apply, fderiv_eval_derivative hr] using he'

lemma second_derivative_complex_smul_left {m : ℕ} {f : V n → V m} {z : V n}
    (hf : ContDiffAt ℂ ∞ f z) (a : ℂ) (u v : V n) :
    fderiv ℝ (fderiv ℝ f) z (a • u) v =
      a • fderiv ℝ (fderiv ℝ f) z u v := by
  have hs := (hf.restrict_scalars ℝ).isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
  rw [hs (a • u) v, second_derivative_complex_smul_right hf, hs v u]

 

lemma hermitianPart_comp {m : ℕ} {f : V n → V m} {φ : V m → ℝ} {z : V n}
    (hf : ContDiffAt ℂ ∞ f z) (hφ : ContDiffAt ℝ ∞ φ (f z)) (u v : V n) :
    hermitianPart (fderiv ℝ (fderiv ℝ (φ ∘ f)) z) u v =
      hermitianPart (fderiv ℝ (fderiv ℝ φ) (f z))
        (fderiv ℝ f z u) (fderiv ℝ f z v) := by
  have hr := hf.restrict_scalars ℝ
  have hd := hf.differentiableAt (by simp)
  apply Complex.ext <;>
    simp only [hermitianPart, second_derivative_comp hr hφ,
      fderiv_complex_smul hd, second_derivative_complex_smul_left hf,
      second_derivative_complex_smul_right hf, smul_smul, Complex.I_mul_I,
      neg_smul, one_smul, map_neg] <;> ring

lemma matrix_pair_pullback {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)
    (D : Matrix (Fin m) (Fin n) ℂ) (u v : V n) :
    star u ⬝ᵥ ((Dᴴ * H * D) *ᵥ v) = star (D *ᵥ u) ⬝ᵥ (H *ᵥ (D *ᵥ v)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]

lemma matrix_eq_of_pair (H K : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ u v : V n, star u ⬝ᵥ (H *ᵥ v) = star u ⬝ᵥ (K *ᵥ v)) : H = K := by
  ext i j
  simpa using h (Pi.single i 1) (Pi.single j 1)

lemma potentialMatrix_congr {φ ψ : V n → ℝ} {z : V n}
    (he : φ =ᶠ[nhds z] ψ) : potentialMatrix φ z = potentialMatrix ψ z := by
  unfold potentialMatrix
  rw [(he.fderiv (𝕜 := ℝ)).fderiv_eq]

lemma potentialMatrix_comp {m : ℕ} {f : V n → V m} {φ : V m → ℝ} {z : V n}
    (hf : ContDiffAt ℂ ∞ f z) (hφ : ContDiffAt ℝ ∞ φ (f z)) :
    potentialMatrix (φ ∘ f) z =
      (LinearMap.toMatrix' (fderiv ℂ f z).toLinearMap)ᴴ *
        potentialMatrix φ (f z) * LinearMap.toMatrix' (fderiv ℂ f z).toLinearMap := by
  apply matrix_eq_of_pair
  intro u v
  rw [matrix_pair_pullback]
  simp only [potentialMatrix, hermitianPartMatrix_pair, LinearMap.toMatrix'_mulVec]
  have he := hermitianPart_comp hf hφ u v
  rw [(hf.differentiableAt (by simp)).fderiv_restrictScalars (𝕜 := ℝ)] at he
  exact he

end PotentialKaehler

namespace Anticanonical.SourceSmooth
open Matrix Filter
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

 
structure SmoothRealFunction (A : ComplexAtlas d X) where
  value : X → ℝ
  smooth : ∀ i, ContDiffOn ℝ ∞ (value ∘ (A.chart i).symm) (A.chart i).target

namespace SmoothRealFunction

def localExpression (φ : SmoothRealFunction A) (i : Fin A.count) : Coordinates d → ℝ :=
  φ.value ∘ (A.chart i).symm

 
def hessian (φ : SmoothRealFunction A) (i : Fin A.count) (z : Coordinates d) :
    Matrix (Fin d) (Fin d) ℂ := PotentialKaehler.potentialMatrix (φ.localExpression i) z

lemma hessian_smooth (φ : SmoothRealFunction A) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (φ.hessian i) (A.chart i).target := by
  intro z hz
  exact (PotentialKaehler.potentialMatrix_smooth
    ((φ.smooth i).contDiffAt ((A.chart i).open_target.mem_nhds hz))).contDiffWithinAt

lemma hessian_hermitian (φ : SmoothRealFunction A) (i : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart i).target) : (φ.hessian i z).IsHermitian :=
  PotentialKaehler.potentialMatrix_hermitian
    ((φ.smooth i).contDiffAt ((A.chart i).open_target.mem_nhds hz))

lemma hessian_compatibility (φ : SmoothRealFunction A) (i j : Fin A.count) {x : X}
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source) :
    φ.hessian i (A.chart i x) =
      (A.derivativeMatrix i j x)ᴴ * φ.hessian j (A.chart j x) * A.derivativeMatrix i j x := by
  have hz := A.coordinate_mem_overlap i j hi hj
  have ho := A.isOpen_coordinateOverlap i j
  have hf : ContDiffAt ℂ ∞ (A.transition i j) (A.chart i x) :=
    (ProjectiveKaehler.analyticOnNhd_pi_of_differentiableOn ho (A.holomorphic i j) _ hz).contDiffAt
  have hφ : ContDiffAt ℝ ∞ (φ.localExpression j) (A.transition i j (A.chart i x)) := by
    rw [A.transition_at i j hi]
    exact (φ.smooth j).contDiffAt ((A.chart j).open_target.mem_nhds ((A.chart j).mapsTo hj))
  have he : φ.localExpression i =ᶠ[nhds (A.chart i x)]
      φ.localExpression j ∘ A.transition i j := by
    filter_upwards [ho.mem_nhds hz] with y hy
    dsimp only [localExpression, ComplexAtlas.transition, Function.comp_apply]
    rw [(A.chart j).left_inv hy.2]
  unfold hessian
  rw [PotentialKaehler.potentialMatrix_congr he,
    PotentialKaehler.potentialMatrix_comp hf hφ, A.transition_at i j hi]
  rfl

lemma hessian_closed (φ : SmoothRealFunction A) (i : Fin A.count) {z : Coordinates d}
    (hz : z ∈ (A.chart i).target) (u v w : Coordinates d) :
    fderiv ℝ (fun y => ComplexAtlas.fundamentalForm (φ.hessian i y) v w) z u +
      fderiv ℝ (fun y => ComplexAtlas.fundamentalForm (φ.hessian i y) w u) z v +
      fderiv ℝ (fun y => ComplexAtlas.fundamentalForm (φ.hessian i y) u v) z w = 0 :=
  PotentialKaehler.potentialMatrix_closed (A.chart i).open_target (φ.smooth i) hz u v w

end SmoothRealFunction

lemma fundamentalForm_add (H K : Matrix (Fin d) (Fin d) ℂ) (u v : Coordinates d) :
    ComplexAtlas.fundamentalForm (H + K) u v =
      ComplexAtlas.fundamentalForm H u v + ComplexAtlas.fundamentalForm K u v := by
  simp [ComplexAtlas.fundamentalForm, add_mulVec, dotProduct_add]

lemma fundamentalForm_smooth {g : Coordinates d → Matrix (Fin d) (Fin d) ℂ}
    {z : Coordinates d} (hg : ContDiffAt ℝ ∞ g z) (u v : Coordinates d) :
    ContDiffAt ℝ ∞ (fun y => ComplexAtlas.fundamentalForm (g y) u v) z := by
  apply Complex.imCLM.contDiff.contDiffAt.comp z
  apply ContDiffAt.sum
  intro i _
  apply contDiffAt_const.mul
  change ContDiffAt ℝ ∞ (fun y => ∑ j, g y i j * v j) z
  apply ContDiffAt.sum
  intro j _
  exact (contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j).mul contDiffAt_const

namespace KaehlerMetric

 

def PositivePotential (g : KaehlerMetric A) (φ : SmoothRealFunction A) : Prop :=
  ∀ i z, z ∈ (A.chart i).target → (g.matrix i z + φ.hessian i z).PosDef

 

def deform (g : KaehlerMetric A) (φ : SmoothRealFunction A) (hp : g.PositivePotential φ) :
    KaehlerMetric A where
  matrix i z := g.matrix i z + φ.hessian i z
  smooth i := (g.smooth i).add (φ.hessian_smooth i)
  positive := hp
  compatibility i j x hi hj := by
    rw [g.compatibility i j x hi hj, φ.hessian_compatibility i j hi hj]
    simp only [mul_add, add_mul]
  closed i z hz u v w := by
    have hg := (g.smooth i).contDiffAt ((A.chart i).open_target.mem_nhds hz)
    have hφ := (φ.hessian_smooth i).contDiffAt ((A.chart i).open_target.mem_nhds hz)
    simp only [fundamentalForm_add]
    simp only [fderiv_fun_add
      ((fundamentalForm_smooth hg _ _).differentiableAt (by simp))
      ((fundamentalForm_smooth hφ _ _).differentiableAt (by simp)), _root_.add_apply]
    have h1 := g.closed i z hz u v w
    have h2 := φ.hessian_closed i hz u v w
    linarith

end KaehlerMetric
end Anticanonical.SourceSmooth

 

open Matrix Polynomial
open scoped Matrix.Norms.Elementwise
noncomputable section
namespace MongeAmpere
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma hasDerivAt_det_one_add_smul (M : Matrix n n ℂ) :
    HasDerivAt (fun t : ℂ => (1 + t • M).det) M.trace 0 := by
  have hp := (Matrix.det (1 + (Polynomial.X : ℂ[X]) • M.map Polynomial.C)).hasDerivAt (0 : ℂ)
  rw [Matrix.derivative_det_one_add_X_smul] at hp
  simpa [eval_det, ← Matrix.smul_eq_mul_diagonal] using hp

lemma hasDerivAt_det_add_smul (H K : Matrix n n ℂ) (hH : IsUnit H.det) :
    HasDerivAt (fun t : ℂ => (H + t • K).det)
      (H.det * (H⁻¹ * K).trace) 0 := by
  have hd := (hasDerivAt_det_one_add_smul (H⁻¹ * K)).const_mul H.det
  apply hd.congr_of_eventuallyEq
  filter_upwards [] with t
  rw [← Matrix.det_mul]
  congr 1
  simp [Matrix.mul_add, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hH]

open scoped ComplexOrder

 

lemma hasDerivAt_logdet_add_smul (H K : Matrix n n ℂ) (hH : H.PosDef) :
    HasDerivAt (fun t : ℝ => Real.log ((H + (t : ℂ) • K).det.re))
      (H⁻¹ * K).trace.re 0 := by
  have hd := (hasDerivAt_det_add_smul H K (isUnit_iff_ne_zero.mpr (ne_of_gt hH.det_pos))).real_of_complex
  have hp := Complex.pos_iff.mp hH.det_pos
  have hne : (H + ((0 : ℝ) : ℂ) • K).det.re ≠ 0 := by
    simpa using ne_of_gt hp.1
  have hl := hd.log hne
  simpa [Complex.mul_re, hp.2.symm, hp.1.ne', mul_div_cancel_left₀] using hl

 

lemma linearized_symbol_pos (H : Matrix n n ℂ) (hH : H.PosDef)
    (v : n → ℂ) (hv : v ≠ 0) :
    0 < (H⁻¹ * Matrix.vecMulVec v (star v)).trace.re := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
  exact hH.inv.re_dotProduct_pos hv

end MongeAmpere

namespace Anticanonical.SourceSmooth
open Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

namespace SmoothRealFunction

def constant (c : ℝ) : SmoothRealFunction A where
  value _ := c
  smooth _ := contDiffOn_const

def realSMul (c : ℝ) (φ : SmoothRealFunction A) : SmoothRealFunction A where
  value x := c * φ.value x
  smooth i := contDiffOn_const.mul (φ.smooth i)

lemma hessian_constant (c : ℝ) (i : Fin A.count) (z : Coordinates d) :
    (constant (A := A) c).hessian i z = 0 := by
  ext a b
  apply Complex.ext <;> simp [hessian, localExpression, constant, Function.comp_def, PotentialKaehler.potentialMatrix,
    PotentialKaehler.hermitianPartMatrix_apply, PotentialKaehler.hermitianPart]

lemma hessian_realSMul (c : ℝ) (φ : SmoothRealFunction A)
    (i : Fin A.count) (z : Coordinates d) :
    (φ.realSMul c).hessian i z = (c : ℂ) • φ.hessian i z := by
  unfold hessian PotentialKaehler.potentialMatrix
  have he : (φ.realSMul c).localExpression i = c • φ.localExpression i := rfl
  rw [he, fderiv_const_smul_field (𝕜 := ℝ) (f := φ.localExpression i) c]
  rw [fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ (φ.localExpression i)) c]
  ext a b
  simp only [PotentialKaehler.hermitianPartMatrix_apply, Matrix.smul_apply]
  apply Complex.ext <;>
    simp [PotentialKaehler.hermitianPart, Pi.smul_apply, smul_eq_mul,
      Complex.mul_re, Complex.mul_im] <;> ring

end SmoothRealFunction

namespace KaehlerMetric

 

def linearizedMongeAmpere (g : KaehlerMetric A) (ψ : SmoothRealFunction A)
    (i : Fin A.count) (z : Coordinates d) : ℝ :=
  ((g.matrix i z)⁻¹ * ψ.hessian i z).trace.re

 
theorem mongeAmpere_directional_derivative (g : KaehlerMetric A)
    (ψ : SmoothRealFunction A) (i : Fin A.count) {z : Coordinates d}
    (hz : z ∈ (A.chart i).target) :
    HasDerivAt (fun t : ℝ =>
      Real.log ((g.matrix i z + (ψ.realSMul t).hessian i z).det.re) -
        Real.log (g.volumeCoefficient i z)) (g.linearizedMongeAmpere ψ i z) 0 := by
  simp only [SmoothRealFunction.hessian_realSMul]
  exact (MongeAmpere.hasDerivAt_logdet_add_smul _ _ (g.positive i z hz)).sub_const _

lemma linearizedMongeAmpere_constant (g : KaehlerMetric A) (c : ℝ) :
    g.linearizedMongeAmpere (SmoothRealFunction.constant c) = 0 := by
  funext i z
  simp [linearizedMongeAmpere, SmoothRealFunction.hessian_constant]

 

theorem linearizedMongeAmpere_not_injective [Nonempty X] (g : KaehlerMetric A) :
    ¬ Function.Injective g.linearizedMongeAmpere := by
  intro h
  have hc : SmoothRealFunction.constant (A := A) 0 = SmoothRealFunction.constant 1 :=
    h (by rw [linearizedMongeAmpere_constant, linearizedMongeAmpere_constant])
  let x : X := Classical.choice inferInstance
  have he := congrArg (fun φ : SmoothRealFunction A => φ.value x) hc
  simp [SmoothRealFunction.constant] at he

end KaehlerMetric
end Anticanonical.SourceSmooth

namespace EllipticKernel
open Filter Set
open scoped ContDiff

lemma second_deriv_nonpos_at_localMax {f : ℝ → ℝ} {x : ℝ}
    (hmax : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra h
  have hpos : 0 < deriv (deriv f) x := lt_of_not_ge h
  have hmin := isLocalMin_of_deriv_deriv_pos hpos hmax.deriv_eq_zero hc
  have he : f =ᶠ[nhds x] fun _ => f x := by
    filter_upwards [hmax, hmin] with y hy hy'
    exact le_antisymm hy hy'
  have hd : deriv f =ᶠ[nhds x] fun _ => 0 := by
    simpa using he.deriv
  have hdd : deriv (deriv f) x = 0 := by
    simpa using hd.deriv_eq
  exact (ne_of_gt hpos) hdd

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma second_fderiv_nonpos_at_localMax {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hmax : IsLocalMax f x) (v : E) :
    fderiv ℝ (fderiv ℝ f) x v v ≤ 0 := by
  let r : ℝ → E := fun t => x + t • v
  have hr : ContDiff ℝ ∞ r := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hr0 : r 0 = x := by simp [r]
  have hfr : ContDiffAt ℝ ∞ (f ∘ r) 0 := (show ContDiffAt ℝ ∞ f (r 0) by simpa only [hr0] using hf).comp 0 hr.contDiffAt
  have hmr : IsLocalMax (f ∘ r) 0 :=
    (hr0.symm ▸ hmax).comp_continuous hr.continuous.continuousAt
  have hle := second_deriv_nonpos_at_localMax hmr hfr.continuousAt
  have hd2 : deriv (deriv (f ∘ r)) 0 = fderiv ℝ (fderiv ℝ (f ∘ r)) 0 1 1 :=
    PotentialKaehler.fderiv_eval_derivative hfr 1 1
  rw [hd2, PotentialKaehler.second_derivative_comp hr.contDiffAt
    (by simpa only [hr0] using hf) 1 1] at hle
  have hDr : fderiv ℝ r = fun _ => ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) v := by
    funext t
    simpa [r] using
      ((hasFDerivAt_id t).smul_const v).const_add x |>.fderiv
  rw [hDr] at hle
  simpa [hr0] using hle

end EllipticKernel

namespace EllipticKernel
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.Elementwise ContDiff

lemma trace_mul_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  let S := CFC.sqrt A
  have hS : S.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hsquare : S * S = A := by simpa [S, pow_two] using CFC.sq_sqrt A hA.nonneg
  have htr := Complex.nonneg_iff.mp (hB.mul_mul_conjTranspose_same S).trace_nonneg
  have heq : (S * B * Sᴴ).trace = (A * B).trace := by
    rw [hS.isHermitian.eq, Matrix.trace_mul_cycle, hsquare]
  rw [heq] at htr
  exact htr.1

lemma negative_potentialMatrix_posSemidef_at_localMax {n : ℕ}
    {f : PotentialKaehler.V n → ℝ} {x : PotentialKaehler.V n}
    (hf : ContDiffAt ℝ ∞ f x) (hmax : IsLocalMax f x) :
    (-PotentialKaehler.potentialMatrix f x).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨(PotentialKaehler.potentialMatrix_hermitian hf).neg, ?_⟩
  intro v
  rw [neg_mulVec, dotProduct_neg]
  rw [PotentialKaehler.potentialMatrix,
    PotentialKaehler.hermitianPartMatrix_pair]
  apply Complex.nonneg_iff.mpr
  constructor
  · simp only [Complex.neg_re, PotentialKaehler.hermitianPart]
    have h1 := second_fderiv_nonpos_at_localMax hf hmax v
    have h2 := second_fderiv_nonpos_at_localMax hf hmax (Complex.I • v)
    linarith
  · simp only [Complex.neg_im, PotentialKaehler.hermitianPart]
    have hs := hf.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top) (Complex.I • v) v
    rw [hs]
    ring

lemma trace_potentialMatrix_nonpos_at_localMax {n : ℕ}
    {f : PotentialKaehler.V n → ℝ} {x : PotentialKaehler.V n}
    (hf : ContDiffAt ℝ ∞ f x) (hmax : IsLocalMax f x)
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    (H⁻¹ * PotentialKaehler.potentialMatrix f x).trace.re ≤ 0 := by
  have ht := trace_mul_nonneg hH.inv.posSemidef
    (negative_potentialMatrix_posSemidef_at_localMax hf hmax)
  simpa using ht

end EllipticKernel

 

noncomputable section
open Filter Set
open scoped ContDiff
namespace EllipticKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
abbrev Bilin (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →L[ℝ] E →L[ℝ] ℝ
abbrev SecondOrder (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  Bilin E →L[ℝ] ℝ

local instance barrierBilinNormedAddCommGroup : NormedAddCommGroup (Bilin E) := inferInstance
local instance barrierBilinNormedSpace : NormedSpace ℝ (Bilin E) := inferInstance

def realInner : Bilin E := innerSL ℝ (E := E)

lemma realInner_apply (u v : E) : realInner u v = inner ℝ u v := by
  exact innerSL_apply_apply ℝ u v

def rankOne (v : E) : Bilin E := (realInner v).smulRight (realInner v)
def barrier (α : ℝ) (y : E) (z : E) : ℝ := Real.exp (-α * ‖z-y‖^2)

lemma barrier_smooth (α : ℝ) (y : E) : ContDiff ℝ ∞ (barrier α y) :=
  (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ)).exp

lemma barrier_hasFDerivAt (α : ℝ) (y z : E) :
    HasFDerivAt (barrier α y)
      ((Real.exp (-α * ‖z-y‖^2) * (-2*α)) • realInner (z-y)) z := by
  have h := ((((hasFDerivAt_id z).sub_const y).norm_sq).const_mul (-α)).exp
  change HasFDerivAt (fun x => Real.exp (-α * ‖x-y‖^2)) _ z
  convert! h using 1
  ext v
  simp only [_root_.smul_apply, realInner_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, id_eq, innerSL_apply_apply, smul_eq_mul]
  ring

lemma barrier_fderiv (α : ℝ) (y : E) :
    fderiv ℝ (barrier α y) = fun z =>
      (Real.exp (-α * ‖z-y‖^2) * (-2*α)) • realInner (z-y) := by
  funext z
  exact (barrier_hasFDerivAt α y z).fderiv

lemma barrier_hessian (α : ℝ) (y z : E) :
    fderiv ℝ (fderiv ℝ (barrier α y)) z =
      Real.exp (-α * ‖z-y‖^2) •
        ((4*α^2) • rankOne (z-y) - (2*α) • (realInner (E := E))) := by
  rw [barrier_fderiv]
  have h₁ := (barrier_hasFDerivAt α y z).mul_const (-2*α)
  have h₂ := (realInner (E := E)).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const y)
  have hh := h₁.smul h₂
  have he := hh.fderiv
  simp only [Function.comp_def, id_eq] at he
  change fderiv ℝ (fun z => (barrier α y z * (-2*α)) • realInner (z-y)) z = _
  convert! he using 1
  ext u v
  simp [rankOne, barrier, realInner, ContinuousLinearMap.smulRight_apply]
  ring
end EllipticKernel

namespace EllipticKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local instance rankOneBilinNormedAddCommGroup : NormedAddCommGroup (Bilin E) := inferInstance
local instance rankOneBilinNormedSpace : NormedSpace ℝ (Bilin E) := inferInstance

lemma continuous_rankOne : Continuous (rankOne (E := E)) := by
  unfold rankOne
  exact ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).continuous.comp
    (realInner (E := E)).continuous).clm_apply (realInner (E := E)).continuous

 

lemma exists_positive_barrier {s : Set E} (hs : IsCompact s)
    (ℒ : E → SecondOrder E) (hℒ : ContinuousOn ℒ s) (y : E)
    (hpos : ∀ z ∈ s, 0 < ℒ z (rankOne (z-y))) :
    ∃ α : ℝ, 0 < α ∧ ∀ z ∈ s,
      0 < ℒ z (fderiv ℝ (fderiv ℝ (barrier α y)) z) := by
  by_cases hne : s.Nonempty
  · let a : E → ℝ := fun z => ℒ z (rankOne (z-y))
    let b : E → ℝ := fun z => ℒ z (realInner (E := E))
    have ha : ContinuousOn a s :=
      hℒ.clm_apply (continuous_rankOne.comp (continuous_id.sub continuous_const)).continuousOn
    have hb : ContinuousOn b s := hℒ.clm_apply continuousOn_const
    have hq : ContinuousOn (fun z => b z / (2*a z)) s :=
      hb.div (continuousOn_const.mul ha) (fun z hz => mul_ne_zero (by norm_num) (ne_of_gt (hpos z hz)))
    obtain ⟨z₀, hz₀, hmax⟩ := hs.exists_isMaxOn hne hq
    let α := max (b z₀ / (2*a z₀)) 0 + 1
    have hα : 0 < α := by dsimp [α]; positivity
    refine ⟨α, hα, ?_⟩
    intro z hz
    have haq : b z / (2*a z) < α := lt_of_le_of_lt (hmax hz)
      (by dsimp [α]; linarith [le_max_left (b z₀ / (2*a z₀)) 0])
    have haz : 0 < a z := hpos z hz
    have hba : b z < 2*α*a z := by
      have := (div_lt_iff₀ (by positivity : 0 < 2*a z)).mp haq
      nlinarith
    rw [barrier_hessian]
    simp only [map_smul, map_sub, smul_eq_mul]
    change 0 < Real.exp (-α*‖z-y‖^2) * (4*α^2 * a z - 2*α * b z)
    apply mul_pos (Real.exp_pos _)
    nlinarith [mul_pos hα (sub_pos.mpr hba)]
  · exact ⟨1, by norm_num, fun z hz => False.elim (hne ⟨z, hz⟩)⟩

end EllipticKernel

namespace EllipticKernel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma hessian_add {f g : E → ℝ} {z : E}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z) :
    fderiv ℝ (fderiv ℝ (f+g)) z =
      fderiv ℝ (fderiv ℝ f) z + fderiv ℝ (fderiv ℝ g) z := by
  have ef : ∀ᶠ x in nhds z, DifferentiableAt ℝ f x :=
    (((contDiffAt_infty.mp hf) 1).eventually (by simp)).mono
      (fun _ h => h.differentiableAt (by simp))
  have eg : ∀ᶠ x in nhds z, DifferentiableAt ℝ g x :=
    (((contDiffAt_infty.mp hg) 1).eventually (by simp)).mono
      (fun _ h => h.differentiableAt (by simp))
  have he : fderiv ℝ (f+g) =ᶠ[nhds z] (fderiv ℝ f + fderiv ℝ g) := by
    filter_upwards [ef, eg] with x hx hx'
    exact fderiv_add hx hx'
  rw [he.fderiv_eq]
  exact fderiv_add ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    ((hg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))

lemma hessian_add_smul_sub_const {f g : E → ℝ} {z : E}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z) (ε c : ℝ) :
    fderiv ℝ (fderiv ℝ (fun z => f z + ε * (g z-c))) z =
      fderiv ℝ (fderiv ℝ f) z + ε • fderiv ℝ (fderiv ℝ g) z := by
  change fderiv ℝ (fderiv ℝ (f + ε • (fun z => g z-c))) z = _
  rw [hessian_add hf (show ContDiffAt ℝ ∞ (ε • (fun z => g z-c)) z from
    (hg.sub contDiffAt_const).const_smul ε)]
  rw [fderiv_const_smul_field (𝕜 := ℝ) (f := fun z => g z-c) ε]
  rw [fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ (fun z => g z-c)) ε]
  have he : fderiv ℝ (fun z => g z-c) = fderiv ℝ g := by
    funext x; exact fderiv_sub_const c
  rw [he]
  rfl

end EllipticKernel

 
noncomputable section
open Set Filter Metric
namespace EllipticKernel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

omit [NormedSpace ℝ E] in
lemma annulus_le_of_no_localMax {u : E → ℝ} {y : E} {r M : ℝ}
    (hu : ContinuousOn u (closedBall y r \ ball y (r/2)))
    (hinner : ∀ z, dist z y = r/2 → u z ≤ M)
    (houter : ∀ z, dist z y = r → u z ≤ M)
    (hmax : ∀ z, r/2 < dist z y → dist z y < r → ¬IsLocalMax u z) :
    ∀ z ∈ closedBall y r \ ball y (r/2), u z ≤ M := by
  intro z hz
  have hc : IsCompact (closedBall y r \ ball y (r/2)) :=
    (isCompact_closedBall y r).diff isOpen_ball
  obtain ⟨p, hp, hpm⟩ := hc.exists_isMaxOn ⟨z, hz⟩ hu
  have hp₁ : dist p y ≤ r := hp.1
  have hp₂ : r/2 ≤ dist p y := le_of_not_gt hp.2
  have hbound : u p ≤ M := by
    by_cases hlow : dist p y = r/2
    · exact hinner p hlow
    by_cases hhigh : dist p y = r
    · exact houter p hhigh
    have hlow' : r/2 < dist p y := lt_of_le_of_ne hp₂ (Ne.symm hlow)
    have hhigh' : dist p y < r := lt_of_le_of_ne hp₁ hhigh
    have hn : closedBall y r \ ball y (r/2) ∈ nhds p := by
      have h₁ : {q : E | dist q y < r} ∈ nhds p :=
        (isOpen_lt (continuous_id.dist continuous_const) continuous_const).mem_nhds hhigh'
      have h₂ : {q : E | r/2 < dist q y} ∈ nhds p :=
        (isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds hlow'
      filter_upwards [h₁, h₂] with q hq₁ hq₂
      exact ⟨le_of_lt hq₁, not_lt_of_gt hq₂⟩
    exact False.elim (hmax p hlow' hhigh' (hpm.isLocalMax hn))
  exact le_trans (hpm hz) hbound

end EllipticKernel

namespace EllipticKernel
open Set Metric Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

 

omit [NormedSpace ℝ E] in
lemma tangent_ball {f : E → ℝ} {U : Set E} {x y : E} {δ M : ℝ}
    (hδ : 0 < δ) (hU : closedBall x δ ⊆ U) (hf : ContinuousOn f U)
    (hle : ∀ z ∈ U, f z ≤ M) (hx : f x = M)
    (hy : y ∈ ball x (δ/4)) (hyf : f y < M) :
    ∃ r : ℝ, 0 < r ∧ closedBall y r ⊆ U ∧
      (∀ z ∈ ball y r, f z < M) ∧
      ∃ p : E, dist p y = r ∧ f p = M := by
  let S := closedBall x (δ/2) ∩ f ⁻¹' {M}
  have hhalf : closedBall x (δ/2) ⊆ U :=
    subset_trans (closedBall_subset_closedBall (by linarith)) hU
  have hSclosed : IsClosed S :=
    (hf.mono hhalf).preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
  have hScompact : IsCompact S := (isCompact_closedBall x (δ/2)).of_isClosed_subset
    hSclosed inter_subset_left
  have hxS : x ∈ S := ⟨by simp only [mem_closedBall, dist_self]; linarith, hx⟩
  obtain ⟨p, hp, hmin⟩ := hScompact.exists_isMinOn ⟨x, hxS⟩
    (continuous_id.dist continuous_const).continuousOn
  let r := dist p y
  have hrle : r ≤ dist x y := hmin hxS
  have hye : dist y x < δ/4 := hy
  have hrsmall : r < δ/4 := lt_of_le_of_lt hrle (by simpa [dist_comm] using hye)
  have hpval : f p = M := hp.2
  have hpy : p ≠ y := by intro h; rw [h] at hpval; linarith
  have hr : 0 < r := dist_pos.mpr hpy
  have hsub : closedBall y r ⊆ closedBall x (δ/2) := by
    intro z hz
    have hz' : dist z y ≤ r := hz
    have htri := dist_triangle z y x
    show dist z x ≤ δ/2
    linarith
  refine ⟨r, hr, subset_trans hsub hhalf, ?_, p, rfl, hpval⟩
  intro z hz
  have hzhalf := hsub (ball_subset_closedBall hz)
  have hzU := hhalf hzhalf
  refine lt_of_le_of_ne (hle z hzU) ?_
  intro heq
  have hzS : z ∈ S := ⟨hzhalf, heq⟩
  have hzd : r ≤ dist z y := hmin hzS
  exact (not_lt_of_ge hzd) hz

end EllipticKernel

namespace EllipticKernel
open Set Filter Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
local instance tangentMaxBilinNormedAddCommGroup : NormedAddCommGroup (Bilin E) := inferInstance
local instance tangentMaxBilinNormedSpace : NormedSpace ℝ (Bilin E) := inferInstance

 

lemma no_tangent_max {f : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (ℒ : E → SecondOrder E) (hℒ : ContinuousOn ℒ U)
    (hell : ∀ z ∈ U, ∀ v : E, v ≠ 0 → 0 < ℒ z (rankOne v))
    (htest : ∀ z ∈ U, ∀ u : E → ℝ, ContDiffAt ℝ ∞ u z → IsLocalMax u z →
      ℒ z (fderiv ℝ (fderiv ℝ u) z) ≤ 0)
    (hharm : ∀ z ∈ U, ℒ z (fderiv ℝ (fderiv ℝ f) z) = 0)
    {M r : ℝ} {y p : E} (hle : ∀ z ∈ U, f z ≤ M)
    (hr : 0 < r) (hball : closedBall y r ⊆ U)
    (hstrict : ∀ z ∈ ball y r, f z < M)
    (hp : dist p y = r) (hfp : f p = M) : False := by
  let K := closedBall y r \ ball y (r/2)
  have hK : IsCompact K := (isCompact_closedBall y r).diff isOpen_ball
  have hKU : K ⊆ U := fun _ hz => hball hz.1
  obtain ⟨α, hα, hbar⟩ := exists_positive_barrier hK ℒ (hℒ.mono hKU) y (by
    intro z hz
    apply hell z (hKU hz)
    intro he
    have hzy : z = y := sub_eq_zero.mp he
    have hh : ¬dist z y < r/2 := hz.2
    rw [hzy, dist_self] at hh
    linarith)
  have hhalf : closedBall y (r/2) ⊆ ball y r := closedBall_subset_ball (by linarith)
  obtain ⟨q, hq, hqm⟩ := (isCompact_closedBall y (r/2)).exists_isMaxOn
    ⟨y, by simp only [mem_closedBall, dist_self]; linarith⟩
    (hf.continuousOn.mono (subset_trans hhalf (subset_trans ball_subset_closedBall hball)))
  have hqf : f q < M := hstrict q (hhalf hq)
  let ε := M - f q
  have hε : 0 < ε := sub_pos.mpr hqf
  let c := Real.exp (-α*r^2)
  let u : E → ℝ := fun z => f z + ε*(barrier α y z-c)
  have hus : ContDiffOn ℝ ∞ u U :=
    hf.add (contDiffOn_const.mul ((barrier_smooth α y).contDiffOn.sub contDiffOn_const))
  have hble : ∀ z : E, barrier α y z-c ≤ 1 := by
    intro z
    have he : barrier α y z ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
    have hc : 0 < c := Real.exp_pos _
    linarith
  have houter : ∀ z : E, dist z y = r → u z ≤ M := by
    intro z hz
    have hzU := hball (show z ∈ closedBall y r from le_of_eq hz)
    have hb : barrier α y z = c := by simp [barrier, ← dist_eq_norm, hz, c]
    simpa [u, hb] using hle z hzU
  have hinner : ∀ z : E, dist z y = r/2 → u z ≤ M := by
    intro z hz
    have hfz : f z ≤ f q := hqm (show z ∈ closedBall y (r/2) from le_of_eq hz)
    have hh := mul_le_mul_of_nonneg_left (hble z) hε.le
    dsimp [u, ε] at *
    linarith
  have hno : ∀ z, r/2 < dist z y → dist z y < r → ¬IsLocalMax u z := by
    intro z hz₁ hz₂ hm
    have hzK : z ∈ K := ⟨le_of_lt hz₂, not_lt_of_gt hz₁⟩
    have hzU := hKU hzK
    have hleu := htest z hzU u (hus.contDiffAt (hU.mem_nhds hzU)) hm
    have he : fderiv ℝ (fderiv ℝ u) z =
        fderiv ℝ (fderiv ℝ f) z + ε • fderiv ℝ (fderiv ℝ (barrier α y)) z :=
      hessian_add_smul_sub_const (hf.contDiffAt (hU.mem_nhds hzU))
        (barrier_smooth α y).contDiffAt ε c
    rw [he, map_add, map_smul, hharm z hzU, zero_add, smul_eq_mul] at hleu
    exact (not_lt_of_ge hleu) (mul_pos hε (hbar z hzK))
  have huK : ∀ z ∈ K, u z ≤ M := annulus_le_of_no_localMax
    (hus.continuousOn.mono hKU) hinner houter hno
  have hpU := hball (show p ∈ closedBall y r from le_of_eq hp)
  have hbp : barrier α y p = c := by simp [barrier, ← dist_eq_norm, hp, c]
  have hup : u p = M := by simp [u, hbp, hfp]
  have humax : IsLocalMax u p := by
    have hn : {z : E | r/2 < dist z y} ∈ nhds p :=
      (isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds
        (by change r/2 < dist p y; rw [hp]; linarith)
    filter_upwards [hU.mem_nhds hpU, hn] with z hzU hz
    rw [hup]
    by_cases hd : dist z y ≤ r
    · exact huK z ⟨hd, not_lt_of_gt hz⟩
    have hd' : r ≤ dist z y := le_of_lt (lt_of_not_ge hd)
    have hsq : r^2 ≤ ‖z-y‖^2 := by rw [← dist_eq_norm]; nlinarith [dist_nonneg (x := z) (y := y)]
    have hb : barrier α y z ≤ c := Real.exp_le_exp.mpr (by nlinarith)
    have hfz := hle z hzU
    have hh : ε * (barrier α y z-c) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε.le (sub_nonpos.mpr hb)
    dsimp [u]
    linarith
  have hfmax : IsLocalMax f p := by
    filter_upwards [hU.mem_nhds hpU] with z hz
    simpa [hfp] using hle z hz
  have hdu := (hf.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp) |>.hasFDerivAt
  have hdb := ((barrier_hasFDerivAt α y p).sub_const c).const_mul ε
  have he := (hdu.add hdb).fderiv
  change fderiv ℝ u p = _ at he
  rw [humax.fderiv_eq_zero, hfmax.fderiv_eq_zero] at he
  have hv := congrArg (fun L : E →L[ℝ] ℝ => L (p-y)) he
  have hn : ‖p-y‖^2 > 0 := by rw [← dist_eq_norm, hp]; positivity
  have hneg : ε * (Real.exp (-α*‖p-y‖^2) * (-2*α)) * ‖p-y‖^2 < 0 := by
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hε
      (mul_neg_of_pos_of_neg (Real.exp_pos _) (by linarith))) hn
  have hv' : 0 = ε * (Real.exp (-α*‖p-y‖^2) * (-2*α)) * ‖p-y‖^2 := by
    simpa only [_root_.smul_apply, _root_.zero_apply, zero_add, _root_.add_apply, realInner_apply,
      real_inner_self_eq_norm_sq, smul_eq_mul, mul_assoc] using hv
  linarith

end EllipticKernel

namespace EllipticKernel
open Set Filter Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
local instance harmonicMaxBilinNormedAddCommGroup : NormedAddCommGroup (Bilin E) := inferInstance
local instance harmonicMaxBilinNormedSpace : NormedSpace ℝ (Bilin E) := inferInstance

theorem harmonic_eventually_eq_of_max {f : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (ℒ : E → SecondOrder E) (hℒ : ContinuousOn ℒ U)
    (hell : ∀ z ∈ U, ∀ v : E, v ≠ 0 → 0 < ℒ z (rankOne v))
    (htest : ∀ z ∈ U, ∀ u : E → ℝ, ContDiffAt ℝ ∞ u z → IsLocalMax u z →
      ℒ z (fderiv ℝ (fderiv ℝ u) z) ≤ 0)
    (hharm : ∀ z ∈ U, ℒ z (fderiv ℝ (fderiv ℝ f) z) = 0)
    {x : E} {M : ℝ} (hx : x ∈ U) (hfx : f x = M) (hle : ∀ z ∈ U, f z ≤ M) :
    f =ᶠ[nhds x] fun _ => M := by
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let δ := a/2
  have hδ : 0 < δ := half_pos ha
  have hδU : closedBall x δ ⊆ U :=
    subset_trans (closedBall_subset_ball (by dsimp [δ]; linarith)) hball
  filter_upwards [ball_mem_nhds x (show 0 < δ/4 by positivity)] with y hy
  by_contra hyf
  have hyU : y ∈ U := hδU (mem_closedBall.mpr (by
    have h := mem_ball.mp hy
    linarith))
  have hlt : f y < M := lt_of_le_of_ne (hle y hyU) hyf
  obtain ⟨r, hr, hrU, hstrict, p, hp, hfp⟩ :=
    tangent_ball hδ hδU hf.continuousOn hle hfx hy hlt
  exact no_tangent_max hU hf ℒ hℒ hell htest hharm hle hr hrU hstrict hp hfp

end EllipticKernel

namespace EllipticKernel
open Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
abbrev EC (n : ℕ) := EuclideanSpace ℂ (Fin n)
variable {n : ℕ}
local instance coordinateBilinNormedAddCommGroup : NormedAddCommGroup (Bilin (EC n)) := inferInstance
local instance coordinateBilinNormedSpace : NormedSpace ℝ (Bilin (EC n)) := inferInstance

 

def coordinateEquiv (n : ℕ) : EC n ≃L[ℝ] PotentialKaehler.V n :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)

lemma coordinateEquiv_apply (z : EC n) : coordinateEquiv n z = WithLp.ofLp z := rfl
lemma coordinateEquiv_symm_apply (z : PotentialKaehler.V n) :
    (coordinateEquiv n).symm z = WithLp.toLp 2 z := rfl

def pullBilin (B : Bilin (EC n)) : PotentialKaehler.RealBilinear n :=
  ((B.comp (coordinateEquiv n).symm.toContinuousLinearMap).flip.comp
    (coordinateEquiv n).symm.toContinuousLinearMap).flip

lemma pullBilin_apply (B : Bilin (EC n)) (u v : PotentialKaehler.V n) :
    pullBilin B u v = B ((coordinateEquiv n).symm u) ((coordinateEquiv n).symm v) := rfl

lemma pullBilin_add (B C : Bilin (EC n)) : pullBilin (B+C) = pullBilin B + pullBilin C := by
  ext u v
  simp only [pullBilin_apply, _root_.add_apply]

lemma pullBilin_smul (c : ℝ) (B : Bilin (EC n)) : pullBilin (c • B) = c • pullBilin B := by
  ext u v
  simp only [pullBilin_apply, _root_.smul_apply]

lemma hermitianPartMatrix_add (B C : PotentialKaehler.RealBilinear n) :
    PotentialKaehler.hermitianPartMatrix (B+C) =
      PotentialKaehler.hermitianPartMatrix B + PotentialKaehler.hermitianPartMatrix C := by
  ext i j
  apply Complex.ext <;>
    simp [PotentialKaehler.hermitianPartMatrix_apply, PotentialKaehler.hermitianPart]
    <;> ring

lemma hermitianPartMatrix_smul (c : ℝ) (B : PotentialKaehler.RealBilinear n) :
    PotentialKaehler.hermitianPartMatrix (c • B) = c • PotentialKaehler.hermitianPartMatrix B := by
  ext i j
  apply Complex.ext <;>
    simp [PotentialKaehler.hermitianPartMatrix_apply, PotentialKaehler.hermitianPart]
    <;> ring

def traceBilinLinear (H : Matrix (Fin n) (Fin n) ℂ) : Bilin (EC n) →ₗ[ℝ] ℝ where
  toFun B := (H⁻¹ * PotentialKaehler.hermitianPartMatrix (pullBilin B)).trace.re
  map_add' B C := by rw [pullBilin_add, hermitianPartMatrix_add, mul_add, trace_add, Complex.add_re]
  map_smul' c B := by rw [pullBilin_smul, hermitianPartMatrix_smul, Matrix.mul_smul, trace_smul]; simp

def traceBilin (H : Matrix (Fin n) (Fin n) ℂ) : SecondOrder (EC n) :=
  (traceBilinLinear H).toContinuousLinearMap

lemma traceBilin_apply (H : Matrix (Fin n) (Fin n) ℂ) (B : Bilin (EC n)) :
    traceBilin H B = (H⁻¹ * PotentialKaehler.hermitianPartMatrix (pullBilin B)).trace.re := rfl

lemma traceBilin_continuousOn {U : Set (EC n)}
    (H : EC n → Matrix (Fin n) (Fin n) ℂ) (hH : ContinuousOn H U)
    (hpos : ∀ z ∈ U, (H z).PosDef) : ContinuousOn (fun z => traceBilin (H z)) U := by
  apply continuousOn_clm_apply.mpr
  intro B
  change ContinuousOn (fun z => ((H z)⁻¹ * PotentialKaehler.hermitianPartMatrix (pullBilin B)).trace.re) U
  have hi : ContinuousOn (fun z => (H z)⁻¹) U := by
    intro z hz
    apply (continuousAt_matrix_inv (H z) ?_).comp_continuousWithinAt (hH z hz)
    obtain ⟨u, hu⟩ := isUnit_iff_ne_zero.mpr (ne_of_gt (hpos z hz).det_pos)
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  apply Complex.continuous_re.comp_continuousOn
  unfold Matrix.trace
  apply continuousOn_finsetSum
  intro i hi'
  exact continuousOn_pi.mp (continuousOn_pi.mp (hi.mul continuousOn_const) i) i

lemma pullBilin_hessian {u : EC n → ℝ} {z : EC n} (hu : ContDiffAt ℝ ∞ u z) :
    pullBilin (fderiv ℝ (fderiv ℝ u) z) =
      fderiv ℝ (fderiv ℝ (u ∘ (coordinateEquiv n).symm)) (coordinateEquiv n z) := by
  let s := (coordinateEquiv n).symm
  have hu' : ContDiffAt ℝ ∞ u (s (coordinateEquiv n z)) := by simpa [s] using hu
  have hd : fderiv ℝ s = fun _ => s.toContinuousLinearMap := by
    funext w; exact s.hasFDerivAt.fderiv
  ext a b
  rw [PotentialKaehler.second_derivative_comp s.contDiff.contDiffAt hu' a b, hd]
  simp [pullBilin_apply, s]

lemma traceBilin_localMax (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    {u : EC n → ℝ} {z : EC n} (hu : ContDiffAt ℝ ∞ u z) (hmax : IsLocalMax u z) :
    traceBilin H (fderiv ℝ (fderiv ℝ u) z) ≤ 0 := by
  rw [traceBilin_apply, pullBilin_hessian hu]
  let s := (coordinateEquiv n).symm
  have hu' : ContDiffAt ℝ ∞ u (s (coordinateEquiv n z)) := by simpa [s] using hu
  have hm' : IsLocalMax u (s (coordinateEquiv n z)) := by simpa [s] using hmax
  exact trace_potentialMatrix_nonpos_at_localMax
    (hu'.comp _ s.contDiff.contDiffAt) (hm'.comp_continuous s.continuous.continuousAt) H hH

end EllipticKernel

namespace EllipticKernel
open Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise ContDiff
variable {n : ℕ}

lemma realInner_coordinate_single (v : EC n) (i : Fin n) (c : ℂ) :
    realInner v ((coordinateEquiv n).symm (Pi.single i c)) = (c * star (v i)).re := by
  rw [realInner_apply, coordinateEquiv_symm_apply, PiLp.inner_apply]
  simp [Pi.single_apply, apply_ite Complex.re, Complex.inner]

lemma pull_rankOne (v : EC n) :
    PotentialKaehler.hermitianPartMatrix (pullBilin (rankOne v)) =
      (1/4 : ℝ) • Matrix.vecMulVec (coordinateEquiv n v) (star (coordinateEquiv n v)) := by
  ext i j
  apply Complex.ext <;>
    simp [PotentialKaehler.hermitianPartMatrix_apply, PotentialKaehler.hermitianPart,
      pullBilin_apply, rankOne, ContinuousLinearMap.smulRight_apply,
      realInner_coordinate_single, ← Pi.single_smul, coordinateEquiv_apply,
      Complex.mul_re, Complex.mul_im, Matrix.vecMulVec_apply] <;> ring

lemma traceBilin_symbol (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (v : EC n) (hv : v ≠ 0) : 0 < traceBilin H (rankOne v) := by
  have hve : coordinateEquiv n v ≠ 0 := by
    intro h
    apply hv
    exact (coordinateEquiv n).injective (by simpa using h)
  have hp := MongeAmpere.linearized_symbol_pos H hH (coordinateEquiv n v) hve
  rw [traceBilin_apply, pull_rankOne, Matrix.mul_smul, trace_smul]
  simpa only [Complex.smul_re, smul_eq_mul] using mul_pos (by norm_num : (0 : ℝ) < 1/4) hp

end EllipticKernel

namespace Anticanonical.SourceSmooth
open EllipticKernel Set Filter
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma SmoothRealFunction.continuous (φ : SmoothRealFunction A) : Continuous φ.value := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨i, hi⟩ := A.covers x
  have hci : ContinuousAt (φ.localExpression i) (A.chart i x) :=
    ((φ.smooth i).contDiffAt ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hi))).continuousAt
  apply (hci.comp ((A.chart i).continuousAt hi)).congr_of_eventuallyEq
  filter_upwards [(A.chart i).eventually_left_inverse hi] with y hy
  simp [SmoothRealFunction.localExpression, hy]

lemma SmoothRealFunction.euclidean_smooth (φ : SmoothRealFunction A) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (φ.localExpression i ∘ coordinateEquiv d)
      ((coordinateEquiv d) ⁻¹' (A.chart i).target) :=
  (φ.smooth i).comp (coordinateEquiv d).contDiff.contDiffOn (fun _ h => h)

lemma KaehlerMetric.traceBilin_localExpression (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (i : Fin A.count) {z : EC d} (hz : coordinateEquiv d z ∈ (A.chart i).target) :
    traceBilin (g.matrix i (coordinateEquiv d z))
      (fderiv ℝ (fderiv ℝ (φ.localExpression i ∘ coordinateEquiv d)) z) =
        g.linearizedMongeAmpere φ i (coordinateEquiv d z) := by
  have hu := (φ.euclidean_smooth i).contDiffAt
    (((A.chart i).open_target.preimage (coordinateEquiv d).continuous).mem_nhds hz)
  have he : (φ.localExpression i ∘ coordinateEquiv d) ∘ (coordinateEquiv d).symm =
      φ.localExpression i := by
    funext w
    simp
  rw [traceBilin_apply, pullBilin_hessian hu, he]
  rfl

 

lemma KaehlerMetric.harmonic_eventually_constant (g : KaehlerMetric A)
    (φ : SmoothRealFunction A)
    (hφ : ∀ (i : Fin A.count) (z : Coordinates d), z ∈ (A.chart i).target →
      g.linearizedMongeAmpere φ i z = 0)
    {x : X} {M : ℝ} (hx : φ.value x = M) (hmax : ∀ y : X, φ.value y ≤ M) :
    φ.value =ᶠ[nhds x] fun _ => M := by
  obtain ⟨i, hi⟩ := A.covers x
  let e := coordinateEquiv d
  let U := e ⁻¹' (A.chart i).target
  let u := φ.localExpression i ∘ e
  let H := fun z => g.matrix i (e z)
  have hU : IsOpen U := (A.chart i).open_target.preimage e.continuous
  have hu : ContDiffOn ℝ ∞ u U := φ.euclidean_smooth i
  have hH : ContinuousOn H U :=
    (g.smooth i).continuousOn.comp e.continuous.continuousOn (fun _ h => h)
  have hp : ∀ z ∈ U, (H z).PosDef := fun z hz => g.positive i (e z) hz
  have hh : ∀ z ∈ U, traceBilin (H z) (fderiv ℝ (fderiv ℝ u) z) = 0 := by
    intro z hz
    exact (g.traceBilin_localExpression φ i hz).trans (hφ i (e z) hz)
  have hz : e.symm (A.chart i x) ∈ U := by
    simpa [U] using (A.chart i).map_source hi
  have hux : u (e.symm (A.chart i x)) = M := by
    simpa [u, SmoothRealFunction.localExpression, (A.chart i).left_inv hi] using hx
  have heq := harmonic_eventually_eq_of_max hU hu (fun z => traceBilin (H z))
    (traceBilin_continuousOn H hH hp)
    (fun z hz v hv => traceBilin_symbol (H z) (hp z hz) v hv)
    (fun z hz u hu hm => traceBilin_localMax (H z) (hp z hz) hu hm)
    hh hz hux (fun z _ => hmax ((A.chart i).symm (e z)))
  have ht : Tendsto (fun y => e.symm (A.chart i y)) (nhds x)
      (nhds (e.symm (A.chart i x))) :=
    e.symm.continuous.continuousAt.comp ((A.chart i).continuousAt hi)
  filter_upwards [ht.eventually heq, (A.chart i).eventually_left_inverse hi] with y hy hiy
  simpa [u, SmoothRealFunction.localExpression, hiy] using hy

 

theorem linearizedMongeAmpere_kernel (d : ℕ) (X : Type*) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] (A : ComplexAtlas d X)
    (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (hφ : ∀ (i : Fin A.count) (z : Coordinates d), z ∈ (A.chart i).target →
      g.linearizedMongeAmpere φ i z = 0) :
    ∃ c : ℝ, ∀ x : X, φ.value x = c := by
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty φ.continuous.continuousOn
  have hmax : ∀ y, φ.value y ≤ φ.value x := fun y => hx (mem_univ y)
  let S := {y : X | φ.value y = φ.value x}
  have hs : IsClosed S := isClosed_eq φ.continuous continuous_const
  have ho : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    exact g.harmonic_eventually_constant φ hφ hy hmax
  have hall : S = univ := (show IsClopen S from ⟨hs, ho⟩).eq_univ ⟨x, rfl⟩
  exact ⟨φ.value x, fun y => show y ∈ S from hall ▸ mem_univ y⟩

end Anticanonical.SourceSmooth

namespace Anticanonical.SourceSmooth
open Set Filter
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

namespace SmoothRealFunction
 
def normalizeAt (φ : SmoothRealFunction A) (x₀ : X) : SmoothRealFunction A where
  value x := φ.value x - φ.value x₀
  smooth i := (φ.smooth i).sub contDiffOn_const

@[simp] lemma normalizeAt_value (φ : SmoothRealFunction A) (x₀ : X) :
    (φ.normalizeAt x₀).value x₀ = 0 := sub_self _

lemma hessian_normalizeAt (φ : SmoothRealFunction A) (x₀ : X) :
    (φ.normalizeAt x₀).hessian = φ.hessian := by
  funext i z
  have he : (φ.normalizeAt x₀).localExpression i =
      fun w => φ.localExpression i w - φ.value x₀ := rfl
  have hd : fderiv ℝ (fun w => φ.localExpression i w - φ.value x₀) =
      fderiv ℝ (φ.localExpression i) := by
    funext w; exact fderiv_sub_const _
  simp only [hessian, he, PotentialKaehler.potentialMatrix, hd]
end SmoothRealFunction

namespace KaehlerMetric
lemma linearizedMongeAmpere_realSMul (g : KaehlerMetric A)
    (φ : SmoothRealFunction A) (c : ℝ) (i : Fin A.count) (z : Coordinates d) :
    g.linearizedMongeAmpere (φ.realSMul c) i z = c * g.linearizedMongeAmpere φ i z := by
  simp only [linearizedMongeAmpere, SmoothRealFunction.hessian_realSMul,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

lemma linearizedMongeAmpere_normalizeAt (g : KaehlerMetric A)
    (φ : SmoothRealFunction A) (x₀ : X) :
    g.linearizedMongeAmpere (φ.normalizeAt x₀) = g.linearizedMongeAmpere φ := by
  funext i z
  unfold linearizedMongeAmpere
  rw [SmoothRealFunction.hessian_normalizeAt]

lemma linearized_nonpos_at_globalMax (g : KaehlerMetric A)
    (φ : SmoothRealFunction A) {x : X} (hx : ∀ y : X, φ.value y ≤ φ.value x)
    (i : Fin A.count) (hi : x ∈ (A.chart i).source) :
    g.linearizedMongeAmpere φ i (A.chart i x) ≤ 0 := by
  have hs := (φ.smooth i).contDiffAt
    ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hi))
  have hm : IsLocalMax (φ.localExpression i) (A.chart i x) := by
    apply Filter.Eventually.of_forall
    intro z
    simpa [SmoothRealFunction.localExpression, (A.chart i).left_inv hi] using
      hx ((A.chart i).symm z)
  exact EllipticKernel.trace_potentialMatrix_nonpos_at_localMax hs hm _
    (g.positive i _ ((A.chart i).map_source hi))

 

theorem no_positive_constant_rhs [CompactSpace X] [Nonempty X]
    (g : KaehlerMetric A) (φ : SmoothRealFunction A) {c : ℝ} (hc : 0 < c) :
    ¬ (∀ i z, z ∈ (A.chart i).target → g.linearizedMongeAmpere φ i z = c) := by
  intro h
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn univ_nonempty φ.continuous.continuousOn
  obtain ⟨i, hi⟩ := A.covers x
  have hn := g.linearized_nonpos_at_globalMax φ (fun y => hx (mem_univ y)) i hi
  rw [h i _ ((A.chart i).map_source hi)] at hn
  exact not_le_of_gt hc hn

 

lemma constant_rhs_eq_zero [CompactSpace X] [Nonempty X]
    (g : KaehlerMetric A) (φ : SmoothRealFunction A) {c : ℝ}
    (hc : ∀ i z, z ∈ (A.chart i).target → g.linearizedMongeAmpere φ i z = c) : c = 0 := by
  have hn : c ≤ 0 := le_of_not_gt (fun h => g.no_positive_constant_rhs φ h hc)
  have hp : 0 ≤ c := by
    by_contra h
    have hc' : 0 < -c := by linarith
    apply g.no_positive_constant_rhs (φ.realSMul (-1)) hc'
    intro i z hz
    rw [linearizedMongeAmpere_realSMul, hc i z hz]
    ring
  exact le_antisymm hn hp

 

theorem normalized_augmented_kernel [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (g : KaehlerMetric A) (φ : SmoothRealFunction A) (x₀ : X) (c : ℝ)
    (hx : φ.value x₀ = 0)
    (he : ∀ i z, z ∈ (A.chart i).target → g.linearizedMongeAmpere φ i z + c = 0) :
    c = 0 ∧ ∀ x, φ.value x = 0 := by
  have hc : -c = 0 := g.constant_rhs_eq_zero φ (by
    intro i z hz
    linarith [he i z hz])
  have hc₀ : c = 0 := neg_eq_zero.mp hc
  obtain ⟨k, hk⟩ := linearizedMongeAmpere_kernel d X A g φ (by
    intro i z hz
    simpa [hc₀] using he i z hz)
  refine ⟨hc₀, fun x => ?_⟩
  rw [hk x, ← hk x₀, hx]
end KaehlerMetric

 

def HasNormalizedPoissonSolution {d : ℕ} {X : Type*} [TopologicalSpace X]
    {A : ComplexAtlas d X} (g : KaehlerMetric A) (x₀ : X)
    (f : SmoothRealFunction A) : Prop :=
  ∃ (φ : SmoothRealFunction A) (c : ℝ), φ.value x₀ = 0 ∧
    ∀ i z, z ∈ (A.chart i).target →
      g.linearizedMongeAmpere φ i z + c = f.localExpression i z

end Anticanonical.SourceSmooth

end
end
end
end
end
end
end
end

end OAI
