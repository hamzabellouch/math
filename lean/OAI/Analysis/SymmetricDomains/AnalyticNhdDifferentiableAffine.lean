import Mathlib
import OAI.Analysis.SymmetricDomains.ContinuityPrinciple

namespace OAI


namespace Release061
open Set Filter Metric
open scoped Topology

theorem gaussian_peak_square_bound {Y : Type*} [PseudoMetricSpace Y]
    {a : ℂ} {p q : Y}
    (hpeak : ‖a‖ ≤ Real.exp (-(dist q p)^2))
    (hclose : ‖1-a‖ ≤ 1/2) : (dist q p)^2 ≤ 2*‖1-a‖ := by
  have htri : 1 ≤ ‖1-a‖ + ‖a‖ := by
    simpa using norm_le_norm_sub_add (1 : ℂ) a
  have hhalf : 1/2 ≤ ‖a‖ := by linarith
  have ha : 0 < ‖a‖ := by linarith
  have hlog : Real.log ‖a‖ ≤ -(dist q p)^2 := by
    simpa using Real.log_le_log ha hpeak
  have hinv : -Real.log ‖a‖ ≤ ‖a‖⁻¹-1 := by
    simpa only [Real.log_inv] using Real.log_le_sub_one_of_pos (inv_pos.mpr ha)
  have hb : (‖a‖⁻¹-1)*‖a‖ = 1-‖a‖ := by
    rw [sub_mul, inv_mul_cancel₀ ha.ne', one_mul]
  have hnonneg : 0 ≤ (dist q p)^2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right (le_trans (neg_le_neg hlog) hinv) ha.le
  rw [neg_neg,hb] at hmul
  nlinarith

end Release061

open Set Metric Complex
open scoped Topology

namespace Release061

abbrev RadiusCircle (R : ℝ) := {z : ℂ // z ∈ sphere (0 : ℂ) R}

instance radiusCircleCompact (R : ℝ) : CompactSpace (RadiusCircle R) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : ℂ) R)

noncomputable def circleExtend {R : ℝ} (f : C(RadiusCircle R, ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if h : z ∈ sphere (0 : ℂ) R then f ⟨z, h⟩ else 0

@[simp] theorem circleExtend_on {R : ℝ} (f : C(RadiusCircle R, ℂ))
    (z : RadiusCircle R) : circleExtend f z = f z := by
  simp [circleExtend]

theorem continuousOn_circleExtend {R : ℝ} (f : C(RadiusCircle R, ℂ)) :
    ContinuousOn (circleExtend f) (sphere (0 : ℂ) R) := by
  rw [continuousOn_iff_continuous_domRestrict]
  simpa only [Set.domRestrict_def, circleExtend_on, Set.domRestrict_apply] using f.continuous

noncomputable def circleIntegralLM (R : ℝ) (hR : 0 ≤ R) :
    C(RadiusCircle R, ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∮ z in C(0, R), circleExtend f z
  map_add' f g := by
    rw [show circleExtend (f + g) = fun z => circleExtend f z + circleExtend g z by
      funext z; simp only [circleExtend]; split_ifs <;> simp]
    exact circleIntegral.integral_add
      ((continuousOn_circleExtend f).circleIntegrable hR)
      ((continuousOn_circleExtend g).circleIntegrable hR)
  map_smul' a f := by
    rw [show circleExtend (a • f) = fun z => a • circleExtend f z by
      funext z; simp only [circleExtend]; split_ifs <;> simp]
    exact circleIntegral.integral_smul a _ _ _

noncomputable def circleIntegralCLM (R : ℝ) (hR : 0 ≤ R) :
    C(RadiusCircle R, ℂ) →L[ℂ] ℂ :=
  (circleIntegralLM R hR).mkContinuous (2 * Real.pi * R) (by
    intro f
    exact circleIntegral.norm_integral_le_of_norm_le_const hR (fun z hz => by
      simpa only [circleExtend, dite_eq_left hz] using f.norm_coe_le_norm ⟨z,hz⟩))

@[simp] theorem circleIntegralCLM_apply {R : ℝ} (hR : 0 ≤ R)
    (f : C(RadiusCircle R, ℂ)) :
    circleIntegralCLM R hR f = ∮ z in C(0,R), circleExtend f z := rfl

noncomputable def cauchyFunctional (R : ℝ) (hR : 0 ≤ R) :
    C(RadiusCircle R, ℂ) →L[ℂ] ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ • circleIntegralCLM R hR

@[simp] theorem cauchyFunctional_apply {R : ℝ} (hR : 0 ≤ R)
    (f : C(RadiusCircle R, ℂ)) :
    cauchyFunctional R hR f =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(0,R), circleExtend f z := rfl

noncomputable def curryCLM (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace (X × Y)] : C(X × Y, ℂ) →L[ℂ] C(X, C(Y, ℂ)) where
  toFun := ContinuousMap.curry
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := ContinuousMap.continuous_curry

theorem continuousMap_ringInverse_apply {X : Type*} [TopologicalSpace X]
    (f : C(X, ℂ)) (hf : ∀ x, f x ≠ 0) (x : X) :
    Ring.inverse f x = (f x)⁻¹ := by
  let u := (ContinuousMap.isUnit_iff_forall_ne_zero f).mpr hf |>.unit
  have hu : (u : C(X,ℂ)) = f := IsUnit.unit_spec _
  rw [← hu, Ring.inverse_unit]
  have hm := congrArg (fun g : C(X,ℂ) => g x) (Units.inv_mul u)
  change (↑u⁻¹ : C(X,ℂ)) x * (u : C(X,ℂ)) x = 1 at hm
  exact eq_inv_of_mul_eq_one_left hm

def joinTorus {R : ℝ} (n : ℕ) :
    C(RadiusCircle R × (Fin n → RadiusCircle R), Fin (n+1) → RadiusCircle R) where
  toFun u := Fin.cons u.1 u.2
  continuous_toFun := by
    apply continuous_pi
    intro j
    induction j using Fin.cases with
    | zero => exact continuous_fst
    | succ i => exact (continuous_apply i).comp continuous_snd

noncomputable def iteratedCauchyFunctional (R : ℝ) (hR : 0 ≤ R) :
    (n : ℕ) → C((Fin n → RadiusCircle R), ℂ) →L[ℂ] ℂ
  | 0 => ContinuousMap.evalCLM ℂ (Fin.elim0)
  | n+1 => (cauchyFunctional R hR).comp
      ((ContinuousLinearMap.compLeftContinuous ℂ (RadiusCircle R)
          (iteratedCauchyFunctional R hR n)).comp
        ((curryCLM (RadiusCircle R) (Fin n → RadiusCircle R)).comp
          (ContinuousMap.compCLM ℂ ℂ (joinTorus n))))

@[simp] theorem iteratedCauchyFunctional_zero (R : ℝ) (hR : 0 ≤ R)
    (f : C((Fin 0 → RadiusCircle R), ℂ)) :
    iteratedCauchyFunctional R hR 0 f = f Fin.elim0 := rfl

@[simp] theorem iteratedCauchyFunctional_succ (R : ℝ) (hR : 0 ≤ R) (n : ℕ)
    (f : C((Fin (n+1) → RadiusCircle R), ℂ)) :
    iteratedCauchyFunctional R hR (n+1) f = cauchyFunctional R hR
      ((ContinuousLinearMap.compLeftContinuous ℂ (RadiusCircle R)
        (iteratedCauchyFunctional R hR n)) ((f.comp (joinTorus n)).curry)) := rfl

lemma fin_cons_continuous {X : Type*} [TopologicalSpace X]
    {n : ℕ} {f : X → ℂ} {g : X → Fin n → ℂ}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => (Fin.cons (f x) (g x) : Fin (n+1) → ℂ)) := by
  apply continuous_pi
  intro j
  induction j using Fin.cases with
  | zero => exact hf
  | succ j => exact (continuous_apply j).comp hg

lemma fin_cons_differentiable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} {f : E → ℂ} {g : E → Fin n → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    Differentiable ℂ (fun x => (Fin.cons (f x) (g x) : Fin (n+1) → ℂ)) := by
  apply differentiable_pi.mpr
  intro j
  induction j using Fin.cases with
  | zero => exact hf
  | succ j =>
      simpa only [Fin.cons_succ, Function.comp_def] using
        (differentiable_apply j : Differentiable ℂ (fun y : Fin n → ℂ => y j)).comp hg

lemma fin_cons_mem_closedBall {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    {w : ℂ} {y : Fin n → ℂ} (hw : w ∈ closedBall (0 : ℂ) R)
    (hy : y ∈ closedBall (0 : Fin n → ℂ) R) :
    Fin.cons w y ∈ closedBall (0 : Fin (n+1) → ℂ) R := by
  simp only [mem_closedBall, dist_zero_right] at *
  rw [pi_norm_le_iff_of_nonneg hR] at *
  intro j
  induction j using Fin.cases with
  | zero => exact hw
  | succ j => exact hy j

theorem iteratedCauchy_formula (n : ℕ) {R : ℝ} (hR : 0 < R)
    {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (closedBall 0 R))
    {x : Fin n → ℂ} (hx : x ∈ ball 0 R)
    (G : C((Fin n → RadiusCircle R), ℂ))
    (hG : ∀ ζ, G ζ = f (fun j => (ζ j : ℂ)) * ∏ j, ((ζ j : ℂ) - x j)⁻¹) :
    iteratedCauchyFunctional R hR.le n G = f x := by
  induction n with
  | zero =>
      rw [iteratedCauchyFunctional_zero, hG]
      simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
      congr 1
      exact Subsingleton.elim _ _
  | succ n ih =>
      rw [iteratedCauchyFunctional_succ, cauchyFunctional_apply]
      let H := (ContinuousLinearMap.compLeftContinuous ℂ (RadiusCircle R)
        (iteratedCauchyFunctional R hR.le n)) ((G.comp (joinTorus n)).curry)
      have hx' : ∀ j, ‖x j‖ < R := (pi_norm_lt_iff hR).mp (by simpa using hx)
      have htail : Fin.tail x ∈ ball (0 : Fin n → ℂ) R := by
        simpa only [mem_ball, dist_zero_right, pi_norm_lt_iff hR, Fin.tail] using fun j : Fin n => hx' j.succ
      have hslice : ∀ w : RadiusCircle R,
          H w = ((w : ℂ) - x 0)⁻¹ * f (Fin.cons (w : ℂ) (Fin.tail x)) := by
        intro w
        change iteratedCauchyFunctional R hR.le n ((G.comp (joinTorus n)).curry w) = _
        apply ih (f := fun y => ((w : ℂ) - x 0)⁻¹ * f (Fin.cons (w : ℂ) y)) _ htail
        · intro ζ
          change G (Fin.cons w ζ) = _
          rw [hG, Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail]
          have hcast : (fun j : Fin (n+1) => ((Fin.cons w ζ : Fin (n+1) → RadiusCircle R) j : ℂ)) =
              (Fin.cons (w : ℂ) (fun j => (ζ j : ℂ)) : Fin (n+1) → ℂ) := by
            funext j
            induction j using Fin.cases with
            | zero => rfl
            | succ _ => rfl
          rw [hcast]
          ring
        · exact (differentiableOn_const _).mul
            (hf.comp (fin_cons_differentiable (differentiable_const (w : ℂ))
              differentiable_id).differentiableOn
              (fun y hy => fin_cons_mem_closedBall hR.le (sphere_subset_closedBall w.property) hy))
      have hext : EqOn (circleExtend H)
          (fun w : ℂ => (w - x 0)⁻¹ • f (Fin.cons w (Fin.tail x))) (sphere 0 R) := by
        intro w hw
        simpa only [circleExtend, dite_eq_left hw, smul_eq_mul] using hslice ⟨w,hw⟩
      rw [circleIntegral.integral_congr hR.le hext]
      have hd : DifferentiableOn ℂ (fun w => f (Fin.cons w (Fin.tail x))) (closedBall 0 R) :=
        hf.comp (fin_cons_differentiable differentiable_id
          (differentiable_const (Fin.tail x))).differentiableOn
          (fun w hw => fin_cons_mem_closedBall hR.le hw (ball_subset_closedBall htail))
      have hc := hd.mono closure_ball_subset_closedBall |>.diffContOnCl
      have hcf := hc.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (by simpa using hx' 0)
      change _ = f (Fin.cons (x 0) (Fin.tail x)) at hcf
      rw [Fin.cons_self_tail x] at hcf
      exact hcf

def torusVal (n : ℕ) (R : ℝ) : C((Fin n → RadiusCircle R), Fin n → ℂ) where
  toFun ζ j := ζ j
  continuous_toFun := continuous_pi (fun j => continuous_subtype_val.comp (continuous_apply j))

lemma torusVal_mem_closedBall {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (ζ : Fin n → RadiusCircle R) : torusVal n R ζ ∈ closedBall 0 R := by
  rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
  intro j
  exact (by simpa only [mem_sphere, dist_zero_right] using (ζ j).property : ‖(ζ j : ℂ)‖ = R).le

noncomputable def torusBoundary {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (f : (Fin n → ℂ) → ℂ) (hf : ContinuousOn f (closedBall 0 R)) :
    C((Fin n → RadiusCircle R), ℂ) :=
  ⟨f ∘ torusVal n R, hf.comp_continuous (torusVal n R).continuous (torusVal_mem_closedBall hR)⟩

def torusCoordinate {n : ℕ} {R : ℝ} (j : Fin n) : C((Fin n → RadiusCircle R), ℂ) :=
  ⟨fun ζ => ζ j, continuous_subtype_val.comp (continuous_apply j)⟩

noncomputable def torusResolvent {n : ℕ} {R : ℝ} (j : Fin n) (x : Fin n → ℂ) :
    C((Fin n → RadiusCircle R), ℂ) :=
  Ring.inverse (torusCoordinate j - ContinuousMap.const _ (x j))

lemma torus_difference_ne_zero {n : ℕ} {R : ℝ} (hR : 0 < R)
    {x : Fin n → ℂ} (hx : x ∈ ball 0 R) (j : Fin n) (ζ : Fin n → RadiusCircle R) :
    ((torusCoordinate (R := R) j - ContinuousMap.const _ (x j)) :
      C((Fin n → RadiusCircle R), ℂ)) ζ ≠ 0 := by
  change (ζ j : ℂ) - x j ≠ 0
  have hxi := (pi_norm_lt_iff hR).mp (by simpa using hx) j
  have hz : ‖(ζ j : ℂ)‖ = R := by simpa only [mem_sphere, dist_zero_right] using (ζ j).property
  intro he
  rw [sub_eq_zero.mp he] at hz
  exact (ne_of_lt hxi) hz

lemma torusResolvent_apply {n : ℕ} {R : ℝ} (hR : 0 < R)
    {x : Fin n → ℂ} (hx : x ∈ ball 0 R) (j : Fin n) (ζ : Fin n → RadiusCircle R) :
    torusResolvent (R := R) j x ζ = ((ζ j : ℂ) - x j)⁻¹ :=
  continuousMap_ringInverse_apply _ (torus_difference_ne_zero hR hx j) ζ

lemma analyticAt_torusResolvent {n : ℕ} {R : ℝ} (hR : 0 < R)
    {x : Fin n → ℂ} (hx : x ∈ ball 0 R) (j : Fin n) :
    AnalyticAt ℂ (torusResolvent (R := R) j) x := by
  have hu := (ContinuousMap.isUnit_iff_forall_ne_zero
    (torusCoordinate (R := R) j - ContinuousMap.const _ (x j))).mpr
    (torus_difference_ne_zero hR hx j)
  have ha : AnalyticAt ℂ
      (fun y : Fin n → ℂ => torusCoordinate (R := R) j - ContinuousMap.const _ (y j)) x :=
    analyticAt_const.sub (((ContinuousLinearMap.const ℂ (Fin n → RadiusCircle R)).comp
      (ContinuousLinearMap.proj j)).analyticAt x)
  have hi : AnalyticAt ℂ Ring.inverse
      (torusCoordinate (R := R) j - ContinuousMap.const _ (x j)) :=
    analyticOnNhd_inverse _ hu
  have hh := hi.comp (f := fun y : Fin n → ℂ => torusCoordinate (R := R) j - ContinuousMap.const _ (y j)) ha
  exact hh

noncomputable def cauchyTransform {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (B : C((Fin n → RadiusCircle R), ℂ)) (x : Fin n → ℂ) : ℂ :=
  iteratedCauchyFunctional R hR n (B * ∏ j, torusResolvent j x)

lemma analyticAt_cauchyTransform {n : ℕ} {R : ℝ} (hR : 0 < R)
    (B : C((Fin n → RadiusCircle R), ℂ)) {x : Fin n → ℂ} (hx : x ∈ ball 0 R) :
    AnalyticAt ℂ (cauchyTransform hR.le B) x := by
  have hp : AnalyticAt ℂ (fun y : Fin n → ℂ => ∏ j, torusResolvent (R := R) j y) x := by
    simpa only [Finset.prod_fn] using Finset.univ.analyticAt_prod
      (fun j _ => analyticAt_torusResolvent hR hx j)
  exact ((iteratedCauchyFunctional R hR.le n).analyticAt _).comp (analyticAt_const.mul hp)

lemma cauchyTransform_eq {n : ℕ} {R : ℝ} (hR : 0 < R)
    {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (closedBall 0 R))
    {x : Fin n → ℂ} (hx : x ∈ ball 0 R) :
    cauchyTransform hR.le (torusBoundary hR.le f hf.continuousOn) x = f x := by
  apply iteratedCauchy_formula n hR hf hx
  intro ζ
  simp only [ContinuousMap.mul_apply, ContinuousMap.prod_apply, torusResolvent_apply hR hx]
  rfl

theorem analyticAt_of_differentiableOn_closedBall {n : ℕ} {R : ℝ} (hR : 0 < R)
    {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (closedBall 0 R))
    {x : Fin n → ℂ} (hx : x ∈ ball 0 R) : AnalyticAt ℂ f x := by
  apply (analyticAt_cauchyTransform hR (torusBoundary hR.le f hf.continuousOn) hx).congr
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  exact cauchyTransform_eq hR hf hy

theorem analyticOnNhd_of_differentiableOn_finite {n : ℕ} {S : Set (Fin n → ℂ)}
    (hS : IsOpen S) {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f S) :
    AnalyticOnNhd ℂ f S := by
  intro x hx
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hx)
  have hmaps : MapsTo (fun y => x + y) (closedBall (0 : Fin n → ℂ) (r/2)) S := by
    intro y hy
    apply hrs
    rw [mem_ball, dist_eq_norm]
    simpa only [add_sub_cancel_left] using
      lt_of_le_of_lt (by simpa only [mem_closedBall, dist_zero_right] using hy) (by linarith : r/2 < r)
  have hd := hf.comp ((differentiable_const x).add differentiable_id).differentiableOn hmaps
  have ha := analyticAt_of_differentiableOn_closedBall (half_pos hr) hd (mem_ball_self (half_pos hr))
  change AnalyticAt ℂ (fun y => f (x+y)) 0 at ha
  have ha' : AnalyticAt ℂ (fun y => f (x+y)) (x-x) := by simpa only [sub_self] using ha
  have hcomp := ha'.comp (f := fun y => y-x) (analyticAt_id.sub analyticAt_const)
  simpa only [Function.comp_def, add_sub_cancel] using hcomp

theorem analyticOnNhd_of_differentiableOn_affine {n m : ℕ} {S : Set (Fin n → ℂ)}
    (hS : IsOpen S) {f : (Fin n → ℂ) → (Fin m → ℂ)} (hf : DifferentiableOn ℂ f S) :
    AnalyticOnNhd ℂ f S := by
  intro x hx
  apply AnalyticAt.pi
  intro j
  apply analyticOnNhd_of_differentiableOn_finite hS _ x hx
  exact (differentiable_apply j).differentiableOn.comp hf (fun _ _ => mem_univ _)

end Release061

end OAI
