import Mathlib

namespace OAI

/-! Analytic functions with values in continuous-function Banach spaces. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Metric Filter Topology
open scoped BigOperators NNReal ENNReal
namespace DegeneratingTrees

variable {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

 
def liftCML {n : ℕ} (p : E [×n]→L[ℂ] F) : C(K, E) [×n]→L[ℂ] C(K, F) :=
  let P : MultilinearMap ℂ (fun _ : Fin n => C(K, E)) C(K, F) :=
    { toFun := fun v => ⟨fun t => p (fun i => v i t),
        p.cont.comp (continuous_pi fun i => (v i).continuous)⟩
      map_update_add' := by
        intro _ v i a b
        ext t
        change p (fun j => Function.update v i (a + b) j t) =
          p (fun j => Function.update v i a j t) + p (fun j => Function.update v i b j t)
        have he (u : C(K, E)) : (fun j => Function.update v i u j t) =
            Function.update (fun j => v j t) i (u t) := by
          ext j
          by_cases hj : j = i <;> simp [hj]
        simp_rw [he]
        exact p.map_update_add (fun j => v j t) i (a t) (b t)
      map_update_smul' := by
        intro _ v i c a
        ext t
        change p (fun j => Function.update v i (c • a) j t) =
          c • p (fun j => Function.update v i a j t)
        have he (u : C(K, E)) : (fun j => Function.update v i u j t) =
            Function.update (fun j => v j t) i (u t) := by
          ext j
          by_cases hj : j = i <;> simp [hj]
        simp_rw [he]
        exact p.map_update_smul (fun j => v j t) i c (a t) }
  P.mkContinuous ‖p‖ (by
    intro v
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro t
    exact (p.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun i _ => (v i).norm_coe_le_norm t)) (norm_nonneg p)))

@[simp] theorem liftCML_apply {n : ℕ} (p : E [×n]→L[ℂ] F)
    (v : Fin n → C(K, E)) (t : K) : liftCML p v t = p (fun i => v i t) := rfl

theorem liftCML_norm_le {n : ℕ} (p : E [×n]→L[ℂ] F) :
    ‖liftCML (K := K) p‖ ≤ ‖p‖ :=
  by
    unfold liftCML
    apply MultilinearMap.mkContinuous_norm_le
    exact norm_nonneg _

 

theorem liftSeries_radius {p : FormalMultilinearSeries ℂ E F} {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < p.radius) :
    (r : ℝ≥0∞) ≤ (show FormalMultilinearSeries ℂ C(K, E) C(K, F) from
      fun n => liftCML (K := K) (p n)).radius := by
  apply FormalMultilinearSeries.le_radius_of_summable
  exact Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun n => mul_le_mul_of_nonneg_right (liftCML_norm_le (p n)) (by positivity))
    (p.summable_norm_mul_pow hr)

 

theorem analytic_continuousMap_of_series [CompleteSpace F] {f : E → F}
    {p : FormalMultilinearSeries ℂ E F} {R : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p 0 R) {r : ℝ≥0} (hrR : (r : ℝ≥0∞) < R) :
    ∃ Φ : C(K, E) → C(K, F), AnalyticOnNhd ℂ Φ (ball 0 (r : ℝ)) ∧
      ∀ v ∈ ball (0 : C(K, E)) (r : ℝ), ∀ t, Φ v t = f (v t) := by
  let P : FormalMultilinearSeries ℂ C(K, E) C(K, F) := fun n => liftCML (p n)
  have hrP : (r : ℝ≥0∞) ≤ P.radius := liftSeries_radius (hrR.trans_le hp.r_le)
  refine ⟨P.sum, ?_, ?_⟩
  · apply P.analyticOnNhd.mono
    intro v hv
    rw [mem_eball_zero_iff]
    apply lt_of_lt_of_le _ hrP
    have hn : ‖v‖ < (r : ℝ) := by simpa using hv
    exact_mod_cast hn
  · intro v hv t
    have hv' : (‖v‖₊ : ℝ≥0∞) < r := by
      have hn : ‖v‖ < (r : ℝ) := by simpa using hv
      exact_mod_cast hn
    have hvP : v ∈ eball (0 : C(K, E)) P.radius := by
      exact (mem_eball_zero_iff).2 (hv'.trans_le hrP)
    have hvR : v t ∈ eball (0 : E) R := by
      rw [mem_eball_zero_iff]
      exact (show (‖v t‖₊ : ℝ≥0∞) ≤ ‖v‖₊ from by
        exact_mod_cast v.norm_coe_le_norm t).trans_lt (hv'.trans hrR)
    have h₁ := (ContinuousMap.evalCLM (R := ℂ) (M := F) t).hasSum (P.hasSum hvP)
    have h₂ := hp.hasSum hvR
    simp only [zero_add] at h₂
    exact h₁.unique h₂

 

theorem analytic_continuousMap_realization [CompleteSpace F] {f : E → F}
    (hf : AnalyticAt ℂ f 0) :
    ∃ (r : ℝ), 0 < r ∧ ∃ Φ : C(K, E) → C(K, F),
      AnalyticOnNhd ℂ Φ (ball 0 r) ∧
      ∀ v ∈ ball (0 : C(K, E)) r, ∀ t, Φ v t = f (v t) := by
  obtain ⟨p, R, hp⟩ := hf
  obtain ⟨r, hr0, hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  exact ⟨r, by exact_mod_cast hr0, analytic_continuousMap_of_series hp hrR⟩

 

def circleExtension {r : ℝ} (f : C(sphere (0 : ℂ) r, ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ sphere (0 : ℂ) r then f ⟨z, hz⟩ else 0

@[simp] theorem circleExtension_on {r : ℝ} (f : C(sphere (0 : ℂ) r, ℂ))
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) r) : circleExtension f z = f ⟨z, hz⟩ := by
  simp only [circleExtension, dite_eq_left hz]

private theorem circleExtension_continuousOn {r : ℝ} (f : C(sphere (0 : ℂ) r, ℂ)) :
    ContinuousOn (circleExtension f) (sphere (0 : ℂ) r) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert f.continuous using 1
  ext z
  exact circleExtension_on f z.property

 
def circleFunctional (r : ℝ) (hr : 0 ≤ r) : C(sphere (0 : ℂ) r, ℂ) →L[ℂ] ℂ :=
  let L : C(sphere (0 : ℂ) r, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∮ z in C(0, r), circleExtension f z
      map_add' := by
        intro f g
        have he : circleExtension (f + g) = fun z => circleExtension f z + circleExtension g z := by
          ext z
          by_cases hz : z ∈ sphere (0 : ℂ) r <;> simp only [circleExtension, hz, dite_true, dite_false, ContinuousMap.add_apply, add_zero]
        rw [he]
        exact circleIntegral.integral_add
          ((circleExtension_continuousOn f).circleIntegrable hr)
          ((circleExtension_continuousOn g).circleIntegrable hr)
      map_smul' := by
        intro c f
        have he : circleExtension (c • f) = fun z => c • circleExtension f z := by
          ext z
          by_cases hz : z ∈ sphere (0 : ℂ) r <;> simp only [circleExtension, hz, dite_true, dite_false, ContinuousMap.smul_apply, smul_zero]
        rw [he, circleIntegral.integral_smul]
        rfl }
  L.mkContinuous (2 * Real.pi * r) (by
    intro f
    apply circleIntegral.norm_integral_le_of_norm_le_const hr
    intro z hz
    rw [circleExtension_on f hz]
    exact f.norm_coe_le_norm ⟨z, hz⟩)

theorem circleFunctional_eq {r : ℝ} (hr : 0 ≤ r) (f : C(sphere (0 : ℂ) r, ℂ))
    (h : ℂ → ℂ) (he : ∀ z : sphere (0 : ℂ) r, f z = h z) :
    circleFunctional r hr f = ∮ z in C(0, r), h z := by
  apply circleIntegral.integral_congr hr
  intro z hz
  rw [circleExtension_on f hz]
  exact he ⟨z, hz⟩

 

theorem analytic_circle_profiles {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {F : A × ℂ → ℂ} (hF : AnalyticAt ℂ F 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ r : ℝ, 0 < r → r < a →
      ∃ φ ψ : A → C(sphere (0 : ℂ) r, ℂ),
        AnalyticOnNhd ℂ F (ball 0 a ×ˢ closedBall 0 r) ∧
        AnalyticOnNhd ℂ φ (ball 0 a) ∧ AnalyticOnNhd ℂ ψ (ball 0 a) ∧
        (∀ q ∈ ball (0 : A) a, ∀ z : sphere (0 : ℂ) r, φ q z = F (q, z)) ∧
        (∀ q ∈ ball (0 : A) a, ∀ z : sphere (0 : ℂ) r,
          ψ q z = deriv (fun y => F (q, y)) z) := by
  let H : A × ℂ → ℂ × ℂ := fun x => (F x, fderiv ℂ F x (0, 1))
  have hH : AnalyticAt ℂ H 0 := hF.prod
    (((ContinuousLinearMap.apply ℂ ℂ ((0, 1) : A × ℂ)).analyticAt _).comp hF.fderiv)
  obtain ⟨p, R, hp⟩ := hH
  obtain ⟨b, hb0, hbR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hb : (0 : ℝ) < b := by exact_mod_cast hb0
  refine ⟨b / 2, half_pos hb, ?_⟩
  intro r hr hra
  let K := sphere (0 : ℂ) r
  let w : C(K, A × ℂ) := ⟨fun z => (0, z),
    continuous_const.prodMk continuous_subtype_val⟩
  let L : A →L[ℂ] C(K, A × ℂ) :=
    (ContinuousLinearMap.const ℂ K).comp (ContinuousLinearMap.inl ℂ A ℂ)
  let v : A → C(K, A × ℂ) := fun q => L q + w
  have hve (q : A) (z : K) : v q z = (q, (z : ℂ)) := by simp [v, L, w]
  have hva : AnalyticOnNhd ℂ v (ball 0 ((b : ℝ) / 2)) :=
    fun q _ => (L.analyticAt q).add analyticAt_const
  have hvb (q : A) (hq : q ∈ ball (0 : A) ((b : ℝ) / 2)) :
      v q ∈ ball (0 : C(K, A × ℂ)) (b : ℝ) := by
    have hnq : ‖q‖ < (b : ℝ) / 2 := by simpa using hq
    have hnv : ‖v q‖ ≤ max ‖q‖ r := by
      apply (ContinuousMap.norm_le _ (le_max_of_le_left (norm_nonneg q))).2
      intro z
      rw [hve, Prod.norm_def]
      have hnz : ‖(z : ℂ)‖ = r := by simp
      rw [hnz]
    have : ‖v q‖ < (b : ℝ) := hnv.trans_lt
      ((max_lt hnq hra).trans (half_lt_self hb))
    simpa using this
  obtain ⟨Φ, hΦ, hΦe⟩ := analytic_continuousMap_of_series (K := K) hp hbR
  let π₁ := ContinuousLinearMap.compLeftContinuous ℂ K (ContinuousLinearMap.fst ℂ ℂ ℂ)
  let π₂ := ContinuousLinearMap.compLeftContinuous ℂ K (ContinuousLinearMap.snd ℂ ℂ ℂ)
  let φ : A → C(K, ℂ) := fun q => π₁ (Φ (v q))
  let ψ : A → C(K, ℂ) := fun q => π₂ (Φ (v q))
  have hFball : AnalyticOnNhd ℂ F (ball 0 ((b : ℝ) / 2) ×ˢ closedBall 0 r) := by
    intro x hx
    have hn : ‖x‖ < (b : ℝ) := by
      rw [Prod.norm_def]
      have hx₁ : ‖x.1‖ < (b : ℝ) / 2 := by simpa using hx.1
      have hx₂ : ‖x.2‖ ≤ r := by simpa using hx.2
      exact (max_lt hx₁ (hx₂.trans_lt hra)).trans (half_lt_self hb)
    have hxR : x ∈ eball (0 : A × ℂ) R := by
      rw [mem_eball_zero_iff]
      exact (show (‖x‖₊ : ℝ≥0∞) < b from by exact_mod_cast hn).trans hbR
    exact ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _).comp (hp.analyticOnNhd x hxR)
  refine ⟨φ, ψ, hFball, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact (π₁.analyticAt _).comp ((hΦ _ (hvb q hq)).comp (hva q hq))
  · intro q hq
    exact (π₂.analyticAt _).comp ((hΦ _ (hvb q hq)).comp (hva q hq))
  · intro q hq z
    change (Φ (v q) z).1 = F (q, z)
    rw [hΦe _ (hvb q hq), hve]
  · intro q hq z
    change (Φ (v q) z).2 = deriv (fun y => F (q, y)) z
    rw [hΦe _ (hvb q hq), hve]
    have hFd := (hFball (q, z) ⟨hq, sphere_subset_closedBall z.property⟩).differentiableAt
    exact ((hFd.hasFDerivAt.comp_hasDerivAt (z : ℂ)
      ((hasDerivAt_const (z : ℂ) q).prodMk (hasDerivAt_id (z : ℂ)))).deriv).symm

 

omit [CompactSpace K] in
theorem continuousMap_ringInverse_apply (f : C(K, ℂ)) (hf : IsUnit f) (z : K) :
    Ring.inverse f z = (f z)⁻¹ := by
  have hn : f z ≠ 0 := (f.isUnit_iff_forall_ne_zero).1 hf z
  apply mul_left_cancel₀ hn
  rw [← ContinuousMap.mul_apply, Ring.mul_inverse_cancel f hf]
  simp [hn]

end DegeneratingTrees
end

end OAI
