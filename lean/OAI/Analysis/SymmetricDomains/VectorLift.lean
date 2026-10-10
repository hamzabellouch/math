import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.AnalyticLift
variable {d j : ℕ} {A : Type*} [NormedCommRing A] [NormedAlgebra ℝ A] [NormOneClass A]

def monomial (σ : Fin j → Fin d) : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → A) A :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ j A).compContinuousLinearMap
    (fun i => ContinuousLinearMap.proj (σ i))

omit [NormOneClass A] in
lemma monomial_apply (σ : Fin j → Fin d) (x : Fin j → Fin d → A) :
    monomial σ x = ∏ i, x i (σ i) := by
  simp [monomial,ContinuousMultilinearMap.mkPiAlgebraFin_apply,List.prod_ofFn]

lemma monomial_norm_le (σ : Fin j → Fin d) : ‖monomial (A := A) σ‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
  intro x
  rw [monomial_apply,one_mul]
  exact (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun i _ => norm_le_pi_norm (x i) (σ i)))

def coefficient (p : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → A) A :=
  ∑ σ : Fin j → Fin d, (p (fun i => Pi.single (σ i) 1)) • monomial σ

lemma coefficient_norm_le (p : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ) :
    ‖coefficient (A := A) p‖ ≤ (d : ℝ)^j * ‖p‖ := by
  classical
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : Fin j → Fin d, ‖p‖ := by
      apply Finset.sum_le_sum
      intro σ _
      rw [norm_smul]
      exact (mul_le_mul (p.unit_le_opNorm ((pi_norm_le_iff_of_nonneg zero_le_one).mpr (by
        intro i
        exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (by
          intro k
          by_cases h : k = σ i <;> simp [h]))))
        (monomial_norm_le σ) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)
    _ = _ := by simp

lemma coordinate_expansion
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ)
    (x : Fin j → Fin d → ℝ) :
    p x = ∑ σ : Fin j → Fin d, p (fun i => Pi.single (σ i) 1) * ∏ i, x i (σ i) := by
  classical
  have hx : x = fun i => ∑ k : Fin d, x i k • Pi.single k 1 := by
    funext i l
    simp [Finset.sum_apply,Pi.single_apply]
  conv_lhs => rw [hx,p.map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [p.map_smul_univ]
  simp only [smul_eq_mul,mul_comm]

omit [NormOneClass A] in
lemma evaluation_coefficient (φ : A →ₐ[ℝ] ℝ)
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ)
    (x : Fin j → Fin d → A) :
    φ (coefficient p x) = p (fun i k => φ (x i k)) := by
  classical
  rw [coordinate_expansion]
  simp only [coefficient,sum_apply,map_sum,
    smul_apply,map_smul,monomial_apply,map_prod,smul_eq_mul]

def series (p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ) :
    FormalMultilinearSeries ℝ (Fin d → A) A := fun j => coefficient (p j)

lemma radius_lower_bound (p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ)
    {r : ℝ≥0} (hr : (r : ℝ≥0∞) < p.radius) :
    (r / (d+1 : ℝ≥0) : ℝ≥0) ≤ (series (A := A) p).radius := by
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  apply (p.summable_norm_mul_pow hr).of_nonneg_of_le
  · intro j; positivity
  · intro j
    have hd : (0 : ℝ) < d+1 := by positivity
    have hd' : (d : ℝ)/(d+1) ≤ 1 := (div_le_one hd).mpr (by linarith)
    calc
      _ ≤ ((d : ℝ)^j*‖p j‖) * ((r : ℝ)/(d+1))^j := by
        exact mul_le_mul_of_nonneg_right (coefficient_norm_le (p j)) (by positivity)
      _ = ‖p j‖ * (r : ℝ)^j * ((d : ℝ)/(d+1))^j := by rw [div_pow,div_pow]; ring
      _ ≤ ‖p j‖ * (r : ℝ)^j * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity) hd') (by positivity)
      _ = _ := mul_one _

lemma radius_pos (p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ)
    (hp : 0 < p.radius) : 0 < (series (A := A) p).radius := by
  obtain ⟨r,hr0,hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp
  apply lt_of_lt_of_le _ (radius_lower_bound (A := A) p hr)
  exact ENNReal.coe_pos.mpr (div_pos (ENNReal.coe_pos.mp hr0) (by positivity))

variable [CompleteSpace A]

lemma analytic_series (p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ)
    (hp : 0 < p.radius) : AnalyticAt ℝ (series (A := A) p).sum 0 :=
  by
  have hq : 0 < (series (A := A) p).radius := radius_pos p hp
  exact ((series (A := A) p).hasFPowerSeriesOnBall hq).analyticAt

lemma evaluation_series (φ : A →ₐ[ℝ] ℝ) (L : A →L[ℝ] ℝ)
    (hL : ∀ a, L a = φ a) (hφ : ∀ a, |φ a| ≤ ‖a‖)
    {f : (Fin d → ℝ) → ℝ} {p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ}
    {R : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f p 0 R)
    {r : ℝ≥0} (hr0 : 0 < r) (hr : (r : ℝ≥0∞) < R)
    {x : Fin d → A} (hx : ‖x‖ < (r : ℝ)/(d+1)) :
    φ ((series p).sum x) = f (fun k => φ (x k)) := by
  have hpr : (r : ℝ≥0∞) < p.radius := hr.trans_le hf.r_le
  have hxr : x ∈ Metric.eball 0 (series (A := A) p).radius := by
    apply Metric.eball_subset_eball (radius_lower_bound p hpr)
    rw [Metric.eball_coe,Metric.mem_ball,dist_zero_right]
    simpa only [NNReal.coe_div,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using hx
  have hex : ‖fun k => φ (x k)‖ < r := by
    have hn : ‖fun k => φ (x k)‖ ≤ ‖x‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr ?_
      intro k
      exact (hφ (x k)).trans (norm_le_pi_norm x k)
    have hdr : (r : ℝ)/(d+1) ≤ r := div_le_self (by positivity) (le_add_of_nonneg_left (Nat.cast_nonneg d))
    exact hn.trans_lt (hx.trans_le hdr)
  have hexR : (fun k => φ (x k)) ∈ Metric.eball 0 R := by
    apply Metric.eball_subset_eball hr.le
    rw [Metric.eball_coe,Metric.mem_ball,dist_zero_right]
    exact hex
  have hh := L.hasSum (((series (A := A) p).hasFPowerSeriesOnBall
    (radius_pos p (hf.r_pos.trans_le hf.r_le))).hasSum hxr)
  simp only [zero_add,hL,series,evaluation_coefficient] at hh
  exact hh.unique (by simpa only [zero_add] using hf.hasSum hexR)

theorem exists_scalar_lift {f : (Fin d → ℝ) → ℝ} (hf : AnalyticAt ℝ f 0) :
    ∃ (ε : ℝ) (F : (Fin d → A) → A), 0 < ε ∧ AnalyticAt ℝ F 0 ∧
      ∀ (φ : A →ₐ[ℝ] ℝ) (L : A →L[ℝ] ℝ), (∀ a, L a = φ a) →
        (∀ a, |φ a| ≤ ‖a‖) → ∀ x, ‖x‖ < ε → φ (F x) = f (fun k => φ (x k)) := by
  obtain ⟨p,R,hp⟩ := hf
  obtain ⟨r,hr0,hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  refine ⟨(r : ℝ)/(d+1),(series p).sum,div_pos (ENNReal.coe_pos.mp hr0) (by positivity),
    analytic_series p (hp.r_pos.trans_le hp.r_le),?_⟩
  intro φ L hL hφ x hx
  exact evaluation_series φ L hL hφ hp (ENNReal.coe_pos.mp hr0) hr hx

theorem exists_vector_lift {k : ℕ} {f : (Fin d → ℝ) → Fin k → ℝ}
    (hf : AnalyticAt ℝ f 0) :
    ∃ (ε : ℝ) (F : (Fin d → A) → Fin k → A), 0 < ε ∧ AnalyticAt ℝ F 0 ∧
      ∀ (φ : A →ₐ[ℝ] ℝ) (L : A →L[ℝ] ℝ), (∀ a, L a = φ a) →
        (∀ a, |φ a| ≤ ‖a‖) → ∀ x, ‖x‖ < ε →
          ∀ i, φ (F x i) = f (fun j => φ (x j)) i := by
  have hfi : ∀ i, AnalyticAt ℝ (fun x => f x i) 0 := (analyticAt_pi_iff.mp hf)
  choose ε F hε hF hEval using fun i => exists_scalar_lift (A := A) (hfi i)
  have hn : ∀ᶠ x : Fin d → A in 𝓝 0, ∀ i, ‖x‖ < ε i := by
    rw [Filter.eventually_all]
    intro i
    exact (isOpen_lt continuous_norm continuous_const).mem_nhds (by simpa using hε i)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨δ,fun x i => F i x,hδ,AnalyticAt.pi hF,?_⟩
  intro φ L hL hφ x hx i
  exact hEval i φ L hL hφ x (hball (by simpa [Metric.mem_ball,dist_zero_right] using hx) i)

end Release061.AnalyticLift

end

end OAI
