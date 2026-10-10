import Mathlib
import OAI.Analysis.SymmetricDomains.BishopPathInterior

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
namespace Release061.Wiener
open Set Filter Metric
open scoped Topology

theorem discContinuityWithin_pullback {k l : ℕ} {Ω : Set (Fin l → ℂ)}
    {S : Set (Fin k → ℂ)} {r ε : ℝ} {Φ : (Fin k → ℂ) → Fin l → ℂ}
    (hCP : DiscContinuityWithin l Ω ε)
    (hΦ : AnalyticOnNhd ℂ Φ (ball 0 r))
    (hS : ball 0 r ⊆ S) (hsmall : MapsTo Φ (ball 0 r) (ball 0 ε)) :
    DiscContinuityWithin k (S ∩ Φ ⁻¹' Ω) r := by
  intro A hA hAh hAr hbd hstart
  let B : Icc (0 : ℝ) 1 → ClosedDisc → Fin l → ℂ := fun s z => Φ (A s z)
  have hB : Continuous (Function.uncurry B) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (hΦ _ (mem_ball_zero_iff.mpr (hAr p.1 p.2))).continuousAt.comp (f := Function.uncurry A) hA.continuousAt
  have hBh (s : Icc (0 : ℝ) 1) : ∃ g : ℂ → Fin l → ℂ,
      AnalyticOnNhd ℂ g (ball 0 1) ∧ ∀ z : ClosedDisc, B s z = g z := by
    obtain ⟨g,hg,he⟩ := hAh s
    refine ⟨Φ ∘ g,hΦ.comp hg ?_,fun z => congrArg Φ (he z)⟩
    intro z hz
    rw [← he ⟨z,ball_subset_closedBall hz⟩]
    exact mem_ball_zero_iff.mpr (hAr s _)
  have hBj (s : Icc (0 : ℝ) 1) (z : ClosedDisc) : ‖B s z‖ < ε :=
    mem_ball_zero_iff.mp (hsmall (mem_ball_zero_iff.mpr (hAr s z)))
  have hBi := hCP B hB hBh hBj (fun s z hz => (hbd s z hz).2) (fun z => (hstart z).2)
  exact fun s z => ⟨hS (mem_ball_zero_iff.mpr (hAr s z)),hBi s z⟩

end Release061.Wiener

open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Complexify
variable {d j : ℕ}

def monomial (σ : Fin j → Fin d) : ContinuousMultilinearMap ℂ (fun _ : Fin j => Fin d → ℂ) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℂ j ℂ).compContinuousLinearMap
    (fun i => ContinuousLinearMap.proj (σ i))

lemma monomial_apply (σ : Fin j → Fin d) (x : Fin j → Fin d → ℂ) :
    monomial σ x = ∏ i, x i (σ i) := by
  simp [monomial,ContinuousMultilinearMap.mkPiAlgebraFin_apply,List.prod_ofFn]

lemma monomial_norm_le (σ : Fin j → Fin d) : ‖monomial σ‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
  intro x
  rw [monomial_apply,one_mul]
  exact (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun i _ => norm_le_pi_norm (x i) (σ i)))

def coefficient (p : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin j => Fin d → ℂ) ℂ :=
  ∑ σ : Fin j → Fin d, (p (fun i => Pi.single (σ i) 1)) • monomial σ

lemma coefficient_norm_le (p : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ) :
    ‖coefficient p‖ ≤ (d : ℝ)^j * ‖p‖ := by
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

lemma coefficient_real
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ)
    (x : Fin j → Fin d → ℝ) :
    coefficient p (fun i k => (x i k : ℂ)) = (p x : ℂ) := by
  classical
  rw [coordinate_expansion]
  simp only [coefficient, sum_apply,smul_apply,monomial_apply,Complex.real_smul,
    Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_prod]

def series (p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ) :
    FormalMultilinearSeries ℂ (Fin d → ℂ) ℂ := fun j => coefficient (p j)

lemma radius_lower_bound (p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ)
    {r : ℝ≥0} (hr : (r : ℝ≥0∞) < p.radius) :
    (r / (d+1 : ℝ≥0) : ℝ≥0) ≤ (series p).radius := by
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
    (hp : 0 < p.radius) : 0 < (series p).radius := by
  obtain ⟨r,hr0,hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp
  apply lt_of_lt_of_le _ (radius_lower_bound p hr)
  exact ENNReal.coe_pos.mpr (div_pos (ENNReal.coe_pos.mp hr0) (by positivity))

lemma norm_real_vector (x : Fin d → ℝ) : ‖fun i => (x i : ℂ)‖ = ‖x‖ := by
  simp only [Pi.norm_def,Complex.nnnorm_real]

lemma series_real {f : (Fin d → ℝ) → ℝ}
    {p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ} {R : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p 0 R) {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < R) {x : Fin d → ℝ} (hx : ‖x‖ < (r : ℝ)/(d+1)) :
    (series p).sum (fun i => (x i : ℂ)) = (f x : ℂ) := by
  have hp : 0 < (series p).radius := radius_pos p hf.radius_pos
  have hxq : (fun i => (x i : ℂ)) ∈ Metric.eball 0 (series p).radius := by
    apply Metric.eball_subset_eball (radius_lower_bound p (hr.trans_le hf.r_le))
    rw [Metric.eball_coe,Metric.mem_ball,dist_zero_right,norm_real_vector]
    simpa only [NNReal.coe_div,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using hx
  have hxp : x ∈ Metric.eball 0 R := by
    apply Metric.eball_subset_eball hr.le
    rw [Metric.eball_coe,Metric.mem_ball,dist_zero_right]
    exact hx.trans_le (div_le_self (by positivity) (le_add_of_nonneg_left (Nat.cast_nonneg d)))
  have H := Complex.ofRealCLM.hasSum (hf.hasSum hxp)
  have Hq := ((series p).hasFPowerSeriesOnBall hp).hasSum hxq
  simp only [zero_add] at H Hq
  simp only [series,coefficient_real] at Hq
  exact Hq.unique H

theorem scalar {f : (Fin d → ℝ) → ℝ} (hf : AnalyticAt ℝ f 0) :
    ∃ g : (Fin d → ℂ) → ℂ, AnalyticAt ℂ g 0 ∧
      ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), g (fun i => (x i : ℂ)) = (f x : ℂ) := by
  obtain ⟨p,R,hp⟩ := hf
  obtain ⟨r,hr0,hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  refine ⟨(series p).sum,((series p).hasFPowerSeriesOnBall (radius_pos p hp.radius_pos)).analyticAt,?_⟩
  have he : 0 < (r : ℝ)/(d+1) := div_pos (ENNReal.coe_pos.mp hr0) (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : Fin d → ℝ) he] with x hx
  exact series_real hp hr (by simpa only [Metric.mem_ball,dist_zero_right] using hx)

theorem vector {k : ℕ} {f : (Fin d → ℝ) → Fin k → ℝ} (hf : AnalyticAt ℝ f 0) :
    ∃ g : (Fin d → ℂ) → Fin k → ℂ, AnalyticAt ℂ g 0 ∧
      ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), g (fun i => (x i : ℂ)) = fun i => (f x i : ℂ) := by
  have hfi := analyticAt_pi_iff.mp hf
  choose g hg he using fun i => scalar (hfi i)
  refine ⟨fun z i => g i z,analyticAt_pi_iff.mpr hg,?_⟩
  filter_upwards [Filter.eventually_all.mpr he] with x hx
  exact funext hx

end Release061.Complexify

end

end OAI
