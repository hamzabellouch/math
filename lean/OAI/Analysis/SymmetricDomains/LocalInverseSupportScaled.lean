import Mathlib
import OAI.Analysis.SymmetricDomains.InverseChartGaussian
import OAI.Analysis.SymmetricDomains.FiniteUnion

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
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter
open scoped Topology
theorem independent_support_coercivity_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k : ℕ}
    (β : Fin k → Fin k → ℝ) (hβ : LinearIndependent ℝ β)
    (h : Fin k → E × (Fin k → ℂ) → ℂ)
    (hh : ∀ i, AnalyticAt ℂ (h i) 0) (hh0 : ∀ i, h i 0 = 1)
    (hder : ∀ i x, fderiv ℂ (fun y => Complex.log (h i y)) 0 x =
      Complex.I*∑ j, (β i j : ℂ)*x.2 j)
    (D : Set (E × (Fin k → ℂ))) {c : ℝ} (hc : 0 < c)
    (i₀ : Fin k) (hpeak : ∀ x ∈ D, ‖h i₀ x‖ ≤ Real.exp (-c*‖x‖^2)) :
    ∃ C > 0, ∃ V ∈ 𝓝 (0 : E × (Fin k → ℂ)), ∀ x ∈ V, x ∈ D →
      ‖x‖^2 ≤ C*‖fun i => 1-h i x‖ ∧ ‖x.2‖ ≤ C*‖fun i => 1-h i x‖ := by
  classical
  obtain ⟨A,hA,hlog⟩ := log_near_one_bound
  have he : ∀ᶠ x in 𝓝 (0 : E × (Fin k → ℂ)), ∀ i,
      h i x ≠ 0 ∧ ‖Complex.log (h i x)‖ ≤ A*‖h i x-1‖ := by
    apply Filter.eventually_all.mpr
    intro i
    exact ((hh0 i) ▸ (hh i).continuousAt.tendsto) hlog
  have hal : ∀ i, AnalyticAt ℂ (fun x => Complex.log (h i x)) 0 :=
    fun i => (hh i).clog (by rw [hh0]; exact Complex.one_mem_slitPlane)
  obtain ⟨B,hB,W,hW,hscale⟩ := normal_scale_bound β hβ
    (fun i x => Complex.log (h i x)) hal (by simp [hh0]) hder
  refine ⟨max (A/c) (B*(A+A/c)), lt_of_lt_of_le (div_pos hA hc) (le_max_left _ _),
    W ∩ {x | ∀ i, h i x ≠ 0 ∧ ‖Complex.log (h i x)‖ ≤ A*‖h i x-1‖},
    inter_mem hW he,?_⟩
  intro x hx hxD
  let d := ‖fun i => (1 : ℂ)-h i x‖
  have hd : 0 ≤ d := norm_nonneg _
  have hld : ‖fun i => Complex.log (h i x)‖ ≤ A*d := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hA.le hd)).mpr
    intro i
    calc
      _ ≤ A*‖h i x-1‖ := (hx.2 i).2
      _ = A*‖1-h i x‖ := by rw [norm_sub_rev]
      _ ≤ A*d := mul_le_mul_of_nonneg_left (norm_le_pi_norm (fun i => (1 : ℂ)-h i x) i) hA.le
  have hreal : (Complex.log (h i₀ x)).re ≤ -c*‖x‖^2 := by
    rw [Complex.log_re]
    exact (Real.log_le_iff_le_exp (norm_pos_iff.mpr (hx.2 i₀).1)).mpr (hpeak x hxD)
  have hs : ‖x‖^2 ≤ (A/c)*d := by
    have hr := Complex.abs_re_le_norm (Complex.log (h i₀ x))
    have hnorm : ‖Complex.log (h i₀ x)‖ ≤ A*d :=
      (norm_le_pi_norm (fun i => Complex.log (h i x)) i₀).trans hld
    have hh' : c*‖x‖^2 ≤ A*d := by
      have habs := neg_le_abs (Complex.log (h i₀ x)).re
      linarith
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    nlinarith [hh']
  constructor
  · exact hs.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd)
  · calc
      ‖x.2‖ ≤ B*(‖fun i => Complex.log (h i x)‖+‖x‖^2) := hscale x hx.1
      _ ≤ B*(A*d+(A/c)*d) := mul_le_mul_of_nonneg_left (add_le_add hld hs) hB.le
      _ = (B*(A+A/c))*d := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hd

theorem local_inverse_support_scaled_bound
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [NormedSpace ℂ H] {k : ℕ}
    (Φ : E × (Fin k → ℂ) → H) (Ψ : H → E × (Fin k → ℂ)) {p : H}
    (hΦ : AnalyticAt ℂ Φ 0) (hΦ0 : Φ 0=p)
    (hΨ : DifferentiableAt ℂ Ψ p) (hΨ0 : Ψ p=0)
    (hinv : ∀ᶠ z in 𝓝 (0 : E × (Fin k → ℂ)), Ψ (Φ z)=z)
    (D : Set H) (h : Fin k → H → ℂ)
    (hh : ∀ i, AnalyticAt ℂ (h i) p) (hh0 : ∀ i, h i p=1)
    (i₀ : Fin k) (hpeak : ∀ y ∈ D, ‖h i₀ y‖ ≤ Real.exp (-(‖y-p‖^2)))
    (β : Fin k → Fin k → ℝ) (hβ : LinearIndependent ℝ β)
    (hder : ∀ i z, fderiv ℂ (fun y => Complex.log (h i (Φ y))) 0 z =
      Complex.I*∑ j, (β i j : ℂ)*z.2 j) :
    ∃ C > 0, ∃ W ∈ 𝓝 (0 : E × (Fin k → ℂ)),
      ∀ A ≥ 0, ∀ t > 0, ∀ z ∈ W, Φ z ∈ D →
        ‖fun i => 1-h i (Φ z)‖ ≤ A*t →
        ‖weightedUnscale t z‖ ≤ max (Real.sqrt (C*A)) (C*A) := by
  obtain ⟨c,hc,hev⟩ := inverse_chart_gaussian hΦ.continuousAt hΦ0 hΨ hΨ0 hinv
    (h i₀) D hpeak
  let R := {z | Φ z ∈ D → ‖h i₀ (Φ z)‖ ≤ Real.exp (-c*‖z‖^2)}
  have hR : R ∈ 𝓝 (0 : E × (Fin k → ℂ)) := hev
  obtain ⟨C,hC,W,hW,hb⟩ := independent_support_coercivity_at β hβ
    (fun i z => h i (Φ z)) (fun i => (hΦ0.symm ▸ hh i).comp hΦ)
    (by intro i; rw [hΦ0,hh0]) (by exact hder) (R ∩ Φ ⁻¹' D) hc i₀
    (fun z hz => hz.1 hz.2)
  refine ⟨C,hC,W ∩ R,inter_mem hW hR,?_⟩
  intro A hA t ht z hz hzD hd
  have H := hb z hz.1 ⟨hz.2,hzD⟩
  have hd' : C*‖fun i => 1-h i (Φ z)‖ ≤ (C*A)*t := by
    calc _ ≤ C*(A*t) := mul_le_mul_of_nonneg_left hd hC.le
         _ = _ := by ring
  exact weightedUnscale_bound (mul_nonneg hC.le hA) ht (H.1.trans hd') (H.2.trans hd')
end Release061

end

end OAI
