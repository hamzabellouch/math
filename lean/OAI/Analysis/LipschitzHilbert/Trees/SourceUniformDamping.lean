import OAI.Analysis.LipschitzHilbert.Trees.SourceLpDamping

namespace OAI

/-! The Gaussian threshold is uniform in the finite number of phases.
This permits the manuscript choice K=blockCount(L) without fixing K
before choosing the lower threshold for L. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem eventually_damped_vertex_bound_finite (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (n : ℕ) (a eta : Fin n → ℝ) (mu P : ℝ) (value : ℂ),
      (∀ i, 0 ≤ a i) → (∑ i, a i = mu) → 0 ≤ mu → mu ≤ 1 → 0 ≤ P →
      ‖value‖ ≤ P*(1+Real.sqrt (∑ i, (eta i)^2))*Real.exp (C*Real.sqrt L) →
      (Real.sqrt (∑ i, (eta i)^2) ≤ L^2 → ‖value‖ ≤ P) →
      ‖gaussianPhaseDamping (phaseTubePoint a eta)*value‖ ≤ Real.exp 1*P := by
  filter_upwards [eventually_gaussian_imaginary_tail C hC] with L htail
  intro n a eta mu P value ha hsum hmu hmu1 hP hcrude hsmall
  let r := Real.sqrt (∑ i, (eta i)^2)
  have hr2 : r^2 = ∑ i, (eta i)^2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hd := gaussianPhaseDamping_simplex_le a eta mu ha hsum
  rw [← hr2] at hd
  rw [norm_mul]
  by_cases hr : r ≤ L^2
  · have hd1 : ‖gaussianPhaseDamping (phaseTubePoint a eta)‖ ≤ Real.exp 1 := by
      apply hd.trans (Real.exp_le_exp.mpr _)
      nlinarith [sq_nonneg r]
    exact mul_le_mul hd1 (hsmall hr) (norm_nonneg _) (Real.exp_pos _).le
  · have hlarge := htail mu r hmu hmu1 (le_of_not_ge hr)
    calc
      _ ≤ Real.exp (mu^2-r^2)*(P*(1+r)*Real.exp (C*Real.sqrt L)) :=
        mul_le_mul hd hcrude (norm_nonneg _) (Real.exp_pos _).le
      _ = P*((1+r)*Real.exp (mu^2-r^2+C*Real.sqrt L)) := by
        rw [Real.exp_add]
        ring
      _ ≤ P*1 := mul_le_mul_of_nonneg_left hlarge hP
      _ ≤ Real.exp 1*P := by
        have he : 1 ≤ Real.exp (1:ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
        nlinarith

theorem eventually_source_damped_vertex_root_finite (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (n : ℕ) (μ : Measure X) (F : X → EuclideanSpace ℂ κ)
      (a eta : Fin n → ℝ) (mu P p : ℝ),
      (∀ i, 0 ≤ a i) → (∑ i, a i = mu) → 0 ≤ mu → mu ≤ 1 → 0 ≤ P → 0 < p →
      (∫ x, ‖F x‖^p ∂μ)^(1/p) ≤
        P*(1+Real.sqrt (∑ i, (eta i)^2))*Real.exp (C*Real.sqrt L) →
      (Real.sqrt (∑ i, (eta i)^2) ≤ L^2 → (∫ x, ‖F x‖^p ∂μ)^(1/p) ≤ P) →
      (∫ x, ‖gaussianPhaseDamping (phaseTubePoint a eta) • F x‖^p ∂μ)^(1/p) ≤
        Real.exp 1*P := by
  filter_upwards [eventually_damped_vertex_bound_finite C hC] with L hL
  intro n μ F a eta mu P p ha hsum hmu hmu1 hP hp hcrude hsmall
  let V := (∫ x, ‖F x‖^p ∂μ)^(1/p)
  have hV : 0 ≤ V := Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _
  have hnorm : ‖(V:ℂ)‖ = V := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hV]
  have h := hL n a eta mu P (V:ℂ) ha hsum hmu hmu1 hP
    (by simpa only [hnorm] using hcrude) (by simpa only [hnorm] using hsmall)
  rw [norm_mul,hnorm] at h
  rwa [source_lp_root_smul μ F _ p hp]

end LipschitzHilbert

end

end OAI
