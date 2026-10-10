import OAI.Analysis.LipschitzHilbert.Phase.DampedSimplexInterpolation

namespace OAI

/-! The crude analytic bound supplies boundedness on the whole simplex
 tube. Gaussian decay also extends the vertex estimate from the ball of
 imaginary radius L² to every imaginary vector, as in manuscript §11. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
variable {ι : Type*} [Fintype ι]

theorem gaussianPhaseDamping_crude_bound (a eta : ι → ℝ) (mu B : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = mu) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) :
    ‖gaussianPhaseDamping (phaseTubePoint a eta)‖*
      (1+Real.sqrt (∑ i, (eta i)^2))*Real.exp B ≤ Real.exp (B+2) := by
  let r := Real.sqrt (∑ i, (eta i)^2)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = ∑ i, (eta i)^2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hd := gaussianPhaseDamping_simplex_le a eta mu ha hsum
  rw [← hr2] at hd
  calc
    _ ≤ Real.exp (mu^2-r^2)*Real.exp r*Real.exp B := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul hd (by simpa only [add_comm] using Real.add_one_le_exp r)
        (by positivity) (Real.exp_pos _).le
    _ = Real.exp (mu^2-r^2+r+B) := by rw [← Real.exp_add,← Real.exp_add]
    _ ≤ Real.exp (B+2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (r-1/2)]

theorem damped_simplex_crude_bound (F : (ι → ℂ) → ℂ) (P B mu : ℝ)
    (hP : 0 ≤ P) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hcrude : ∀ a : ι → ℝ, (∀ i, 0 ≤ a i) → (∑ i, a i = mu) → ∀ eta,
      ‖F (phaseTubePoint a eta)‖ ≤
        P*(1+Real.sqrt (∑ i, (eta i)^2))*Real.exp B) :
    ∀ a : ι → ℝ, (∀ i, 0 ≤ a i) → (∑ i, a i = mu) →
      phaseTubeBound (fun z => gaussianPhaseDamping z*F z) (P*Real.exp (B+2)) a := by
  intro a ha hsum eta
  rw [norm_mul]
  calc
    _ ≤ ‖gaussianPhaseDamping (phaseTubePoint a eta)‖*
        (P*(1+Real.sqrt (∑ i, (eta i)^2))*Real.exp B) :=
      mul_le_mul_of_nonneg_left (hcrude a ha hsum eta) (norm_nonneg _)
    _ = P*(‖gaussianPhaseDamping (phaseTubePoint a eta)‖*
        (1+Real.sqrt (∑ i, (eta i)^2))*Real.exp B) := by ring
    _ ≤ P*Real.exp (B+2) := mul_le_mul_of_nonneg_left
      (gaussianPhaseDamping_crude_bound a eta mu B ha hsum hmu hmu1) hP

theorem eventually_damped_vertex_bound (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (a eta : ι → ℝ) (mu P : ℝ) (value : ℂ),
      (∀ i, 0 ≤ a i) → (∑ i, a i = mu) → 0 ≤ mu → mu ≤ 1 → 0 ≤ P →
      ‖value‖ ≤ P*(1+Real.sqrt (∑ i, (eta i)^2))*Real.exp (C*Real.sqrt L) →
      (Real.sqrt (∑ i, (eta i)^2) ≤ L^2 → ‖value‖ ≤ P) →
      ‖gaussianPhaseDamping (phaseTubePoint a eta)*value‖ ≤ Real.exp 1*P := by
  filter_upwards [eventually_gaussian_imaginary_tail C hC] with L htail
  intro a eta mu P value ha hsum hmu hmu1 hP hcrude hsmall
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

end LipschitzHilbert

end

end OAI
