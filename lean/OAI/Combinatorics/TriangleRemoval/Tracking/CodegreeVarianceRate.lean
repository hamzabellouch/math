import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.PowersetCardTriple
import OAI.Combinatorics.TriangleRemoval.Process.History

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem pmfMean_centered_sq_le {α : Type*} [Fintype α]
    (p : PMF α) (f : α → ℝ) (a : ℝ) :
    pmfMean p (fun b => (f b - pmfMean p f)^2) ≤
      pmfMean p (fun b => (f b - a)^2) := by
  rw [pmfMean_sq_sub,pmfMean_sq_sub]
  nlinarith [sq_nonneg (pmfMean p f - a)]

theorem codegree_centered_range {n : ℕ} {G H : Graph n}
    (hG : G ⊆ completeGraph n) (u v : Fin n) (hH : H ∈ (step G).support) :
    |(currentCodegree H u v : ℝ) -
      pmfMean (step G) (fun J => (currentCodegree J u v : ℝ))| ≤ 2 := by
  have hmlo : (currentCodegree G u v : ℝ) - 2 ≤
      pmfMean (step G) (fun J => (currentCodegree J u v : ℝ)) := by
    rw [← pmfMean_const (step G) ((currentCodegree G u v : ℝ) - 2)]
    apply pmfMean_mono
    intro J hJ
    have hJ' := (codegree_step_range hG u v hJ).2
    linarith
  have hmhi : pmfMean (step G) (fun J => (currentCodegree J u v : ℝ)) ≤
      (currentCodegree G u v : ℝ) := by
    rw [← pmfMean_const (step G) (currentCodegree G u v : ℝ)]
    apply pmfMean_mono
    intro J hJ
    have hJ' := (codegree_step_range hG u v hJ).1
    linarith
  obtain ⟨hlo,hhi⟩ := codegree_step_range hG u v hH
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem codegree_centered_variance {n : ℕ} {G : Graph n}
    (hG : G ⊆ completeGraph n) (u v : Fin n) :
    pmfMean (step G) (fun H => ((currentCodegree H u v : ℝ) -
      pmfMean (step G) (fun J => (currentCodegree J u v : ℝ)))^2) ≤
      2 * ((currentCodegree G u v : ℝ) -
        pmfMean (step G) (fun H => (currentCodegree H u v : ℝ))) := by
  exact (pmfMean_centered_sq_le _ _ (currentCodegree G u v : ℝ)).trans
    (codegree_step_second_moment hG u v)

@[simp] theorem markovLaw_triangle_step {n : ℕ} (G : Graph n) (k : ℕ) :
    markovLaw (PMF.pure G) (fun _ => step) k = evolve G k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [markovLaw,evolve,ih]

noncomputable def codegreeVarianceRate {n : ℕ} (u v : Fin n) (_k : ℕ) (G : Graph n) : ℝ :=
  2 * ((currentCodegree G u v : ℝ) -
    pmfMean (step G) (fun H => (currentCodegree H u v : ℝ)))

theorem triangle_codegree_noise_freedman {n : ℕ} (G : Graph n)
    (hG : G ⊆ completeGraph n) (u v : Fin n) (T k : ℕ)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw (PMF.pure G) (fun _ => step) T k)
      (fun ω => if r ≤ historyNoise (fun _ => step)
          (fun _ H => (currentCodegree H u v : ℝ)) T k ω ∧
        historyCounter (codegreeVarianceRate u v) T k ω ≤ V then 1 else 0) ≤
      Real.exp (-r ^ 2 / (4 * (V + 2 * r))) := by
  apply history_noise_freedman (PMF.pure G) (fun _ => step)
    (fun _ H => (currentCodegree H u v : ℝ)) (codegreeVarianceRate u v) T 2
    (by norm_num)
  · intro j _ H hH J hJ
    rw [markovLaw_triangle_step] at hH
    exact codegree_centered_range ((evolve_support_subset G j hH).trans hG) u v hJ
  · intro j _ H hH
    rw [markovLaw_triangle_step] at hH
    exact codegree_centered_variance ((evolve_support_subset G j hH).trans hG) u v
  · exact hr
  · exact hV

end SharpTerminalLeave

end

end OAI
