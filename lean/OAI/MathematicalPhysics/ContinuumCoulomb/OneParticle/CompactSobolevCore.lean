import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SmoothCutoffApproximation

namespace OAI

/-! Compactly supported C1 approximation on the full declared weak-H1
configuration domain. Only the explicitly cited smooth-density input is
conditional; the compactification step is proved here. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

private theorem integral_square_error_triangle {n : ℕ}
    (f g h : Configuration n → ℂ) (hf : MemLp f 2) (hg : MemLp g 2) (hh : MemLp h 2) :
    (∫ x, ‖f x-h x‖^2) ≤ 2*(∫ x, ‖f x-g x‖^2) + 2*(∫ x, ‖g x-h x‖^2) := by
  have hi (v w : Configuration n → ℂ) (hv : MemLp v 2) (hw : MemLp w 2) :
      Integrable (fun x => ‖v x-w x‖^2) :=
    (memLp_two_iff_integrable_sq_norm (hv.sub hw).aestronglyMeasurable).mp (hv.sub hw)
  calc
    _ ≤ ∫ x, 2*‖f x-g x‖^2 + 2*‖g x-h x‖^2 := by
      apply integral_mono (hi f h hf hh) ((hi f g hf hg).const_mul 2 |>.add
        ((hi g h hg hh).const_mul 2))
      intro x
      change ‖f x-h x‖^2 ≤ 2*‖f x-g x‖^2 + 2*‖g x-h x‖^2
      have he : ‖f x-h x‖ ≤ ‖f x-g x‖ + ‖g x-h x‖ := by
        calc
          _ = ‖(f x-g x)+(g x-h x)‖ := by congr 1; ring
          _ ≤ _ := norm_add_le _ _
      have hs := pow_le_pow_left₀ (norm_nonneg _) he 2
      nlinarith [sq_nonneg (‖f x-g x‖ - ‖g x-h x‖)]
    _ = _ := by
      rw [integral_add ((hi f g hf hg).const_mul 2) ((hi g h hg hh).const_mul 2),
        integral_const_mul, integral_const_mul]

theorem h1GraphError_triangle {n : ℕ} (u v w : Coulomb.H1Vector n) :
    h1GraphError u w ≤ 2*h1GraphError u v + 2*h1GraphError v w := by
  have hv := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
    integral_square_error_triangle (u.value s) (v.value s) (w.value s)
      (u.value_L2 s) (v.value_L2 s) (w.value_L2 s))
  have hg := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
    Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) =>
      integral_square_error_triangle (u.gradient s a) (v.gradient s a) (w.gradient s a)
        (u.partial_L2 s a) (v.partial_L2 s a) (w.partial_L2 s a)))
  have h := add_le_add hv hg
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  unfold h1GraphError
  linarith

/-- The smooth-density theorem plus the proved cutoff step gives a compact
core for the actual full weak-H1 vectors, with no symmetry restriction. -/
theorem exists_compact_h1_approximation (hpublished : PublishedSobolevSmoothDensity)
    {n : ℕ} (u : Coulomb.H1Vector n) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Coulomb.H1Vector n,
      (∀ s, ContDiff ℝ 1 (v.value s) ∧ HasCompactSupport (v.value s)) ∧
      (∀ s a x, v.gradient s a x =
        fderiv ℝ (v.value s) x (EuclideanSpace.single a 1)) ∧
      h1GraphError u v < ε := by
  obtain ⟨v, hv, hd, hve⟩ := exists_smooth_h1_approximation hpublished u
    (by linarith : (0 : ℝ) < ε/4)
  obtain ⟨w, hw, hwd, hwe⟩ := exists_compact_approximation_of_smooth v hv hd
    (by linarith : (0 : ℝ) < ε/4)
  refine ⟨w, hw, hwd, ?_⟩
  have h := h1GraphError_triangle u v w
  linarith

end ContinuumCoulomb

end

end OAI
