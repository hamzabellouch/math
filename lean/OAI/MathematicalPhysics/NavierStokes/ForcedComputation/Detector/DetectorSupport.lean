import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorReferenceBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.TorusGeometry

namespace OAI

/-! Every nonzero point of the transported bump stays within the fixed
torus clearance of its central characteristic. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem detectorBump_near_lift {b : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1 / 16)
    {q : Plane} (hn : detectorBump b q ≠ 0) :
    ∃ k : Fin 2 → ℤ,
      ‖planeCoordinates.symm (q - (fun j => (k j : ℝ)) - ![1 / 4, 1 / 4])‖ ≤ 2 * b := by
  let k : Fin 2 → ℤ := fun j => ⌊q j⌋
  let q₀ : Plane := q - fun j => (k j : ℝ)
  have hq : q₀ + (fun j => (k j : ℝ)) = q := by dsimp only [q₀]; abel
  have hp := detectorBump_periodic b q₀ k
  rw [hq] at hp
  have hn₀ : detectorBump b q₀ ≠ 0 := fun hz => hn (hp.trans hz)
  have hc : ∀ j, q₀ j ∈ Icc (0 : ℝ) 1 := by
    intro j
    change q j - (⌊q j⌋ : ℤ) ∈ Icc (0 : ℝ) 1
    exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hclose := detectorBump_support_in_chart hb hb₁ hc hn₀
  have hpi : ‖q₀ - ![1 / 4, 1 / 4]‖ ≤ b := by
    apply (pi_norm_le_iff_of_nonneg hb.le).mpr
    intro j
    have hj : (![1 / 4, 1 / 4] : Plane) j = 1 / 4 := by fin_cases j <;> rfl
    simpa only [Pi.sub_apply, hj, Real.norm_eq_abs] using (hclose j).le
  exact ⟨k, (planeCoordinates_symm_norm_le _).trans
    (mul_le_mul_of_nonneg_left hpi (by norm_num))⟩

theorem detector_transport_radius (L n : ℕ) :
    (expansion L : ℝ) ^ (n + 1) * (2 * (width L n : ℝ)) ≤ 1 / 32 := by
  have he : (width L n : ℝ) * (expansion L : ℝ) ^ (n + 1) =
      (1 / 1000000 : ℝ) * (1 / 2 : ℝ) ^ (n + 1) := by
    have h := congrArg (fun r : ℚ => (r : ℝ)) (transported_width L n)
    simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_one, Rat.cast_ofNat, Nat.cast_pow] using h
  have hp : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

theorem planar_flow_distance_bound {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hv : PlanarVariations V Ψ)
    (hV : ∀ s, ContDiff ℝ ∞ (V s)) (L N : ℕ)
    (h₁ : ∀ s x, ‖fderiv ℝ (euclideanMap (V s)) x‖ ≤ (L : ℝ))
    {s : ℝ} (hs : 0 ≤ s) (hsN : s ≤ N) (x y : Plane) :
    ‖planeCoordinates.symm (Ψ 0 s x - Ψ 0 s y)‖ ≤
      (expansion L : ℝ) ^ N * ‖planeCoordinates.symm (x - y)‖ := by
  have hE := hv.euclidean hV
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (s := (univ : Set EuclideanPlane))
    (fun z _ => (hE.smooth 0 s).differentiable (by simp) z)
    (fun z _ => (euclidean_first_variation_operator hE h₁ 0 z hs).trans
      (exp_time_le_expansion_pow L N hsN))
    (convex_univ : Convex ℝ (univ : Set EuclideanPlane))
    (mem_univ (planeCoordinates.symm y)) (mem_univ (planeCoordinates.symm x))
  simpa only [euclideanMap, ContinuousLinearEquiv.apply_symm_apply, ← map_sub] using h

theorem detectorReference_support_near {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ)
    (hv : PlanarVariations V Ψ) (hV : ∀ s, ContDiff ℝ ∞ (V s))
    (hp : ∀ s, PlanePeriodic (V s)) (C L n : ℕ)
    (h₁ : ∀ s x, ‖fderiv ℝ (euclideanMap (V s)) x‖ ≤ (L : ℝ))
    {t : ℝ} {y : Plane} (hn : detectorReference Ψ C L n t y ≠ 0) :
    torusNorm (y - Ψ 0 (detectorPhase C L n t) ![1 / 4, 1 / 4]) ≤ 1 / 32 := by
  let σ := detectorPhase C L n t
  let q := Ψ σ (-σ) y
  have hnq : detectorBump (width L n : ℝ) q ≠ 0 := (mul_ne_zero_iff.mp hn).2
  obtain ⟨k, hk⟩ := detectorBump_near_lift (by exact_mod_cast width_pos L n)
    (detector_width_small L n) hnq
  let q₀ : Plane := q - fun j => (k j : ℝ)
  have hq : q₀ + (fun j => (k j : ℝ)) = q := by dsimp only [q₀]; abel
  have hy : y = Ψ 0 σ q₀ + (fun j => (k j : ℝ)) := by
    calc
      y = Ψ 0 σ q := by simpa only [zero_add] using (hΨ.inverse_right 0 σ y).symm
      _ = Ψ 0 σ (q₀ + fun j => (k j : ℝ)) := by rw [hq]
      _ = _ := planar_transition_equivariant hΨ hp 0 σ q₀ k
  have hσ := detectorPhase_range C L n t
  have hdist := planar_flow_distance_bound hv hV L (n + 1) h₁ hσ.1
    (by simpa only [Nat.cast_add, Nat.cast_one] using hσ.2) q₀ ![1 / 4, 1 / 4]
  calc
    _ ≤ ‖planeCoordinates.symm
        ((y - Ψ 0 σ ![1 / 4, 1 / 4]) - fun j => (k j : ℝ))‖ := torusNorm_le_lattice _ k
    _ = ‖planeCoordinates.symm (Ψ 0 σ q₀ - Ψ 0 σ ![1 / 4, 1 / 4])‖ := by
      rw [hy]
      congr 2
      abel
    _ ≤ (expansion L : ℝ) ^ (n + 1) * (2 * (width L n : ℝ)) :=
      hdist.trans (mul_le_mul_of_nonneg_left hk (by positivity))
    _ ≤ 1 / 32 := detector_transport_radius L n

end ForcedComputation.VelocityDetector

end

end OAI
