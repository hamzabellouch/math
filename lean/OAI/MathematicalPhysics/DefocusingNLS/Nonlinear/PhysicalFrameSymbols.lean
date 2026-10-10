import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSymbolProducts
import OAI.MathematicalPhysics.DefocusingNLS.Profile.CartesianTransportSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalFrame

namespace OAI

/-! # Symbol bounds for the fourteen physical profile directions -/

open scoped ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem HasCartesianSymbol.add {σ : ℝ} {f g : E → ℂ}
    (hf : HasCartesianSymbol σ f) (hg : HasCartesianSymbol σ g) :
    HasCartesianSymbol σ (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  intro n
  obtain ⟨A, hA, ha⟩ := hf.2 n
  obtain ⟨B, hB, hb⟩ := hg.2 n
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro x hx
  change ‖iteratedFDeriv ℝ n (f + g) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (hf.1.contDiffAt.of_le (by simp)) (hg.1.contDiffAt.of_le (by simp))]
  exact (norm_add_le _ _).trans (by nlinarith only [ha x hx, hb x hx])

theorem HasCartesianSymbol.global_profile_bound (a : ℝ) (ha : 0 < a) {Q : E → ℂ}
    (hQ : HasCartesianSymbol (-2 * a) Q) :
    ∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ y : E, y ≠ 0 →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ)) := by
  intro n
  obtain ⟨D, hD, hd⟩ := hQ.2 n
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn
    ((hQ.1.of_le (by simp : (n : ℕ∞ω) ≤ ∞)).continuous_iteratedFDeriv'.continuousOn)
  let B := max (max C 0) D
  have hB : 0 ≤ B := (le_max_right C 0).trans (le_max_left _ _)
  refine ⟨B, hB, ?_⟩
  intro y hy
  by_cases hlarge : 1 ≤ ‖y‖
  · exact (hd y hlarge).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  · have hsmall : ‖y‖ ≤ 1 := (lt_of_not_ge hlarge).le
    have hcore : ‖iteratedFDeriv ℝ n Q y‖ ≤ B :=
      (hC y (by simpa only [Metric.mem_closedBall, dist_zero_right] using hsmall)).trans
        ((le_max_left C 0).trans (le_max_left _ _))
    have hp : 1 ≤ ‖y‖ ^ (-2 * a - (n : ℝ)) := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hy) hsmall
          (show -2 * a - (n : ℝ) ≤ 0 by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    exact hcore.trans (le_mul_of_one_le_right hB hp)

theorem HasCartesianSymbol.profile_directional (a : ℝ) {Q : E → ℂ}
    (hQ : HasCartesianSymbol (-2 * a) Q) (v : E) :
    HasCartesianSymbol (-2 * a) (cartesianDerivative v Q) := by
  refine ⟨cartesianDerivative_contDiff Q hQ.1 v, ?_⟩
  have hb := cartesianDerivative_symbol_decay a Q hQ.1
    (fun n => let ⟨D, _, hd⟩ := hQ.2 n; ⟨D, hd⟩) v
  intro n
  obtain ⟨D, hd⟩ := hb n
  exact ⟨max D 0, le_max_right _ _, fun y hy => (hd y hy).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))⟩

theorem HasCartesianSymbol.profile_transport (a : ℝ) (ha : 0 < a) {Q : E → ℂ}
    (hQ : HasCartesianSymbol (-2 * a) Q) :
    HasCartesianSymbol (-2 * a) (cartesianTransport Q) := by
  refine ⟨cartesianTransport_contDiff Q hQ.1, ?_⟩
  have hb := cartesianTransport_global_symbol a Q hQ.1 (hQ.global_profile_bound a ha)
  intro n
  obtain ⟨D, hD, hd⟩ := hb n
  exact ⟨D, hD, fun y hy => hd y (norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le zero_lt_one hy)))⟩

theorem physical_symmetry_frame_symbol (a b : ℝ) (ha : 0 < a) {Q : E → ℂ}
    (hQ : HasCartesianSymbol (-2 * a) Q) (p : ProfileSymmetryParameters) :
    HasCartesianSymbol (-2 * a) (fun y =>
      (p.1 : ℂ) * (Complex.I * Q y) +
      (p.2.2 : ℂ) * (((a : ℂ) - Complex.I * (b : ℂ)) * Q y + cartesianTransport Q y) +
      cartesianDerivative p.2.1 Q y) :=
  (((hQ.const_mul Complex.I).const_mul p.1).add
    (((hQ.const_mul ((a : ℂ) - Complex.I * (b : ℂ))).add
      (hQ.profile_transport a ha)).const_mul p.2.2)).add (hQ.profile_directional a p.2.1)

end DefocusingNLS

end OAI
