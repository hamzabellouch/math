import OAI.Analysis.MarkovType.JConvexityBasic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity

namespace OAI

namespace MarkovSuperreflexivity

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem seminorm_sub_le (p : Seminorm ℝ X) (x y : X) :
    p (x - y) ≤ p x + p y := by
  simpa only [sub_eq_add_neg, map_neg_eq_map] using map_add_le_add p x (-y)

private theorem seminorm_normalize (p : Seminorm ℝ X) (x : X) (hx : 0 < p x) :
    p ((p x)⁻¹ • x) = 1 := by
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx),
    inv_mul_cancel₀ (ne_of_gt hx)]

private theorem seminorm_normalize_error (p : Seminorm ℝ X) (x : X)
    (hx : 0 < p x) (hx1 : p x ≤ 1) :
    p (x - (p x)⁻¹ • x) = 1 - p x := by
  have hcancel : (p x) • ((p x)⁻¹ • x) = x := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hx), one_smul]
  have hvec : x - (p x)⁻¹ • x = (p x - 1) • ((p x)⁻¹ • x) := by
    rw [sub_smul, hcancel, one_smul]
  rw [hvec, map_smul_eq_mul, Real.norm_eq_abs, seminorm_normalize p x hx,
    mul_one, abs_of_nonpos (sub_nonpos.mpr hx1)]
  ring

theorem unitSphere_nonsquare_of_uniformSmooth {p : Seminorm ℝ X}
    (h : UniformSmooth p) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ x y : X, p x = 1 → p y = 1 →
        p (x + y) ≤ 2 * (1 - δ) ∨ p (x - y) ≤ 2 * (1 - δ) := by
  obtain ⟨ρ, hρ, hsmooth⟩ := h (1 / 2) (by norm_num)
  let t : ℝ := min (ρ / 2) (1 / 2)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have htρ2 : t ≤ ρ / 2 := min_le_left _ _
  have htρ : t < ρ := by linarith
  have hthalf : t ≤ 1 / 2 := min_le_right _ _
  have ht1 : t ≤ 1 := by linarith
  let δ : ℝ := t / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ < 1 := by dsimp [δ]; linarith
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro x y hx hy
  by_cases hplus : p (x + y) ≤ 2 * (1 - δ)
  · exact Or.inl hplus
  by_cases hminus : p (x - y) ≤ 2 * (1 - δ)
  · exact Or.inr hminus
  have hplus' : 2 * (1 - δ) < p (x + y) := lt_of_not_ge hplus
  have hminus' : 2 * (1 - δ) < p (x - y) := lt_of_not_ge hminus
  have hscale : p ((1 - t) • y) = 1 - t := by
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht1),
      hy, mul_one]
  have hscalar : t + (1 - t) = 1 := by ring
  have hvecPlus : x + y = (x + t • y) + (1 - t) • y := by
    rw [add_assoc, ← add_smul, hscalar, one_smul]
  have hvecMinus : x - y = (x - t • y) - (1 - t) • y := by
    rw [sub_sub, ← add_smul, hscalar, one_smul]
  have hboundPlus : p (x + y) ≤ p (x + t • y) + (1 - t) := by
    calc
      p (x + y) = p ((x + t • y) + (1 - t) • y) := congrArg p hvecPlus
      _ ≤ p (x + t • y) + p ((1 - t) • y) := map_add_le_add p _ _
      _ = p (x + t • y) + (1 - t) := by rw [hscale]
  have hboundMinus : p (x - y) ≤ p (x - t • y) + (1 - t) := by
    calc
      p (x - y) = p ((x - t • y) - (1 - t) • y) := congrArg p hvecMinus
      _ ≤ p (x - t • y) + p ((1 - t) • y) := seminorm_sub_le p _ _
      _ = p (x - t • y) + (1 - t) := by rw [hscale]
  have havg := hsmooth t ht htρ x y hx hy
  dsimp only [δ] at hplus' hminus'
  exfalso
  linarith

theorem uniformlyNonsquare_of_unitSphere {p : Seminorm ℝ X}
    (h : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ x y : X, p x = 1 → p y = 1 →
        p (x + y) ≤ 2 * (1 - δ) ∨ p (x - y) ≤ 2 * (1 - δ)) :
    UniformlyNonsquare p := by
  obtain ⟨δ, hδ, _, hsphere⟩ := h
  let ε : ℝ := min (δ / 4) (1 / 8)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεδ : ε ≤ δ / 4 := min_le_left _ _
  have hεsmall : ε ≤ 1 / 8 := min_le_right _ _
  have hε1 : ε < 1 := by linarith
  refine ⟨ε, hε, hε1, ?_⟩
  intro x y hx hy
  by_cases hplus : p (x + y) ≤ 2 * (1 - ε)
  · exact Or.inl hplus
  by_cases hminus : p (x - y) ≤ 2 * (1 - ε)
  · exact Or.inr hminus
  have hplus' : 2 * (1 - ε) < p (x + y) := lt_of_not_ge hplus
  have hminus' : 2 * (1 - ε) < p (x - y) := lt_of_not_ge hminus
  have hadd : p (x + y) ≤ p x + p y := map_add_le_add p _ _
  have hxpos : 0 < p x := by linarith
  have hypos : 0 < p y := by linarith
  let u : X := (p x)⁻¹ • x
  let v : X := (p y)⁻¹ • y
  have hu : p u = 1 := seminorm_normalize p x hxpos
  have hv : p v = 1 := seminorm_normalize p y hypos
  have hxu : p (x - u) ≤ 2 * ε := by
    have he : p (x - u) = 1 - p x := seminorm_normalize_error p x hxpos hx
    linarith
  have hyv : p (y - v) ≤ 2 * ε := by
    have he : p (y - v) = 1 - p y := seminorm_normalize_error p y hypos hy
    linarith
  rcases hsphere u v hu hv with hsum | hdiff
  · have hdecomp : x + y = (u + v) + ((x - u) + (y - v)) := by abel
    have hbound : p (x + y) ≤ p (u + v) + (p (x - u) + p (y - v)) := by
      calc
        p (x + y) = p ((u + v) + ((x - u) + (y - v))) := congrArg p hdecomp
        _ ≤ p (u + v) + p ((x - u) + (y - v)) := map_add_le_add p _ _
        _ ≤ p (u + v) + (p (x - u) + p (y - v)) :=
          add_le_add le_rfl (map_add_le_add p _ _)
    exfalso
    linarith
  · have hdecomp : x - y = (u - v) + ((x - u) - (y - v)) := by abel
    have hbound : p (x - y) ≤ p (u - v) + (p (x - u) + p (y - v)) := by
      calc
        p (x - y) = p ((u - v) + ((x - u) - (y - v))) := congrArg p hdecomp
        _ ≤ p (u - v) + p ((x - u) - (y - v)) := map_add_le_add p _ _
        _ ≤ p (u - v) + (p (x - u) + p (y - v)) :=
          add_le_add le_rfl (seminorm_sub_le p _ _)
    exfalso
    linarith

theorem UniformSmooth.uniformlyNonsquare {p : Seminorm ℝ X} (h : UniformSmooth p) :
    UniformlyNonsquare p :=
  uniformlyNonsquare_of_unitSphere (unitSphere_nonsquare_of_uniformSmooth h)

theorem UniformSmooth.jConvex {p : Seminorm ℝ X} (h : UniformSmooth p) : JConvex p :=
  h.uniformlyNonsquare.jConvex

end MarkovSuperreflexivity

end OAI
