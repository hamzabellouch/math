import Mathlib

namespace OAI

noncomputable section

namespace CylinderCovering.ThresholdInverse

section Normed
variable {E : Type*} [NormedAddCommGroup E]

theorem inverse_norm_bound {p q u v : E} {c : ℝ}
    (hc : c < 1)
    (h : ‖(p - q) - (u - v)‖ ≤ c * ‖p - q‖) :
    ‖p - q‖ ≤ ‖u - v‖ / (1 - c) := by
  have htri : ‖p - q‖ ≤ ‖(p - q) - (u - v)‖ + ‖u - v‖ :=
    calc
      ‖p - q‖ = ‖((p - q) - (u - v)) + (u - v)‖ := by congr 1; abel
      _ ≤ ‖(p - q) - (u - v)‖ + ‖u - v‖ := norm_add_le _ _
  apply (le_div_iff₀ (by linarith : 0 < 1 - c)).2
  nlinarith

theorem inverse_remainder_bound {p q u v : E} {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c < 1)
    (h : ‖(p - q) - (u - v)‖ ≤ c * ‖p - q‖) :
    ‖(p - q) - (u - v)‖ ≤ c / (1 - c) * ‖u - v‖ := by
  calc
    ‖(p - q) - (u - v)‖ ≤ c * ‖p - q‖ := h
    _ ≤ c * (‖u - v‖ / (1 - c)) :=
      mul_le_mul_of_nonneg_left (inverse_norm_bound hc h) hc0
    _ = c / (1 - c) * ‖u - v‖ := by ring

theorem inverse_unique {p q : E} {c : ℝ}
    (hc : c < 1) (h : ‖p - q‖ ≤ c * ‖p - q‖) : p = q := by
  have hn := norm_nonneg (p - q)
  have hz : ‖p - q‖ = 0 := by nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

variable [NormedSpace ℝ E]

theorem inverse_equations_estimate {W : E → E} {p q u v : E} {k L : ℝ}
    (hW : ‖W p - W q‖ ≤ L * ‖p - q‖)
    (hp : p + k • W p = u) (hq : q + k • W q = v) :
    ‖(p - q) - (u - v)‖ ≤ (|k| * L) * ‖p - q‖ := by
  have heq : (p - q) - (u - v) = -(k • (W p - W q)) := by
    rw [← hp, ← hq, smul_sub]
    abel
  rw [heq, norm_neg, norm_smul, Real.norm_eq_abs]
  calc
    |k| * ‖W p - W q‖ ≤ |k| * (L * ‖p - q‖) :=
      mul_le_mul_of_nonneg_left hW (abs_nonneg k)
    _ = (|k| * L) * ‖p - q‖ := by ring

theorem existsUnique_inverse_on_complete
    {s : Set E} (hs : IsComplete s) (hne : s.Nonempty)
    {W : E → E} {y : E} {k L : ℝ}
    (hL : 0 ≤ L) (hc : |k| * L < 1)
    (hW : ∀ p ∈ s, ∀ q ∈ s, ‖W p - W q‖ ≤ L * ‖p - q‖)
    (hmaps : Set.MapsTo (fun p => y - k • W p) s s) :
    ∃! p : E, p ∈ s ∧ p + k • W p = y := by
  let c : NNReal := ⟨|k| * L, mul_nonneg (abs_nonneg k) hL⟩
  have hcontract : ContractingWith c (hmaps.restrict (fun p => y - k • W p) s s) := by
    refine ⟨hc, LipschitzWith.of_dist_le_mul ?_⟩
    intro p q
    change dist (y - k • W p) (y - k • W q) ≤ (|k| * L) * dist (p : E) (q : E)
    rw [dist_sub_left, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      dist_eq_norm]
    calc
      |k| * ‖W p - W q‖ ≤ |k| * (L * ‖(p : E) - q‖) :=
        mul_le_mul_of_nonneg_left (hW p p.property q q.property) (abs_nonneg k)
      _ = (|k| * L) * ‖(p : E) - q‖ := by ring
  obtain ⟨x, hxs⟩ := hne
  obtain ⟨p, hps, hp, -⟩ := ContractingWith.exists_fixedPoint' hs hmaps hcontract
    hxs (edist_ne_top _ _)
  have hpeq : p + k • W p = y := by
    have h := hp.eq
    change y - k • W p = p at h
    exact (eq_sub_iff_add_eq).mp h.symm
  refine ⟨p, ⟨hps, hpeq⟩, ?_⟩
  intro q hq
  have he := inverse_equations_estimate (hW q hq.1 p hps) hq.2 hpeq
  simp only [sub_self, sub_zero] at he
  exact inverse_unique hc he

end Normed

theorem norm_vertical_difference (y t t' : ℝ) :
    ‖(WithLp.toLp 2 ![y, t'] : EuclideanSpace ℝ (Fin 2)) -
      WithLp.toLp 2 ![y, t]‖ = |t' - t| := by
  have heq : (WithLp.toLp 2 ![y, t'] : EuclideanSpace ℝ (Fin 2)) -
      WithLp.toLp 2 ![y, t] = PiLp.single 2 1 (t' - t) := by
    ext i
    fin_cases i <;> simp
  rw [heq, PiLp.norm_single, Real.norm_eq_abs]

theorem inverse_height_strict
    {W : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {p q : EuclideanSpace ℝ (Fin 2)} {y t t' k L : ℝ}
    (hL : 0 ≤ L) (hc : |k| * L < 1 / 2)
    (hW : ‖W p - W q‖ ≤ L * ‖p - q‖)
    (hp : p + k • W p = WithLp.toLp 2 ![y, t'])
    (hq : q + k • W q = WithLp.toLp 2 ![y, t])
    (ht : t < t') : q 1 < p 1 := by
  have hc0 : 0 ≤ |k| * L := mul_nonneg (abs_nonneg k) hL
  have hc1 : |k| * L < 1 := by linarith
  have he := inverse_equations_estimate hW hp hq
  have hr := inverse_remainder_bound hc0 hc1 he
  rw [norm_vertical_difference, abs_of_pos (sub_pos.mpr ht)] at hr
  have ha := PiLp.norm_apply_le
    ((p - q) - ((WithLp.toLp 2 ![y, t'] : EuclideanSpace ℝ (Fin 2)) -
      WithLp.toLp 2 ![y, t])) 1
  have habs : |p 1 - q 1 - (t' - t)| ≤
      |k| * L / (1 - |k| * L) * (t' - t) := by
    simpa [Real.norm_eq_abs] using ha.trans hr
  have hratio : |k| * L / (1 - |k| * L) < 1 := by
    apply (div_lt_iff₀ (by linarith : 0 < 1 - |k| * L)).2
    linarith
  have hlt : |k| * L / (1 - |k| * L) * (t' - t) < t' - t := by
    nlinarith
  have hlo := (abs_le.mp habs).1
  linarith

end CylinderCovering.ThresholdInverse

end

end OAI
