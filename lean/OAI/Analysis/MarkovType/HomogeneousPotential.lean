import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace MarkovSuperreflexivity

variable {E : Type*} [sectionNormedAddCommGroupE : NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

private theorem subadditive_of_convex_unit_sublevel (N : E → ℝ)
    (hN : ∀ x, 0 ≤ N x)
    (hsmul : ∀ (a : ℝ) x, N (a • x) = ‖a‖ * N x)
    (hconv : Convex ℝ {x | N x ≤ 1}) (x y : E) :
    N (x + y) ≤ N x + N y := by
  have happrox (ε : ℝ) (hε : 0 < ε) :
      N (x + y) ≤ N x + N y + 2 * ε := by
    let a := N x + ε
    let b := N y + ε
    have ha : 0 < a := add_pos_of_nonneg_of_pos (hN x) hε
    have hb : 0 < b := add_pos_of_nonneg_of_pos (hN y) hε
    have hs : 0 < a + b := add_pos ha hb
    have hu : N (a⁻¹ • x) ≤ 1 := by
      calc
        N (a⁻¹ • x) = N x / a := by
          rw [hsmul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha),
            div_eq_mul_inv, mul_comm]
        _ ≤ 1 := (div_le_one ha).mpr (le_add_of_nonneg_right hε.le)
    have hv : N (b⁻¹ • y) ≤ 1 := by
      calc
        N (b⁻¹ • y) = N y / b := by
          rw [hsmul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb),
            div_eq_mul_inv, mul_comm]
        _ ≤ 1 := (div_le_one hb).mpr (le_add_of_nonneg_right hε.le)
    have hweights : a / (a + b) + b / (a + b) = 1 := by
      rw [← add_div, div_self hs.ne']
    have hc := hconv hu hv (div_nonneg ha.le hs.le)
      (div_nonneg hb.le hs.le) hweights
    change N ((a / (a + b)) • (a⁻¹ • x) +
      (b / (a + b)) • (b⁻¹ • y)) ≤ 1 at hc
    have hca : (a / (a + b)) * a⁻¹ = (a + b)⁻¹ := by
      field_simp [ha.ne', hs.ne']
    have hcb : (b / (a + b)) * b⁻¹ = (a + b)⁻¹ := by
      field_simp [hb.ne', hs.ne']
    have hvec : (a / (a + b)) • (a⁻¹ • x) +
        (b / (a + b)) • (b⁻¹ • y) = (a + b)⁻¹ • (x + y) := by
      simp only [smul_smul, hca, hcb, smul_add]
    rw [hvec, hsmul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)] at hc
    have hquot : N (x + y) / (a + b) ≤ 1 := by
      simpa only [div_eq_mul_inv, mul_comm] using hc
    have hbound := (div_le_one hs).mp hquot
    dsimp [a, b] at hbound
    linarith only [hbound]
  by_contra h
  have hgap : 0 < N (x + y) - (N x + N y) := sub_pos.mpr (lt_of_not_ge h)
  have hε : 0 < (N (x + y) - (N x + N y)) / 4 := by
    linarith only [hgap]
  have hbound := happrox ((N (x + y) - (N x + N y)) / 4) hε
  linarith only [hbound, hgap]

noncomputable def potentialRoot (q : ℝ) (F : E → ℝ) (x : E) : ℝ :=
  F x ^ (1 / q)

omit sectionNormedAddCommGroupE sectionNormedSpaceℝE in
theorem potentialRoot_nonneg [NormedAddCommGroup E] [NormedSpace ℝ E] (q : ℝ) (F : E → ℝ)
    (hF : ∀ x, 0 ≤ F x) (x : E) : 0 ≤ potentialRoot q F x :=
  Real.rpow_nonneg (hF x) _

omit sectionNormedAddCommGroupE sectionNormedSpaceℝE in
theorem potentialRoot_rpow [NormedAddCommGroup E] [NormedSpace ℝ E] (q : ℝ) (hq : 0 < q) (F : E → ℝ)
    (hF : ∀ x, 0 ≤ F x) (x : E) : (potentialRoot q F x) ^ q = F x := by
  have hexp : (1 / q) * q = (1 : ℝ) := by field_simp [hq.ne']
  rw [potentialRoot, ← Real.rpow_mul (hF x), hexp, Real.rpow_one]

theorem potentialRoot_smul (q : ℝ) (hq : 0 < q) (F : E → ℝ)
    (hF : ∀ x, 0 ≤ F x)
    (hhom : ∀ (a : ℝ) x, F (a • x) = ‖a‖ ^ q * F x)
    (a : ℝ) (x : E) : potentialRoot q F (a • x) = ‖a‖ * potentialRoot q F x := by
  have hexp : q * (1 / q) = (1 : ℝ) := by field_simp [hq.ne']
  simp only [potentialRoot, hhom]
  rw [Real.mul_rpow (Real.rpow_nonneg (norm_nonneg a) q) (hF x),
    ← Real.rpow_mul (norm_nonneg a), hexp, Real.rpow_one]

theorem potentialRoot_le_iff (q : ℝ) (hq : 0 < q) (F : E → ℝ)
    (hF : ∀ x, 0 ≤ F x) (x : E) (b : ℝ) (hb : 0 ≤ b) :
    potentialRoot q F x ≤ b ↔ F x ≤ b ^ q := by
  rw [← Real.rpow_le_rpow_iff (potentialRoot_nonneg q F hF x) hb hq,
    potentialRoot_rpow q hq F hF x]

theorem le_potentialRoot_iff (q : ℝ) (hq : 0 < q) (F : E → ℝ)
    (hF : ∀ x, 0 ≤ F x) (x : E) (b : ℝ) (hb : 0 ≤ b) :
    b ≤ potentialRoot q F x ↔ b ^ q ≤ F x := by
  rw [← Real.rpow_le_rpow_iff hb (potentialRoot_nonneg q F hF x) hq,
    potentialRoot_rpow q hq F hF x]

private theorem potentialRoot_unit_sublevel_convex
    (q : ℝ) (hq : 0 < q) (F : E → ℝ) (hF : ∀ x, 0 ≤ F x)
    (hconv : ConvexOn ℝ Set.univ F) :
    Convex ℝ {x | potentialRoot q F x ≤ 1} := by
  intro x hx y hy a b ha hb hab
  have hxF : F x ≤ 1 := by
    simpa only [Real.one_rpow] using
      (potentialRoot_le_iff q hq F hF x 1 zero_le_one).mp hx
  have hyF : F y ≤ 1 := by
    simpa only [Real.one_rpow] using
      (potentialRoot_le_iff q hq F hF y 1 zero_le_one).mp hy
  have hFcombo : F (a • x + b • y) ≤ 1 := by
    calc
      F (a • x + b • y) ≤ a * F x + b * F y := by
        simpa only [smul_eq_mul] using
          hconv.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
      _ ≤ a * 1 + b * 1 := add_le_add
        (mul_le_mul_of_nonneg_left hxF ha) (mul_le_mul_of_nonneg_left hyF hb)
      _ = 1 := by simpa only [mul_one] using hab
  exact (potentialRoot_le_iff q hq F hF (a • x + b • y) 1 zero_le_one).mpr
    (by simpa only [Real.one_rpow] using hFcombo)

noncomputable def potentialSeminorm
    (q : ℝ) (hq : 0 < q) (F : E → ℝ) (hF : ∀ x, 0 ≤ F x)
    (hhom : ∀ (a : ℝ) x, F (a • x) = ‖a‖ ^ q * F x)
    (hconv : ConvexOn ℝ Set.univ F) : Seminorm ℝ E :=
  Seminorm.of (potentialRoot q F)
    (subadditive_of_convex_unit_sublevel (potentialRoot q F)
      (potentialRoot_nonneg q F hF) (potentialRoot_smul q hq F hF hhom)
      (potentialRoot_unit_sublevel_convex q hq F hF hconv))
    (potentialRoot_smul q hq F hF hhom)

@[simp] theorem potentialSeminorm_apply
    (q : ℝ) (hq : 0 < q) (F : E → ℝ) (hF : ∀ x, 0 ≤ F x)
    (hhom : ∀ (a : ℝ) x, F (a • x) = ‖a‖ ^ q * F x)
    (hconv : ConvexOn ℝ Set.univ F) (x : E) :
    potentialSeminorm q hq F hF hhom hconv x = F x ^ (1 / q) := rfl

theorem potentialSeminorm_rpow
    (q : ℝ) (hq : 0 < q) (F : E → ℝ) (hF : ∀ x, 0 ≤ F x)
    (hhom : ∀ (a : ℝ) x, F (a • x) = ‖a‖ ^ q * F x)
    (hconv : ConvexOn ℝ Set.univ F) (x : E) :
    (potentialSeminorm q hq F hF hhom hconv x) ^ q = F x :=
  potentialRoot_rpow q hq F hF x

theorem potentialSeminorm_le_iff
    (q : ℝ) (hq : 0 < q) (F : E → ℝ) (hF : ∀ x, 0 ≤ F x)
    (hhom : ∀ (a : ℝ) x, F (a • x) = ‖a‖ ^ q * F x)
    (hconv : ConvexOn ℝ Set.univ F) (x : E) (b : ℝ) (hb : 0 ≤ b) :
    potentialSeminorm q hq F hF hhom hconv x ≤ b ↔ F x ≤ b ^ q :=
  potentialRoot_le_iff q hq F hF x b hb

theorem le_potentialSeminorm_iff
    (q : ℝ) (hq : 0 < q) (F : E → ℝ) (hF : ∀ x, 0 ≤ F x)
    (hhom : ∀ (a : ℝ) x, F (a • x) = ‖a‖ ^ q * F x)
    (hconv : ConvexOn ℝ Set.univ F) (x : E) (b : ℝ) (hb : 0 ≤ b) :
    b ≤ potentialSeminorm q hq F hF hhom hconv x ↔ b ^ q ≤ F x :=
  le_potentialRoot_iff q hq F hF x b hb

end MarkovSuperreflexivity

end OAI
