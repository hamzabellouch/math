import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

namespace OAI

/-!
# Sublinear cocycle bounds from compact coboundary approximation

Compact-uniform approximation by coboundaries makes an isometric cocycle
sublinear on words of linearly bounded length.
-/

namespace PolycyclicRecognition

variable {G E : Type*} [Group G] [NormedAddCommGroup E]
  [DistribMulAction G E] [IsIsometricSMul G E]

theorem norm_isometric_action (g : G) (v : E) : ‖g • v‖ = ‖v‖ := by
  simpa only [smul_zero, dist_zero_right] using dist_smul g v (0 : E)

/-- The left cocycle convention for an isometric representation. -/
def IsCocycle (b : G → E) : Prop := ∀ g h, b (g * h) = b g + g • b h

omit [IsIsometricSMul G E] in
theorem IsCocycle.map_one {b : G → E} (hb : IsCocycle b) : b 1 = 0 := by
  have h := hb 1 1
  simp only [one_mul, one_smul] at h
  apply add_left_cancel (a := b 1)
  simpa only [add_zero] using h.symm

omit [IsIsometricSMul G E] in
/-- Coboundary correction preserves the cocycle identity. -/
theorem IsCocycle.corrected {b : G → E} (hb : IsCocycle b) (φ : E) :
    IsCocycle (fun g => b g + g • φ - φ) := by
  intro g h
  dsimp only
  rw [hb g h, mul_smul, smul_sub, smul_add]
  abel

theorem IsCocycle.norm_word_le {b : G → E} (hb : IsCocycle b)
    (Q : Set G) {ε : ℝ} (hQ : ∀ g ∈ Q, ‖b g‖ ≤ ε)
    (l : List G) (hl : ∀ g ∈ l, g ∈ Q) : ‖b l.prod‖ ≤ (l.length : ℝ) * ε := by
  induction l with
  | nil => simp [hb.map_one]
  | cons g l ih =>
    have htail : ∀ h ∈ l, h ∈ Q := fun h hh => hl h (by simp [hh])
    calc
      ‖b (g :: l).prod‖ = ‖b g + g • b l.prod‖ := by rw [List.prod_cons, hb g l.prod]
      _ ≤ ‖b g‖ + ‖g • b l.prod‖ := norm_add_le _ _
      _ = ‖b g‖ + ‖b l.prod‖ := by rw [norm_isometric_action]
      _ ≤ ε + (l.length : ℝ) * ε := add_le_add (hQ g (hl g (by simp))) (ih htail)
      _ = ((g :: l).length : ℝ) * ε := by simp [add_mul]; ring

/-- The error of removing a coboundary is at most twice the vector norm,
uniformly over the acting group. -/
theorem norm_le_corrected_add (b : G → E) (φ : E) (g : G) :
    ‖b g‖ ≤ ‖b g + g • φ - φ‖ + 2 * ‖φ‖ := by
  have heq : b g = (b g + g • φ - φ) - g • φ + φ := by abel
  calc
    ‖b g‖ = ‖(b g + g • φ - φ) - g • φ + φ‖ := congrArg norm heq
    _ ≤ ‖(b g + g • φ - φ) - g • φ‖ + ‖φ‖ := norm_add_le _ _
    _ ≤ (‖b g + g • φ - φ‖ + ‖g • φ‖) + ‖φ‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ = _ := by rw [norm_isometric_action]; ring

/-- The concrete word estimate used after reduced cohomology vanishing. The
approximating vector is fixed before the word length tends to infinity. -/
theorem IsCocycle.norm_word_le_of_coboundary {b : G → E} (hb : IsCocycle b)
    (Q : Set G) (φ : E) {ε : ℝ}
    (hQ : ∀ g ∈ Q, ‖b g + g • φ - φ‖ ≤ ε)
    (l : List G) (hl : ∀ g ∈ l, g ∈ Q) :
    ‖b l.prod‖ ≤ (l.length : ℝ) * ε + 2 * ‖φ‖ :=
  (norm_le_corrected_add b φ l.prod).trans
    (add_le_add ((hb.corrected φ).norm_word_le Q hQ l hl) le_rfl)

/-- Compact-uniform coboundary approximation implies a global sublinear
estimate. The length and word-factorization hypotheses are explicit. -/
theorem IsCocycle.sublinear_of_coboundary_approximation
    {b : G → E} (hb : IsCocycle b) (Q : Set G) (length : G → ℝ)
    (hlen : ∀ g, 0 ≤ length g) {a : ℝ} (ha : 0 ≤ a)
    (hword : ∀ g, ∃ l : List G, (∀ q ∈ l, q ∈ Q) ∧ l.prod = g ∧
      (l.length : ℝ) ≤ a * length g + a)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ φ : E, ∀ q ∈ Q, ‖b q + q • φ - φ‖ ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g, ‖b g‖ ≤ ε * length g + B := by
  intro ε hε
  let δ := ε / (a + 1)
  have hden : 0 < a + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨φ, hφ⟩ := happrox δ hδ
  have hcoef : a * δ ≤ ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  refine ⟨a * δ + 2 * ‖φ‖, by positivity, ?_⟩
  intro g
  obtain ⟨l, hl, hprod, hlbound⟩ := hword g
  calc
    ‖b g‖ = ‖b l.prod‖ := by rw [hprod]
    _ ≤ (l.length : ℝ) * δ + 2 * ‖φ‖ := hb.norm_word_le_of_coboundary Q φ hφ l hl
    _ ≤ (a * length g + a) * δ + 2 * ‖φ‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hlbound hδ.le) le_rfl
    _ = (a * δ) * length g + (a * δ + 2 * ‖φ‖) := by ring
    _ ≤ ε * length g + (a * δ + 2 * ‖φ‖) :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef (hlen g)) le_rfl

omit [Group G] [DistribMulAction G E] [IsIsometricSMul G E] in
/-- A global sublinear estimate is uniform after division by scale on every
linearly growing metric ball. The additive error is chosen before the scale. -/
theorem uniform_sublinear_on_balls {b : G → E} (length : G → ℝ)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g, ‖b g‖ ≤ ε * length g + B)
    {R : ℝ} (hR : 0 ≤ R) : ∀ ε : ℝ, 0 < ε →
      ∃ r₀ : ℝ, 0 ≤ r₀ ∧ ∀ r, r₀ ≤ r → ∀ g, length g ≤ R * r → ‖b g‖ ≤ ε * r := by
  intro ε hε
  have hden : 0 < 2 * (R + 1) := by linarith
  let δ := ε / (2 * (R + 1))
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨B, hB, hb⟩ := hsub δ hδ
  refine ⟨2 * B / ε, by positivity, ?_⟩
  intro r hr g hg
  have hr0 : 0 ≤ r := (by positivity : 0 ≤ 2 * B / ε).trans hr
  have hBr : 2 * B ≤ r * ε := (div_le_iff₀ hε).mp hr
  have hcoef : δ * R ≤ ε / 2 := by
    dsimp [δ]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  calc
    ‖b g‖ ≤ δ * length g + B := hb g
    _ ≤ δ * (R * r) + B := add_le_add (mul_le_mul_of_nonneg_left hg hδ.le) le_rfl
    _ = (δ * R) * r + B := by ring
    _ ≤ (ε / 2) * r + B := add_le_add (mul_le_mul_of_nonneg_right hcoef hr0) le_rfl
    _ ≤ ε * r := by nlinarith

end PolycyclicRecognition

end OAI
