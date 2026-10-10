import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OAI

/-! # Choosing the source enlargement before the sampled frames -/

namespace PolycyclicRecognition

/-- The source enlargement and the vanishing-rate tolerance are chosen
from the fixed metric constants and target restriction threshold. Neither
depends on the source section, the sample, or the path-length constant. -/
theorem exists_source_offset_threshold
    {A B Λ c target source : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hΛ : 0 ≤ Λ) (hc : 0 ≤ c)
    (htarget : 0 < target) (hsource : 0 < source) :
    ∃ δ₀ ε : ℝ, 0 < δ₀ ∧ 0 < ε ∧ δ₀ ≤ source ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        c * δ ≤ 1 ∧ Λ * (A * δ + B * ε) ≤ target := by
  let a := (Λ + 1) * (A + 1)
  let b := (Λ + 1) * (B + 1)
  have ha : 0 < a := mul_pos (by linarith) (by linarith)
  have hb : 0 < b := mul_pos (by linarith) (by linarith)
  let δ₀ := min source (min (1 / (c + 1)) (target / (2 * a)))
  let ε := target / (2 * b)
  have hδ₀ : 0 < δ₀ := lt_min hsource
    (lt_min (div_pos zero_lt_one (by linarith)) (div_pos htarget (by positivity)))
  have hε : 0 < ε := div_pos htarget (by positivity)
  refine ⟨δ₀, ε, hδ₀, hε, min_le_left _ _, ?_⟩
  intro δ hδ hd
  have hdc : δ ≤ 1 / (c + 1) :=
    hd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hda : δ ≤ target / (2 * a) :=
    hd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hca : δ * (c + 1) ≤ 1 := (le_div_iff₀ (by linarith)).mp hdc
  have hda' : δ * (2 * a) ≤ target := (le_div_iff₀ (by positivity)).mp hda
  have heb : ε * (2 * b) = target := div_mul_cancel₀ _ (by positivity)
  have hΛA : Λ * A ≤ a := by dsimp [a]; nlinarith
  have hΛB : Λ * B ≤ b := by dsimp [b]; nlinarith
  have hfirst := mul_le_mul_of_nonneg_right hΛA hδ.le
  have hsecond := mul_le_mul_of_nonneg_right hΛB hε.le
  constructor <;> nlinarith

/-- A single source enlargement works for the finite family of possible
affine labels and cone tests. The family is fixed before taking a limiting
neighboring law. -/
theorem exists_uniform_source_offset_threshold
    {I : Type*} [Finite I] [Nonempty I]
    {A B Λ c source : ℝ} (target : I → ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hΛ : 0 ≤ Λ) (hc : 0 ≤ c)
    (htarget : ∀ i, 0 < target i) (hsource : 0 < source) :
    ∃ δ₀ ε : ℝ, 0 < δ₀ ∧ 0 < ε ∧ δ₀ ≤ source ∧
      ∀ (i : I) (δ : ℝ), 0 < δ → δ ≤ δ₀ →
        c * δ ≤ 1 ∧ Λ * (A * δ + B * ε) ≤ target i := by
  classical
  let _ := Fintype.ofFinite I
  let targets := Finset.univ.image target
  have hne : targets.Nonempty := Finset.univ_nonempty.image target
  have hmin : 0 < targets.min' hne := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem targets hne)
    exact hi ▸ htarget i
  obtain ⟨δ₀, ε, hδ₀, hε, hsource', hb⟩ :=
    exists_source_offset_threshold hA hB hΛ hc hmin hsource
  refine ⟨δ₀, ε, hδ₀, hε, hsource', ?_⟩
  intro i δ hδ hd
  obtain ⟨hcδ, hbound⟩ := hb δ hδ hd
  exact ⟨hcδ, hbound.trans (Finset.min'_le targets (target i)
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))⟩

end PolycyclicRecognition

end OAI
