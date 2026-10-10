import OAI.Analysis.MarkovType.SpreadingLimit

namespace OAI

open scoped BigOperators

namespace MarkovSuperreflexivity

structure SpreadingModel (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y] where
  p : Seminorm ℝ C00
  d : ℝ
  d_pos : 0 < d
  prefix_lower : ∀ x r, d * |prefixCut x r| ≤ p x
  array_upper : ∀ {m : ℕ} (a : Fin m → ℝ), p (C00.ofArray a) ≤ ∑ i, |a i|
  spreading : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
    ∀ a : Fin m → ℝ, p (C00.place ι a) = p (C00.ofArray a)
  embeddings : ∀ (m : ℕ) (η : ℝ), 0 < η →
    ∃ T : (Fin m → ℝ) →ₗ[ℝ] Y, ∀ a,
      p (C00.ofArray a) ≤ ‖T a‖ ∧ ‖T a‖ ≤ (1 + η) * p (C00.ofArray a)

namespace SpreadingModel

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem coordinate_lower (S : SpreadingModel Y) (x : C00) (i : ℕ) :
    (S.d / 2) * |x i| ≤ S.p x :=
  SpreadingLimit.coordinate_lower_of_prefix S.p S.d S.d_pos.le S.prefix_lower x i

theorem definite (S : SpreadingModel Y) (x : C00) : S.p x = 0 → x = 0 :=
  SpreadingLimit.definite_of_prefix S.p S.d S.d_pos S.prefix_lower x

@[simp] theorem eq_zero_iff (S : SpreadingModel Y) (x : C00) : S.p x = 0 ↔ x = 0 :=
  ⟨S.definite x, fun h => h ▸ S.p.map_zero'⟩

end SpreadingModel

end MarkovSuperreflexivity

end OAI
