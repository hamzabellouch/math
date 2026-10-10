import OAI.Probability.SwitchChain.SliceEuclideanGenerator
import OAI.Probability.SwitchChain.SliceGenerator

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.SliceEuclideanGenerator

variable {α : Type*} [Fintype α] [DecidableEq α]

def coordinates {q : ℕ} (S : State α q) (i : α) : ℝ :=
  if i ∈ S.val then 1 else 0

theorem coordinates_binary {q : ℕ} (S : State α q) (i : α) :
    coordinates S i = 0 ∨ coordinates S i = 1 := by
  by_cases hi : i ∈ S.val <;> simp [coordinates, hi]

theorem coordinates_sum {q : ℕ} (S : State α q) :
    ∑ i, coordinates S i = (q : ℝ) := by
  have hc := (Finset.mem_powersetCard.mp S.property).2
  simp [coordinates, hc]

theorem coordinates_swap {q : ℕ} (S : State α q) (a b : α) :
    coordinates (swapState q a b S) = coordinates S ∘ Equiv.swap a b := by
  ext i
  have hm : i ∈ (swapState q a b S).val ↔ Equiv.swap a b i ∈ S.val := by
    change i ∈ S.val.image (Equiv.swap a b) ↔ _
    constructor
    · intro hi
      obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hi
      have he' := congrArg (Equiv.swap a b) he
      have hji : j = Equiv.swap a b i := by simpa using he'
      exact hji ▸ hj
    · intro hi
      apply Finset.mem_image.mpr
      exact ⟨Equiv.swap a b i, hi, by simp⟩
  simp only [coordinates, Function.comp_apply, hm]

def sample (q : ℕ) (f : (α → ℝ) → ℝ) : EuclideanSpace ℝ (State α q) :=
  WithLp.toLp 2 (fun S => f (coordinates S))

@[simp] theorem sample_apply (q : ℕ) (f : (α → ℝ) → ℝ) (S : State α q) :
    sample q f S = f (coordinates S) := rfl

theorem generator_sample (q : ℕ) (f : (α → ℝ) → ℝ) :
    generator q (sample q f) = sample q (SliceGenerator.generator f) := by
  ext S
  rw [generator_apply]
  simp only [sample_apply, SliceGenerator.generator, coordinates_swap]
  ring

theorem generator_sample_linear (q : ℕ) (u : α → ℝ) (hu : ∑ i, u i = 0) :
    generator q (sample q (fun y => ∑ i, u i * y i)) =
      ((Fintype.card α : ℝ) / 2) • sample q (fun y => ∑ i, u i * y i) := by
  rw [generator_sample]
  ext S
  change SliceGenerator.generator (fun y => ∑ i, u i * y i) (coordinates S) = _
  simpa only [PiLp.smul_apply, smul_eq_mul, sample_apply] using
    SliceGenerator.generator_centered_linear (coordinates S) u hu

theorem generator_sample_quadratic (q : ℕ) (c : α → α → ℝ)
    (hdiag : ∀ i, c i i = 0) (hrow : ∀ i, ∑ j, c i j = 0)
    (hcol : ∀ j, ∑ i, c i j = 0) :
    generator q (sample q (fun y => ∑ i, ∑ j, c i j * (y i * y j))) =
      ((Fintype.card α : ℝ) - 1) • sample q (fun y => ∑ i, ∑ j, c i j * (y i * y j)) := by
  rw [generator_sample]
  ext S
  change SliceGenerator.generator (fun y => ∑ i, ∑ j, c i j * (y i * y j)) (coordinates S) = _
  simpa only [PiLp.smul_apply, smul_eq_mul, sample_apply] using
    SliceGenerator.generator_row_zero_quadratic (coordinates S) (q : ℝ)
      (coordinates_sum S) (coordinates_binary S) c hdiag hrow hcol

end Problem315.SliceEuclideanGenerator

end

end OAI
