import Mathlib
import OAI.Computability.MaxCut.Model

namespace OAI

/-! Exact finite uniform conditioning and total expectation, including empty fibres. -/

namespace MaxCutGames.Soundness.UniformPartition
open scoped BigOperators
noncomputable section

def mean {Ω : Type} [Fintype Ω] (g : Ω → ℝ) : ℝ :=
  (∑ ω, g ω) / Fintype.card Ω

theorem mean_equiv {Ω Γ : Type} [Fintype Ω] [Fintype Γ]
    (e : Ω ≃ Γ) (g : Γ → ℝ) : mean (fun ω => g (e ω)) = mean g := by
  unfold mean
  rw [e.sum_comp, Fintype.card_congr e]

def fiberSum {Ω H : Type} [Fintype Ω] [DecidableEq H]
    (f : Ω → H) (h : H) (g : Ω → ℝ) : ℝ :=
  ∑ ω, if f ω = h then g ω else 0

def fiberSize {Ω H : Type} [Fintype Ω] [DecidableEq H]
    (f : Ω → H) (h : H) : ℝ := fiberSum f h (fun _ => 1)

theorem fiberSize_eq_card {Ω H : Type} [Fintype Ω] [DecidableEq H]
    (f : Ω → H) (h : H) :
    fiberSize f h = ((Finset.univ.filter (fun ω => f ω = h)).card : ℝ) := by
  classical
  unfold fiberSize fiberSum
  rw [← Finset.sum_filter]
  simp

theorem sum_fiberSum {Ω H : Type} [Fintype Ω] [Fintype H] [DecidableEq H]
    (f : Ω → H) (g : Ω → ℝ) :
    (∑ h, fiberSum f h g) = ∑ ω, g ω := by
  unfold fiberSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp

theorem fiberSize_mul {Ω H : Type} [Fintype Ω] [DecidableEq H]
    (f : Ω → H) (b : H → ℝ) (h : H) :
    fiberSize f h * b h = fiberSum f h (fun ω => b (f ω)) := by
  unfold fiberSize fiberSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : f ω = h <;> simp [hω]

theorem fiberSize_pos {Ω H : Type} [Fintype Ω] [DecidableEq H]
    (f : Ω → H) (h : H) (hh : ∃ ω, f ω = h) : 0 < fiberSize f h := by
  classical
  obtain ⟨ω, hω⟩ := hh
  rw [fiberSize_eq_card]
  have hc : 0 < (Finset.univ.filter (fun ω => f ω = h)).card :=
    Finset.card_pos.mpr ⟨ω, by simp [hω]⟩
  exact_mod_cast hc

theorem fiberSize_mul_conditional {Ω H : Type} [Fintype Ω] [DecidableEq H]
    (f : Ω → H) (g : Ω → ℝ) (h : H) :
    fiberSize f h * (fiberSum f h g / fiberSize f h) = fiberSum f h g := by
  classical
  by_cases hh : ∃ ω, f ω = h
  · have hn : fiberSize f h ≠ 0 := ne_of_gt (fiberSize_pos f h hh)
    field_simp [hn]
  · have hz : ∀ ω, f ω ≠ h := fun ω hω => hh ⟨ω, hω⟩
    simp [fiberSize, fiberSum, hz]

theorem total_mean {Ω H : Type} [Fintype Ω] [Fintype H] [DecidableEq H]
    (f : Ω → H) (g : Ω → ℝ) :
    mean g = mean (fun ω => fiberSum f (f ω) g / fiberSize f (f ω)) := by
  let b : H → ℝ := fun h => fiberSum f h g / fiberSize f h
  change mean g = mean (fun ω => b (f ω))
  unfold mean
  apply congrArg (fun x : ℝ => x / (Fintype.card Ω : ℝ))
  calc
    (∑ ω, g ω) = ∑ h, fiberSum f h g := (sum_fiberSum f g).symm
    _ = ∑ h, fiberSize f h * b h := by
      apply Finset.sum_congr rfl
      intro h _
      exact (fiberSize_mul_conditional f g h).symm
    _ = ∑ h, fiberSum f h (fun ω => b (f ω)) := by
      apply Finset.sum_congr rfl
      intro h _
      exact fiberSize_mul f b h
    _ = ∑ ω, b (f ω) := sum_fiberSum f (fun ω => b (f ω))

theorem mean_mono {Ω : Type} [Fintype Ω] {g g' : Ω → ℝ}
    (h : ∀ ω, g ω ≤ g' ω) : mean g ≤ mean g' := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ => h ω)) (Nat.cast_nonneg _)

theorem mean_le_partition_bound {Ω H : Type}
    [Fintype Ω] [Fintype H] [DecidableEq H]
    (f : Ω → H) (g : Ω → ℝ) (bound : H → ℝ)
    (hlocal : ∀ h, (∃ ω, f ω = h) →
      fiberSum f h g / fiberSize f h ≤ bound h) :
    mean g ≤ mean (fun ω => bound (f ω)) := by
  calc
    mean g = mean (fun ω => fiberSum f (f ω) g / fiberSize f (f ω)) := total_mean f g
    _ ≤ mean (fun ω => bound (f ω)) := mean_mono (fun ω => hlocal (f ω) ⟨ω,rfl⟩)

theorem fiber_conditional_eq_subtype_mean {Ω H : Type}
    [Fintype Ω] [DecidableEq H] (f : Ω → H) (h : H) (g : Ω → ℝ) :
    fiberSum f h g / fiberSize f h =
      mean (fun ω : {ω // f ω = h} => g ω.val) := by
  classical
  simp only [fiberSum, fiberSize, mean]
  congr 1
  · rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun ω => by simp) g
  · rw [← Finset.sum_filter]
    simp [Fintype.card_subtype]

end
end MaxCutGames.Soundness.UniformPartition

end OAI
