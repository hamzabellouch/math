import OAI.Analysis.Cotype.CoefficientBounds
import Mathlib.Data.Finset.Powerset

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def rectangle (s : Finset ι) (t : Finset κ) : (ι × κ) → Bool :=
  fun ij => decide (ij.1 ∈ s ∧ ij.2 ∈ t)

def rectangularIndices (k l : ℕ) : Finset ((ι × κ) → Bool) :=
  ((Finset.univ.powersetCard k) ×ˢ (Finset.univ.powersetCard l)).image
    (fun st => rectangle st.1 st.2)

theorem mem_rectangularIndices {k l : ℕ} {P : (ι × κ) → Bool} :
    P ∈ rectangularIndices k l ↔
      ∃ (s : Finset ι) (t : Finset κ), s.card = k ∧ t.card = l ∧ rectangle s t = P := by
  simp [rectangularIndices, Finset.mem_powersetCard, and_assoc]

omit [Fintype ι] [Fintype κ] in
theorem rectangle_injective_nonempty {s s' : Finset ι} {t t' : Finset κ}
    (hs : s.Nonempty) (ht : t.Nonempty) (h : rectangle s t = rectangle s' t') :
    s = s' ∧ t = t' := by
  have he (i : ι) (j : κ) : (i ∈ s ∧ j ∈ t) ↔ (i ∈ s' ∧ j ∈ t') := by
    have hh := congrFun h (i,j)
    apply Iff.of_eq
    simpa only [rectangle, decide_eq_true_eq] using congrArg (fun b : Bool => b = true) hh
  obtain ⟨i₀, hi₀⟩ := hs
  obtain ⟨j₀, hj₀⟩ := ht
  have h₀ := (he i₀ j₀).mp ⟨hi₀, hj₀⟩
  constructor
  · ext i
    exact ⟨fun hi => ((he i j₀).mp ⟨hi, hj₀⟩).1,
      fun hi => ((he i j₀).mpr ⟨hi, h₀.2⟩).1⟩
  · ext j
    exact ⟨fun hj => ((he i₀ j).mp ⟨hi₀, hj⟩).2,
      fun hj => ((he i₀ j).mpr ⟨h₀.1, hj⟩).2⟩

theorem card_rectangularIndices_le (k l : ℕ) :
    (rectangularIndices (ι := ι) (κ := κ) k l).card ≤
      (Fintype.card ι).choose k * (Fintype.card κ).choose l := by
  unfold rectangularIndices
  apply Finset.card_image_le.trans
  simp

def Ckl (f : ((ι × κ) → Bool) → ℝ) (k l : ℕ) : ℝ :=
  ∑ P ∈ rectangularIndices k l, fourier f P

theorem Ckl_bound {f : ((ι × κ) → Bool) → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ S, |f S| ≤ M) (k l : ℕ) :
    |Ckl f k l| ≤ M * Real.sqrt
      (((Fintype.card ι).choose k : ℝ) * ((Fintype.card κ).choose l : ℝ)) := by
  apply (fourier_subset_sum_bound hM hf (rectangularIndices k l)).trans
  apply mul_le_mul_of_nonneg_left _ hM
  apply Real.sqrt_le_sqrt
  exact_mod_cast card_rectangularIndices_le (ι := ι) (κ := κ) k l

end Cotype

end

end OAI
