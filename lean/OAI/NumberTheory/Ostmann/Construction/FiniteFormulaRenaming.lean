import OAI.NumberTheory.Ostmann.Arithmetic.ReconstructedCoprimalityBound

namespace OAI

/-! # Reindexing the polynomial support bound onto actual finite prime slots -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def finiteProductPrior {K A : Type*} [Fintype K]
    (μ : K → A → ℝ) (x : K → A) : ℝ := ∏ i, μ i (x i)

namespace HistoryFormula

def rename {V W : Type*} (f : V → W) (F : HistoryFormula V) : HistoryFormula W :=
  F.bind (fun i => .prime (f i))

theorem rename_value {V W : Type*} (f : V → W) (F : HistoryFormula V) (x : W → ℚ) :
    (F.rename f).value x = F.value (x ∘ f) := by
  rw [rename, value_bind]
  simp only [value_prime, Function.comp_def]

theorem rename_cost {V W : Type*} (f : V → W) (F : HistoryFormula V) :
    (F.rename f).cost = F.cost := by
  induction F with
  | prime i => rfl
  | external z => rfl
  | product l r hl hr => exact congrArg₂ (· + ·) hl hr
  | solve l r v w s hs hl hr =>
    change (l.rename f).cost + (r.rename f).cost + 2 = l.cost + r.cost + 2
    rw [hl, hr]

theorem rename_frequencies {V W : Type*} (f : V → W) (F : HistoryFormula V) :
    (F.rename f).frequencies = F.frequencies := by
  induction F with
  | prime i => rfl
  | external z => rfl
  | product l r hl hr => exact congrArg₂ List.append hl hr
  | solve l r v w s hs hl hr => exact congrArg (s :: ·) (congrArg₂ List.append hl hr)

theorem rename_denominator {V W : Type*} (f : V → W) (F : HistoryFormula V) :
    (F.rename f).cleared.denominator = F.cleared.denominator := by
  rw [denominator_eq_frequency_product, rename_frequencies, denominator_eq_frequency_product]

theorem rename_inputs {V W : Type*} (f : V → W) (F : HistoryFormula V)
    (R : ℝ) (hF : F.InputsBounded R) : (F.rename f).InputsBounded R :=
  inputsBounded_bind F _ R hF (fun _ => trivial)

end HistoryFormula

theorem finite_prior_reindex {V W A : Type*} [Fintype V] [Fintype W] [Fintype A]
    (e : V ≃ W) (μ : W → A → ℝ) (F : (W → A) → ℂ) :
    (∑ x : V → A, ((∏ i, μ (e i) (x i) : ℝ) : ℂ) * F (x ∘ e.symm)) =
      ∑ x : W → A, ((∏ i, μ i (x i) : ℝ) : ℂ) * F x := by
  have he := (Equiv.arrowCongr e (Equiv.refl A)).sum_comp
    (fun x : W → A => ((∏ i, μ i (x i) : ℝ) : ℂ) * F x)
  rw [← he]
  apply Finset.sum_congr rfl
  intro x _
  change ((∏ i, μ (e i) (x i) : ℝ) : ℂ) * F (x ∘ e.symm) =
    ((∏ i, μ i (x (e.symm i)) : ℝ) : ℂ) * F (x ∘ e.symm)
  congr 2
  simpa only [Equiv.symm_apply_apply] using
    e.prod_comp (fun i => μ i (x (e.symm i)))

end Ostmann

end OAI
