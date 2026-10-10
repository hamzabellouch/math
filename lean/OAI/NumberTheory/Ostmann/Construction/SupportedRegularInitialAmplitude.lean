import OAI.NumberTheory.Ostmann.Construction.RegularInitialAmplitude

namespace OAI

/-! # Initial Poisson bounds on the actual support of the original prior -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def priorSupportedWeight {A : Type*} {n : ℕ}
    (μ : Fin n → A → ℝ) (w : (Fin n → A) → ℂ) (x : Fin n → A) : ℂ :=
  if productPrior μ x = 0 then 0 else w x

theorem priorSupportedWeight_support {A : Type*} {n : ℕ}
    (μ : Fin n → A → ℝ) (w : (Fin n → A) → ℂ) (x : Fin n → A)
    (hx : priorSupportedWeight μ w x ≠ 0) : productPrior μ x ≠ 0 ∧ w x ≠ 0 := by
  by_cases hp : productPrior μ x = 0
  · simp only [priorSupportedWeight, hp, ite_true, ne_eq, not_true_eq_false] at hx
  · exact ⟨hp, by simpa only [priorSupportedWeight, hp, ite_false] using hx⟩

theorem priorSupportedWeight_sum {A : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (w F : (Fin n → A) → ℂ) :
    (∑ x, (productPrior μ x : ℂ) * priorSupportedWeight μ w x * F x) =
      ∑ x, (productPrior μ x : ℂ) * w x * F x := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : productPrior μ x = 0 <;> simp only [priorSupportedWeight, hp, ite_true,
    ite_false, Complex.ofReal_zero, zero_mul, mul_zero]

theorem regularInitialAmplitude_priorSupportedWeight {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (μ : Fin n → P → ℝ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (N : ℕ) (w : (Fin n → P) → ℂ) :
    regularInitialAmplitude P μ F ψ X N (priorSupportedWeight μ w) =
      regularInitialAmplitude P μ F ψ X N w :=
  priorSupportedWeight_sum μ w _

/-- Product and frequency bounds need hold only where the original weighted
summand is nonzero. Zero prior atoms are removed by an exact identity. -/
theorem regularInitialAmplitude_lower_on_support {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime)
    (μ : Fin n → P → ℝ) (C : Fin n → ℝ)
    (hμ : ∀ i p, 0 ≤ μ i p) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (p : P), (p : ℝ) * μ i p ≤ C i)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (hzero : ∀ i q, (∑ a, F i q a) = 0)
    (henergy : ∀ i q, (∑ a, ‖F i q a‖ ^ 2) ≤ q)
    (ψ : 𝓢(ℝ, ℂ)) (X H R Δ δ : ℝ) (hX : 0 < X) (hR : 0 < R) (N : ℕ)
    (w : (Fin n → P) → ℂ) (hw : ∀ x, ‖w x‖ ≤ 1)
    (hcut : ∀ x, productPrior μ x ≠ 0 → w x ≠ 0 → H * (∏ i, (x i : ℕ)) ≤ N * X)
    (hsupp : ∀ t : ℝ, H < |t| → 𝓕 ψ t = 0)
    (hsmall : ∀ i (p : P), μ i p ≠ 0 → H * R < (p : ℝ))
    (hlower : ∀ x, productPrior μ x ≠ 0 → w x ≠ 0 → X * Real.exp Δ ≤ ∏ i, (x i : ℝ))
    (hupper : ∀ x, productPrior μ x ≠ 0 → w x ≠ 0 → (∏ i, (x i : ℝ)) ≤ X * R)
    (hpositive : Real.sqrt X * (δ +
      ‖𝓕 ψ 0‖ * (∏ i, C i) * (n : ℝ) ^ n *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - Δ / 2)) ≤
      ‖∑ x : Fin n → P, (productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X‖) :
    δ ≤ ‖regularInitialAmplitude P μ F ψ X N w‖ := by
  have hnorm (x) : ‖priorSupportedWeight μ w x‖ ≤ 1 := by
    by_cases hp : productPrior μ x = 0
    · simp only [priorSupportedWeight, hp, ite_true, norm_zero, zero_le_one]
    · simpa only [priorSupportedWeight, hp, ite_false] using hw x
  have hpos := hpositive
  rw [← priorSupportedWeight_sum μ w (fun x => physicalTupleSum P x F ψ X)] at hpos
  let E := Finset.univ.filter (fun x : Fin n → P =>
    ¬ Function.Injective x ∧ productPrior μ x ≠ 0 ∧ w x ≠ 0)
  have hEsupport (x) (hx : x ∈ E) : ¬ Function.Injective x ∧ productPrior μ x ≠ 0 ∧ w x ≠ 0 :=
    (Finset.mem_filter.mp hx).2
  have herr := repeated_physical_prior_bound_at P hP μ C hμ hC hbound F hzero henergy
    ψ X H R Δ hX hR hsupp E (fun x hx => (hEsupport x hx).1)
    (fun x hx i => hsmall i (x i)
      ((Finset.prod_ne_zero_iff.mp (hEsupport x hx).2.1) i (Finset.mem_univ i)))
    (fun x hx => hlower x (hEsupport x hx).2.1 (hEsupport x hx).2.2)
    (fun x hx => hupper x (hEsupport x hx).2.1 (hEsupport x hx).2.2)
    w (fun x _ => hw x)
  have heq : (∑ x ∈ Finset.univ.filter (fun x : Fin n → P => ¬ Function.Injective x),
      (productPrior μ x : ℂ) * priorSupportedWeight μ w x * physicalTupleSum P x F ψ X) =
      ∑ x ∈ E, (productPrior μ x : ℂ) * w x * physicalTupleSum P x F ψ X := by
    simp only [E, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hi : Function.Injective x <;> by_cases hp : productPrior μ x = 0 <;>
      by_cases hz : w x = 0 <;> simp [priorSupportedWeight, hi, hp, hz]
  have hresult := regularInitialAmplitude_lower P hP μ F ψ X H hX N
    (priorSupportedWeight μ w)
    (fun x hx => hcut x (priorSupportedWeight_support μ w x hx).1
      (priorSupportedWeight_support μ w x hx).2) hsupp δ
    (‖𝓕 ψ 0‖ * (∏ i, C i) * (n : ℝ) ^ n *
      Real.exp ((∑ p : P, (p : ℝ)⁻¹) - Δ / 2)) hpos (by rw [heq]; exact herr)
  rwa [regularInitialAmplitude_priorSupportedWeight] at hresult

end Ostmann

end OAI
