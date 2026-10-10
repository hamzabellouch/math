import OAI.Combinatorics.SharpThreshold.FourierOption
import OAI.Combinatorics.SharpThreshold.FourierOptionExpectation
import OAI.Combinatorics.SharpThreshold.FourierReindex
import OAI.Combinatorics.SharpThreshold.TwoPoint
import OAI.Combinatorics.SharpThreshold.HypercontractiveTensor

namespace OAI

universe u

noncomputable section

namespace Problem313.BiasedFourier

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- The scalar hypercontractive estimate in normalized character notation. -/
theorem scalar_synthesis_fourth {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (a b : ℝ) :
    (1 - p) * (a + (Real.sqrt (p * (1-p)) / 4) * chi p false * b) ^ 4 +
      p * (a + (Real.sqrt (p * (1-p)) / 4) * chi p true * b) ^ 4 ≤
      (a ^ 2 + b ^ 2) ^ 2 := by
  have hs : Real.sqrt (p * (1 - p)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (mul_pos hp (sub_pos.mpr hp1)))
  have hfalse : (Real.sqrt (p * (1-p)) / 4) * chi p false = -p / 4 := by
    rw [chi_false]
    field_simp
  have htrue : (Real.sqrt (p * (1-p)) / 4) * chi p true = (1-p) / 4 := by
    rw [chi_true]
    field_simp
  rw [hfalse, htrue]
  convert Problem313.biased_two_point_fourth_moment p a b hp.le hp1.le using 1; ring

/-- Tensorization step for an additional Boolean coordinate, in spectral form. -/
theorem synthesis_fourth_option_of_split {ι : Type u} [Fintype ι]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hsplit : ∀ g : (Option ι → Bool) → ℝ,
      (∑ x, weight p x * g x) =
        (1-p) * (∑ y : ι → Bool, weight p y * g (fun t => Option.elim t false y)) +
        p * (∑ y : ι → Bool, weight p y * g (fun t => Option.elim t true y)))
    (ih : ∀ c : Finset ι → ℝ,
      (∑ x, weight p x * (∑ S, (Real.sqrt (p*(1-p))/4) ^ S.card *
        c S * char p S x) ^ 4) ≤ (∑ S, c S ^ 2) ^ 2)
    (c : Finset (Option ι) → ℝ) :
    (∑ x, weight p x * (∑ S, (Real.sqrt (p*(1-p))/4) ^ S.card *
      c S * char p S x) ^ 4) ≤ (∑ S, c S ^ 2) ^ 2 := by
  classical
  let ρ := Real.sqrt (p*(1-p))/4
  let c₀ : Finset ι → ℝ := fun S => c (S.map Function.Embedding.some)
  let c₁ : Finset ι → ℝ := fun S => c (Finset.insertNone S)
  let A : (ι → Bool) → ℝ := fun x => ∑ S, ρ ^ S.card * c₀ S * char p S x
  let B : (ι → Bool) → ℝ := fun x => ∑ S, ρ ^ S.card * c₁ S * char p S x
  have hw : ∀ x : ι → Bool, 0 ≤ weight p x := by
    intro x
    apply Finset.prod_nonneg
    intro i hi
    cases x i <;> simp [scalarWeight] <;> linarith
  have hA : (∑ x, weight p x * (A x) ^ 4) ≤ (∑ S, c₀ S ^ 2) ^ 2 := ih c₀
  have hB : (∑ x, weight p x * (B x) ^ 4) ≤ (∑ S, c₁ S ^ 2) ^ 2 := ih c₁
  have hbound := Problem313.weighted_fourth_moment_add_sq Finset.univ
    (weight p) A B (∑ S, c₀ S ^ 2) (∑ S, c₁ S ^ 2)
    (fun x _ => hw x) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hA hB
  rw [coefficient_energy_option]
  change _ ≤ ((∑ S, c₀ S ^ 2) + ∑ S, c₁ S ^ 2) ^ 2
  calc
    _ = (1-p) * (∑ x, weight p x * (A x + ρ * chi p false * B x) ^ 4) +
        p * (∑ x, weight p x * (A x + ρ * chi p true * B x) ^ 4) := by
      rw [hsplit]
      simp only [synthesis_option]
      rfl
    _ = ∑ x, weight p x * ((1-p) * (A x + ρ * chi p false * B x) ^ 4 +
        p * (A x + ρ * chi p true * B x) ^ 4) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ ≤ ∑ x, weight p x * ((A x) ^ 2 + (B x) ^ 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (scalar_synthesis_fourth hp hp1 (A x) (B x)) (hw x)
    _ ≤ _ := hbound

/-- Initial case of the finite-coordinate tensorization induction. -/
theorem synthesis_fourth_empty {ι : Type u} [Fintype ι] [IsEmpty ι]
    (p : ℝ) (c : Finset ι → ℝ) :
    (∑ x : ι → Bool, weight p x *
      (∑ S, (Real.sqrt (p*(1-p))/4) ^ S.card * c S * char p S x) ^ 4) ≤
      (∑ S, c S ^ 2) ^ 2 := by
  have he : (default : Finset ι) = ∅ := Subsingleton.elim _ _
  simp [weight, char, he]
  ring_nf
  exact le_rfl

/-- Biased product hypercontractivity in its root-free, arbitrary-coefficient form. -/
theorem synthesis_fourth_bound {ι : Type u} [Fintype ι]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (c : Finset ι → ℝ) :
    (∑ x, weight p x * (∑ S, (Real.sqrt (p*(1-p))/4) ^ S.card *
      c S * char p S x) ^ 4) ≤ (∑ S, c S ^ 2) ^ 2 := by
  classical
  refine Fintype.induction_empty_option
    (P := fun α _ => ∀ c : Finset α → ℝ,
      (∑ x, weight p x * (∑ S, (Real.sqrt (p*(1-p))/4) ^ S.card *
        c S * char p S x) ^ 4) ≤ (∑ S, c S ^ 2) ^ 2) ?_ ?_ ?_ ι c
  · intro α β _ e h d
    let : Fintype α := Fintype.ofEquiv β e.symm
    exact synthesis_contraction_reindex e p (Real.sqrt (p*(1-p))/4) h d
  · exact synthesis_fourth_empty p
  · intro α _ h d
    convert! synthesis_fourth_option_of_split hp hp1 (weighted_sum_option p) h d using 1
    apply Finset.sum_congr (by ext x; simp)
    intro x hx
    rfl

/-- The noise operator contracts the weighted second moment into the fourth moment. -/
theorem noise_fourth_bound {ι : Type u} [Fintype ι]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (g : (ι → Bool) → ℝ) :
    (∑ x, weight p x * (∑ S, (Real.sqrt (p*(1-p))/4) ^ S.card *
      coeff p g S * char p S x) ^ 4) ≤ (∑ x, weight p x * (g x) ^ 2) ^ 2 := by
  have h := synthesis_fourth_bound hp hp1 (coeff p g)
  rw [parseval hp hp1 g] at h
  exact h

end Problem313.BiasedFourier

end

end OAI
