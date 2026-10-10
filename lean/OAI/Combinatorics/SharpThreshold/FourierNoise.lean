import OAI.Combinatorics.SharpThreshold.FourierBasis

namespace OAI

universe u v w

noncomputable section

namespace Problem313.Spectral

variable {Ω : Type u} {S : Type v} [Fintype Ω] [Fintype S] [DecidableEq S]

def coefficient (w : Ω → ℝ) (χ : S → Ω → ℝ) (f : Ω → ℝ) (s : S) : ℝ :=
  ∑ x, w x * f x * χ s x

def synthesis (χ : S → Ω → ℝ) (a : S → ℝ) (x : Ω) : ℝ :=
  ∑ s, a s * χ s x

def multiplier (w : Ω → ℝ) (χ : S → Ω → ℝ) (symbol : S → ℝ)
    (f : Ω → ℝ) : Ω → ℝ :=
  synthesis χ (fun s => symbol s * coefficient w χ f s)

/-- Orthogonality diagonalizes every spectral multiplier. -/
theorem coefficient_synthesis (w : Ω → ℝ) (χ : S → Ω → ℝ)
    (horth : ∀ s t, (∑ x, w x * χ s x * χ t x) = if s = t then 1 else 0)
    (a : S → ℝ) (t : S) :
    coefficient w χ (synthesis χ a) t = a t := by
  classical
  unfold coefficient synthesis
  calc
    (∑ x, w x * (∑ s, a s * χ s x) * χ t x) =
        ∑ x, ∑ s, a s * (w x * χ s x * χ t x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ = ∑ s, a s * (∑ x, w x * χ s x * χ t x) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ = a t := by simp [horth]

/-- The Fourier coefficient of a multiplier is multiplied by its symbol. -/
theorem coefficient_multiplier (w : Ω → ℝ) (χ : S → Ω → ℝ)
    (horth : ∀ s t, (∑ x, w x * χ s x * χ t x) = if s = t then 1 else 0)
    (symbol : S → ℝ) (f : Ω → ℝ) (t : S) :
    coefficient w χ (multiplier w χ symbol f) t = symbol t * coefficient w χ f t :=
  coefficient_synthesis w χ horth _ t

omit [DecidableEq S] in
/-- Finite synthesis/analysis duality, without any orthogonality assumption. -/
theorem inner_synthesis (w : Ω → ℝ) (χ : S → Ω → ℝ)
    (a : S → ℝ) (g : Ω → ℝ) :
    (∑ x, w x * synthesis χ a x * g x) =
      ∑ s, a s * coefficient w χ g s := by
  unfold synthesis coefficient
  calc
    (∑ x, w x * (∑ s, a s * χ s x) * g x) =
        ∑ x, ∑ s, a s * (w x * g x * χ s x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ = ∑ s, a s * (∑ x, w x * g x * χ s x) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]

omit [DecidableEq S] in
/-- Every real spectral multiplier is self-adjoint. -/
theorem multiplier_self_adjoint (w : Ω → ℝ) (χ : S → Ω → ℝ)
    (symbol : S → ℝ) (f g : Ω → ℝ) :
    (∑ x, w x * multiplier w χ symbol f x * g x) =
      ∑ x, w x * f x * multiplier w χ symbol g x := by
  calc
    _ = ∑ s, (symbol s * coefficient w χ f s) * coefficient w χ g s :=
      inner_synthesis w χ _ g
    _ = ∑ s, (symbol s * coefficient w χ g s) * coefficient w χ f s := by
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ = ∑ x, w x * multiplier w χ symbol g x * f x :=
      (inner_synthesis w χ _ f).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      ring

/-- Parseval for an explicitly synthesized function. -/
theorem synthesis_energy (w : Ω → ℝ) (χ : S → Ω → ℝ)
    (horth : ∀ s t, (∑ x, w x * χ s x * χ t x) = if s = t then 1 else 0)
    (a : S → ℝ) :
    (∑ x, w x * (synthesis χ a x)^2) = ∑ s, (a s)^2 := by
  calc
    _ = ∑ x, w x * synthesis χ a x * synthesis χ a x := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = ∑ s, a s * coefficient w χ (synthesis χ a) s :=
      inner_synthesis w χ a _
    _ = ∑ s, (a s)^2 := by
      simp_rw [coefficient_synthesis w χ horth, pow_two]

end Problem313.Spectral

namespace Problem313.BiasedFourier

variable {ι : Type w} [Fintype ι]

open scoped Classical

/-- The biased noise operator, defined by its Fourier multiplier. -/
def noise (p ρ : ℝ) (g : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ := by
  classical
  exact ∑ S : Finset ι, ρ ^ S.card * coeff p g S * char p S x

theorem noise_self_adjoint (p ρ : ℝ) (f g : (ι → Bool) → ℝ) :
    (∑ x, weight p x * noise p ρ f x * g x) =
      ∑ x, weight p x * f x * noise p ρ g x := by
  classical
  have h := Spectral.multiplier_self_adjoint (weight p) (char p) (fun S => ρ ^ S.card) f g
  simpa only [Spectral.multiplier, Spectral.synthesis, Spectral.coefficient, noise, coeff] using h

end Problem313.BiasedFourier

end

end OAI
