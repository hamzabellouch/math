import OAI.Combinatorics.SharpThreshold.FourierBasis
import OAI.Combinatorics.SharpThreshold.InfluenceReindex

namespace OAI

universe u v

noncomputable section

open scoped BigOperators

namespace Problem313.BiasedFourier

variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Product Bernoulli weight is unchanged by renaming its coordinates. -/
theorem weight_reindex (e : ι ≃ κ) (p : ℝ) (x : ι → Bool) :
    weight p (Reindex.config e x) = weight p x := by
  unfold weight
  exact (Fintype.prod_equiv e _ _ (fun i => by simp)).symm

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- Fourier characters are natural under a bijection of coordinate sets. -/
theorem char_reindex (e : ι ≃ κ) (p : ℝ) (S : Finset ι) (x : ι → Bool) :
    char p (S.map e.toEmbedding) (Reindex.config e x) = char p S x := by
  simp [char, Finset.prod_map]

/-- Every weighted finite expectation is unchanged by coordinate transport. -/
theorem expectation_reindex (e : ι ≃ κ) (p : ℝ)
    (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ)
    (hfg : ∀ x, g (Reindex.config e x) = f x) :
    (∑ y, weight p y * g y) = ∑ x, weight p x * f x := by
  classical
  symm
  apply Fintype.sum_equiv (Reindex.configEquiv e)
  intro x
  simp only [Reindex.configEquiv_apply, weight_reindex, hfg]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Transport of Fourier coefficients, with the support transported by `Finset.map`. -/
theorem coeff_reindex (e : ι ≃ κ) (p : ℝ)
    (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ)
    (hfg : ∀ x, g (Reindex.config e x) = f x) (S : Finset ι) :
    coeff p g (S.map e.toEmbedding) = coeff p f S := by
  classical
  unfold coeff
  symm
  apply Fintype.sum_equiv (Reindex.configEquiv e)
  intro x
  simp only [Reindex.configEquiv_apply, weight_reindex, hfg, char_reindex]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Coordinate transport of spectral synthesis, including a degree-dependent multiplier. -/
theorem spectral_sum_reindex (e : ι ≃ κ) (p : ℝ) (M : ℕ → ℝ)
    (c : Finset ι → ℝ) (d : Finset κ → ℝ)
    (hcd : ∀ S, d (S.map e.toEmbedding) = c S) (x : ι → Bool) :
    (∑ T : Finset κ, M T.card * d T * char p T (Reindex.config e x)) =
      ∑ S : Finset ι, M S.card * c S * char p S x := by
  classical
  symm
  apply Fintype.sum_equiv e.finsetCongr
  intro S
  simp only [Equiv.finsetCongr_apply, Finset.card_map, hcd, char_reindex]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Spectral noise is natural under arbitrary finite-coordinate equivalences. -/
theorem noise_sum_reindex (e : ι ≃ κ) (p ρ : ℝ)
    (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ)
    (hfg : ∀ x, g (Reindex.config e x) = f x) (x : ι → Bool) :
    (∑ T : Finset κ, ρ ^ T.card * coeff p g T * char p T (Reindex.config e x)) =
      ∑ S : Finset ι, ρ ^ S.card * coeff p f S * char p S x := by
  apply spectral_sum_reindex e p (fun k => ρ ^ k)
  exact coeff_reindex e p f g hfg

/-- The fourth-moment hypercontractive statement transports along coordinate equivalences. -/
theorem noise_fourth_moment_reindex (e : ι ≃ κ) (p ρ : ℝ)
    (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ)
    (hfg : ∀ x, g (Reindex.config e x) = f x)
    (hf : (∑ x, weight p x *
        (∑ S : Finset ι, ρ ^ S.card * coeff p f S * char p S x) ^ 4) ≤
        (∑ x, weight p x * (f x) ^ 2) ^ 2) :
    (∑ y, weight p y *
        (∑ T : Finset κ, ρ ^ T.card * coeff p g T * char p T y) ^ 4) ≤
        (∑ y, weight p y * (g y) ^ 2) ^ 2 := by
  classical
  rw [expectation_reindex e p (fun x =>
    (∑ S : Finset ι, ρ ^ S.card * coeff p f S * char p S x) ^ 4)
    (fun y => (∑ T : Finset κ, ρ ^ T.card * coeff p g T * char p T y) ^ 4)
    (fun x => congrArg (fun z : ℝ => z ^ 4) (noise_sum_reindex e p ρ f g hfg x))]
  rw [expectation_reindex e p (fun x => (f x) ^ 2) (fun y => (g y) ^ 2)
    (fun x => congrArg (fun z : ℝ => z ^ 2) (hfg x))]
  exact hf

/-- A proof of spectral hypercontractivity on every `Fin n` cube suffices for every
finite coordinate type. This isolates the reindexing burden from the product induction. -/
theorem noise_fourth_moment_of_fin (p ρ : ℝ)
    (hfin : ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ),
      (∑ x, weight p x *
        (∑ S : Finset (Fin n), ρ ^ S.card * coeff p f S * char p S x) ^ 4) ≤
        (∑ x, weight p x * (f x) ^ 2) ^ 2)
    (g : (ι → Bool) → ℝ) :
    (∑ x, weight p x *
        (∑ S : Finset ι, ρ ^ S.card * coeff p g S * char p S x) ^ 4) ≤
        (∑ x, weight p x * (g x) ^ 2) ^ 2 := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  exact noise_fourth_moment_reindex e p ρ
    (fun x => g (Reindex.config e x)) g (fun _ => rfl) (hfin _ _)

omit [DecidableEq ι] [DecidableEq κ] in
/-- Every degree-weighted squared coefficient sum is invariant under coordinate transport. -/
theorem coefficient_energy_reindex (e : ι ≃ κ) (M : ℕ → ℝ)
    (c : Finset ι → ℝ) (d : Finset κ → ℝ)
    (hcd : ∀ S, d (S.map e.toEmbedding) = c S) :
    (∑ T : Finset κ, M T.card * (d T) ^ 2) =
      ∑ S : Finset ι, M S.card * (c S) ^ 2 := by
  classical
  symm
  apply Fintype.sum_equiv e.finsetCongr
  intro S
  simp only [Equiv.finsetCongr_apply, Finset.card_map, hcd]

/-- The universal coefficient form of hypercontractivity transports along coordinate
bijections. It is the equivalence branch of finite-type induction. -/
theorem synthesis_contraction_reindex (e : ι ≃ κ) (p ρ : ℝ)
    (hι : ∀ c : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S : Finset ι, ρ ^ S.card * c S * char p S x) ^ 4) ≤
        (∑ S : Finset ι, (c S) ^ 2) ^ 2)
    (d : Finset κ → ℝ) :
    (∑ y, weight p y *
        (∑ T : Finset κ, ρ ^ T.card * d T * char p T y) ^ 4) ≤
        (∑ T : Finset κ, (d T) ^ 2) ^ 2 := by
  classical
  let c : Finset ι → ℝ := fun S => d (S.map e.toEmbedding)
  have he := spectral_sum_reindex e p (fun k => ρ ^ k) c d (fun _ => rfl)
  rw [expectation_reindex e p
    (fun x => (∑ S : Finset ι, ρ ^ S.card * c S * char p S x) ^ 4)
    (fun y => (∑ T : Finset κ, ρ ^ T.card * d T * char p T y) ^ 4)
    (fun x => congrArg (fun z : ℝ => z ^ 4) (he x))]
  have hc : (∑ T : Finset κ, (d T) ^ 2) = ∑ S : Finset ι, (c S) ^ 2 := by
    simpa using coefficient_energy_reindex e (fun _ => 1) c d (fun _ => rfl)
  rw [hc]
  exact hι c

end Problem313.BiasedFourier

end

end OAI
