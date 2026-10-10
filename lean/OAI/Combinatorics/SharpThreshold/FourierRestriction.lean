import OAI.Combinatorics.SharpThreshold.FourierBasis

namespace OAI

universe u v

noncomputable section

open scoped BigOperators

namespace Problem313.BiasedFourier

variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]

/-- Fourier transformation in the exterior variables of a conditional Fourier
coefficient recovers the full Fourier coefficient on the disjoint support. -/
theorem coeff_restricted_coeff (p : ℝ) (f : (ι ⊕ κ → Bool) → ℝ)
    (A : Finset ι) (D : Finset κ) :
    coeff p (fun y => coeff p (fun x => f (Sum.elim x y)) A) D =
      coeff p f (A.disjSum D) := by
  classical
  let : DecidableEq ι := Classical.decEq _
  let : DecidableEq κ := Classical.decEq _
  let : DecidableEq (ι ⊕ κ) := Classical.decEq _
  unfold coeff
  symm
  calc
    (∑ z, weight p z * f z * char p (A.disjSum D) z) =
        ∑ x : ι → Bool, ∑ y : κ → Bool,
          weight p (Sum.elim x y) * f (Sum.elim x y) *
            char p (A.disjSum D) (Sum.elim x y) := by
      calc
        _ = ∑ xy : (ι → Bool) × (κ → Bool),
            weight p (Sum.elim xy.1 xy.2) * f (Sum.elim xy.1 xy.2) *
              char p (A.disjSum D) (Sum.elim xy.1 xy.2) := by
          apply Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow ι κ Bool)
          intro z
          have hz : Sum.elim (fun i => z (Sum.inl i)) (fun j => z (Sum.inr j)) = z := by
            funext i
            cases i <;> rfl
          simpa only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_mk, Function.comp_def] using
            congrArg (fun z => weight p z * f z * char p (A.disjSum D) z) hz.symm
        _ = _ := Fintype.sum_prod_type _
    _ = ∑ y, weight p y * (∑ x, weight p x * f (Sum.elim x y) * char p A x) *
        char p D y := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro x hx
      simp only [weight, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
        char, Finset.prod_disjSum]
      ring

/-- A conditional Fourier coefficient expands in the exterior characters,
with full Fourier coefficients and no cutoff on the exterior degree. -/
theorem restricted_coeff_expansion {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι ⊕ κ → Bool) → ℝ) (A : Finset ι) (y : κ → Bool) :
    coeff p (fun x => f (Sum.elim x y)) A =
      ∑ D : Finset κ, coeff p f (A.disjSum D) * char p D y := by
  classical
  symm
  simpa only [coeff_restricted_coeff] using
    inversion hp hp1 (fun y => coeff p (fun x => f (Sum.elim x y)) A) y

/-- Averaging the square of a conditional coefficient retains all exterior
Fourier degrees. This is the single-coefficient restriction identity. -/
theorem restricted_coeff_sq_average [DecidableEq κ] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι ⊕ κ → Bool) → ℝ) (A : Finset ι) :
    (∑ y : κ → Bool, weight p y *
      (coeff p (fun x => f (Sum.elim x y)) A) ^ 2) =
      ∑ D : Finset κ, (coeff p f (A.disjSum D)) ^ 2 := by
  classical
  symm
  simpa only [coeff_restricted_coeff] using
    parseval hp hp1 (fun y => coeff p (fun x => f (Sum.elim x y)) A)

end Problem313.BiasedFourier

end

end OAI
