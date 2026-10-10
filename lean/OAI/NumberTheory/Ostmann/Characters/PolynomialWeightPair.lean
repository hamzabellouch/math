import OAI.NumberTheory.Ostmann.Characters.PolynomialIntegerCharacterSum

namespace OAI

/-! # The actual off-diagonal product of two polynomial weights -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def ClippedPolynomialFactor.conjugate (f : ClippedPolynomialFactor) :
    ClippedPolynomialFactor where
  polynomial := f.polynomial
  profile := fun x => conj (f.profile x)
  lo := f.lo
  hi := f.hi
  bound := f.bound
  lip := f.lip
  lo_le_hi := f.lo_le_hi
  bound_nonneg := f.bound_nonneg
  lip_nonneg := f.lip_nonneg
  norm_le := fun x hx => by simpa only [Complex.norm_conj] using f.norm_le x hx
  lipschitz := fun x hx y hy => by
    rw [← map_sub, Complex.norm_conj]
    exact f.lipschitz x hx y hy

@[simp] theorem ClippedPolynomialFactor.conjugate_value (f : ClippedPolynomialFactor) (x : ℝ) :
    f.conjugate.value x = conj (f.value x) := rfl

noncomputable def pairedPolynomialFactors {n m : ℕ}
    (F : Fin n → ClippedPolynomialFactor) (G : Fin m → ClippedPolynomialFactor) :
    Fin (n + m) → ClippedPolynomialFactor := Fin.append F (fun i => (G i).conjugate)

theorem pairedPolynomialFactors_weight {n m : ℕ}
    (F : Fin n → ClippedPolynomialFactor) (G : Fin m → ClippedPolynomialFactor) (x : ℝ) :
    smoothPolynomialWeight (pairedPolynomialFactors F G) x =
      smoothPolynomialWeight F x * conj (smoothPolynomialWeight G x) := by
  simp only [smoothPolynomialWeight, pairedPolynomialFactors, Fin.prod_univ_add,
    Fin.append_left, Fin.append_right, ClippedPolynomialFactor.conjugate_value, map_prod]

theorem pairedPolynomialFactors_budget {n m : ℕ}
    (F : Fin n → ClippedPolynomialFactor) (G : Fin m → ClippedPolynomialFactor) :
    smoothPolynomialBudget (pairedPolynomialFactors F G) =
      smoothPolynomialBudget F * smoothPolynomialBudget G := by
  simp only [smoothPolynomialBudget, pairedPolynomialFactors, Fin.prod_univ_add,
    Fin.append_left, Fin.append_right, ClippedPolynomialFactor.conjugate]

noncomputable def polynomialAmplitude {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (keep : (Fin t → Bool) → Bool) (x : ℝ) : ℂ :=
  (if keep (polynomialSupportCode H x) = true then 1 else 0) * smoothPolynomialWeight F x

def pairedPolynomialKeep {t u : ℕ} (keep : (Fin t → Bool) → Bool)
    (keep' : (Fin u → Bool) → Bool) (c : Fin (t + u) → Bool) : Bool :=
  keep (fun i => c (Fin.castAdd u i)) && keep' (fun i => c (Fin.natAdd t i))

theorem pairedPolynomialAmplitude {n m t u : ℕ}
    (F : Fin n → ClippedPolynomialFactor) (G : Fin m → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (J : Fin u → Polynomial ℝ)
    (keep : (Fin t → Bool) → Bool) (keep' : (Fin u → Bool) → Bool) (x : ℝ) :
    polynomialAmplitude (pairedPolynomialFactors F G) (Fin.append H J)
      (pairedPolynomialKeep keep keep') x =
      polynomialAmplitude F H keep x * conj (polynomialAmplitude G J keep' x) := by
  have hleft : (fun i : Fin t => polynomialSupportCode (Fin.append H J) x (Fin.castAdd u i)) =
      polynomialSupportCode H x := by
    funext i
    simp only [polynomialSupportCode, Fin.append_left]
  have hright : (fun i : Fin u => polynomialSupportCode (Fin.append H J) x (Fin.natAdd t i)) =
      polynomialSupportCode J x := by
    funext i
    simp only [polynomialSupportCode, Fin.append_right]
  simp only [polynomialAmplitude, pairedPolynomialKeep, hleft, hright, Bool.and_eq_true,
    pairedPolynomialFactors_weight, map_mul]
  split_ifs <;> simp_all

theorem polynomialAmplitude_norm {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (keep : (Fin t → Bool) → Bool) (x : ℝ) :
    ‖polynomialAmplitude F H keep x‖ ≤ smoothPolynomialBudget F := by
  unfold polynomialAmplitude
  split_ifs
  · simpa only [one_mul] using smoothPolynomialWeight_norm F x
  · simpa only [zero_mul, norm_zero] using smoothPolynomialBudget_nonneg F

noncomputable def polynomialWeightComplexity {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) : ℕ :=
  (∑ i, (F i).polynomial.derivative.natDegree) + ∑ i, (H i).natDegree

theorem polynomialWeightComplexity_pair {n m t u : ℕ}
    (F : Fin n → ClippedPolynomialFactor) (G : Fin m → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (J : Fin u → Polynomial ℝ) :
    polynomialWeightComplexity (pairedPolynomialFactors F G) (Fin.append H J) =
      polynomialWeightComplexity F H + polynomialWeightComplexity G J := by
  simp only [polynomialWeightComplexity, pairedPolynomialFactors, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right, ClippedPolynomialFactor.conjugate]
  omega

end Ostmann

end OAI
