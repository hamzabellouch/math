import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralEndpointMultiplicity
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.MatchingPolynomialDegree

namespace OAI

/-! # The integer zero-tail recurrence is the actual backward matching column -/

open Polynomial Matrix

namespace DefocusingNLS.SeparatorArithmetic

attribute [local irreducible] backwardProduct backwardCoefficients matchingHomotopyColumn

noncomputable def zeroTailQ (ell : ℕ) (z : ℂ) : ℂ :=
  spectralQ ell 1 (33477607 / 100000000) (z - 1 / 32)

noncomputable def zeroTailS : ℂ := Complex.I * (270506819 / 100000000)

noncomputable def evaluatePair (xy : List GaussianInt × List GaussianInt) (z : ℂ) :
    Fin 2 → ℂ :=
  ![((toPolynomial xy.1).map GaussianInt.toComplex).eval z,
    ((toPolynomial xy.2).map GaussianInt.toComplex).eval z]

theorem affine_coefficient_eval (ell n : ℕ) (z : ℂ) :
    GaussianInt.toComplex ⟨scale * n + 50000000 * ell - 3125000, -centerB⟩ +
      GaussianInt.toComplex (scale : GaussianInt) * z =
        (100000000 : ℂ) * (zeroTailQ ell z + n) := by
  have hD : GaussianInt.toComplex (scale : GaussianInt) = (100000000 : ℂ) := by
    rw [GaussianInt.toComplex_def]
    norm_num [scale]
  rw [hD]
  change ((⟨scale * n + 50000000 * ell - 3125000, -centerB⟩ : GaussianInt) : ℂ) +
    (100000000 : ℂ) * z = _
  rw [GaussianInt.toComplex_def']
  simp only [scale, centerB, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast, Int.cast_ofNat, Int.cast_neg, zeroTailQ, spectralQ,
    Complex.ofReal_one, one_mul]
  push_cast
  ring

theorem mass_coefficient_eval (ell : ℕ) :
    GaussianInt.toComplex ⟨scale * (ell + 5), centerZ⟩ =
      (100000000 : ℂ) * ((ell + 5 : ℕ) + zeroTailS) := by
  rw [GaussianInt.toComplex_def']
  simp only [scale, centerZ, zeroTailS]
  push_cast
  ring

theorem coupling_coefficient_eval :
    GaussianInt.toComplex ⟨0, centerZ⟩ = (100000000 : ℂ) * zeroTailS := by
  rw [GaussianInt.toComplex_def']
  norm_num [centerZ, zeroTailS]
  ring

theorem evaluatePair_backwardStep (ell n : ℕ)
    (xy : List GaussianInt × List GaussianInt) (z : ℂ) :
    evaluatePair (backwardStep ell n xy) z = (100000000 : ℂ) •
      (backwardMatrix (ell + 5) zeroTailS (zeroTailQ ell z + n) *ᵥ evaluatePair xy z) := by
  have ht := affine_coefficient_eval ell n z
  have hm := mass_coefficient_eval ell
  have hs := coupling_coefficient_eval
  funext i
  by_cases hi : i = 0
  · subst i
    simp only [evaluatePair, Matrix.cons_val_zero, toPolynomial_backwardStep_fst,
      Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add, map_C, map_X,
      eval_sub, eval_mul, eval_add, eval_C, eval_X, Pi.smul_apply, smul_eq_mul]
    rw [ht, hm, hs]
    simp [backwardMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · have hi1 : i = 1 := by omega
    subst i
    simp only [evaluatePair, Matrix.cons_val_one, toPolynomial_backwardStep_snd,
      Polynomial.map_mul, Polynomial.map_add, map_C, map_X,
      eval_mul, eval_add, eval_C, eval_X, Pi.smul_apply, smul_eq_mul]
    rw [ht]
    simp [backwardMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

theorem backward_fold_smul (M s q a : ℂ) (ns : List ℕ) (v : Fin 2 → ℂ) :
    ns.foldl (fun w (n : ℕ) => backwardMatrix M s (q + n) *ᵥ w) (a • v) =
      a • ns.foldl (fun w (n : ℕ) => backwardMatrix M s (q + n) *ᵥ w) v := by
  induction ns generalizing v with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.foldl_cons, Matrix.mulVec_smul, ih]

theorem evaluatePair_backwardFold (ell : ℕ) (ns : List ℕ)
    (xy : List GaussianInt × List GaussianInt) (z : ℂ) :
    evaluatePair (ns.foldl (fun v n => backwardStep ell n v) xy) z =
      (100000000 : ℂ) ^ ns.length •
        ns.foldl (fun v (n : ℕ) => backwardMatrix (ell + 5) zeroTailS (zeroTailQ ell z + n) *ᵥ v)
          (evaluatePair xy z) := by
  induction ns generalizing xy with
  | nil => simp
  | cons n ns ih =>
    simp only [List.foldl_cons, List.length_cons, ih, evaluatePair_backwardStep,
      backward_fold_smul, smul_smul, pow_succ]

theorem reverse_range_backwardProduct (M s q : ℂ) (N : ℕ) (v : Fin 2 → ℂ) :
    (List.range N).reverse.foldl (fun w (n : ℕ) => backwardMatrix M s (q + n) *ᵥ w) v =
      backwardProduct M s q N *ᵥ v := by
  induction N generalizing v with
  | zero => simp [backwardProduct]
  | succ N ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.foldl_cons, ih, Matrix.mulVec_mulVec, backwardProduct]

theorem evaluatePair_backwardCoefficients (ell : ℕ) (z : ℂ) :
    evaluatePair (backwardCoefficients ell) z = (100000000 : ℂ) ^ 8 •
      matchingHomotopyColumn (ell + 5) 8 zeroTailS 0 (zeroTailQ ell z) := by
  rw [matchingHomotopyColumn_zero]
  have h := evaluatePair_backwardFold ell (List.range 8).reverse ([], [1]) z
  rw [reverse_range_backwardProduct] at h
  have hn : (List.range 8).reverse = [7, 6, 5, 4, 3, 2, 1, 0] := by decide
  have hi : evaluatePair ([], [1]) z = ![0, 1] := by
    simp [evaluatePair, toPolynomial]
  rw [List.length_reverse, List.length_range, hn, hi] at h
  simpa only [backwardCoefficients, Nat.cast_add, Nat.cast_ofNat] using h

end DefocusingNLS.SeparatorArithmetic

end OAI
