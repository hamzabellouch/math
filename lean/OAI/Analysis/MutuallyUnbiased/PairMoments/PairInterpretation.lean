import OAI.Analysis.MutuallyUnbiased.PairPolynomial.Main

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem pairAverage_add (H : CMatrix) (F G : CMatrix → ℝ) :
    pairAverage H (fun K => F K + G K) = pairAverage H F + pairAverage H G := by
  have h (π : Equiv.Perm Coord) :
      ((F (fun i j => H (π i) j) + G (fun i j => H (π i) j)) +
        (F (fun i j => H j (π i)) + G (fun i j => H j (π i)))) / 2 =
      (F (fun i j => H (π i) j) + F (fun i j => H j (π i))) / 2 +
        (G (fun i j => H (π i) j) + G (fun i j => H j (π i))) / 2 := by ring
  simp only [pairAverage, h, average_add]

theorem pairAverage_mul (H : CMatrix) (c : ℝ) (F : CMatrix → ℝ) :
    pairAverage H (fun K => c * F K) = c * pairAverage H F := by
  unfold pairAverage
  have h (π : Equiv.Perm Coord) :
      (c * F (fun i j => H (π i) j) + c * F (fun i j => H j (π i))) / 2 =
      c * ((F (fun i j => H (π i) j) + F (fun i j => H j (π i))) / 2) := by ring
  simp_rw [h]
  exact average_mul c _

theorem pairAverage_sum {ι : Type*} [Fintype ι] (H : CMatrix) (F : ι → CMatrix → ℝ) :
    pairAverage H (fun K => ∑ i, F i K) = ∑ i, pairAverage H (F i) := by
  simp only [pairAverage, ← Finset.sum_add_distrib, div_eq_mul_inv,
    Finset.sum_mul, average_sum]

theorem pairAverage_congr_hadamard {H : CMatrix} (hH : IsHadamard H)
    {F G : CMatrix → ℝ} (h : ∀ K, IsHadamard K → F K = G K) :
    pairAverage H F = pairAverage H G := by
  apply average_congr
  intro π
  have h₁ : IsHadamard (fun i j => H (π i) j) := by
    simpa only [Equiv.refl_apply] using hH.permutations π (Equiv.refl Coord)
  have h₂ : IsHadamard (fun i j => H j (π i)) := by
    simpa only [Equiv.refl_apply, Matrix.transpose_apply] using
      hH.transpose.permutations π (Equiv.refl Coord)
  rw [h _ h₁, h _ h₂]

namespace Certificate.PairTargetSemantics

theorem termPolynomial_re (H : CMatrix) (t : Term) :
    (termPolynomial H t).re = (t.coefficient : ℝ) * (∏ j, g H (fun i => t.charges i j)).re := by
  simp [termPolynomial, Complex.mul_re]

theorem pair_real_polynomial0 {H : CMatrix} (hH : IsHadamard H) :
    (∑ i : Fin 26, ((terms0 i).coefficient : ℝ) *
      (∏ j, g H (fun k => (terms0 i).charges k j)).re) =
      3 * Complex.normSq (pairL H) + Complex.normSq (g H alpha * g H qCross) := by
  have h := congrArg Complex.re (pair_polynomial0 hH)
  rw [Complex.mul_conj, Complex.mul_conj] at h
  simpa only [Complex.re_sum, termPolynomial_re, Complex.add_re, Complex.mul_re,
    Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using h

theorem pair_real_polynomial1 {H : CMatrix} (hH : IsHadamard H) :
    (∑ i : Fin 26, ((terms1 i).coefficient : ℝ) *
      (∏ j, g H (fun k => (terms1 i).charges k j)).re) =
      3 * Complex.normSq (pairL H) + Complex.normSq (g H alpha * g H qSame) := by
  have h := congrArg Complex.re (pair_polynomial1 hH)
  rw [Complex.mul_conj, Complex.mul_conj] at h
  simpa only [Complex.re_sum, termPolynomial_re, Complex.add_re, Complex.mul_re,
    Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using h

theorem expanded_identity0 {H : CMatrix} (hH : IsHadamard H) :
    expanded0 H = 3 * pairAverage H (fun K => Complex.normSq (pairL K)) +
      pairAverage H (fun K => Complex.normSq (g K alpha * g K qCross)) := by
  calc
    _ = pairAverage H (fun K => ∑ i : Fin 26, ((terms0 i).coefficient : ℝ) *
        (∏ j, g K (fun k => (terms0 i).charges k j)).re) := by
      simp only [pairAverage_sum, pairAverage_mul, expanded0, weightedAverage]
    _ = pairAverage H (fun K => 3 * Complex.normSq (pairL K) +
        Complex.normSq (g K alpha * g K qCross)) :=
      pairAverage_congr_hadamard hH (fun _ hK => pair_real_polynomial0 hK)
    _ = _ := by rw [pairAverage_add, pairAverage_mul]

theorem expanded_identity1 {H : CMatrix} (hH : IsHadamard H) :
    expanded1 H = 3 * pairAverage H (fun K => Complex.normSq (pairL K)) +
      pairAverage H (fun K => Complex.normSq (g K alpha * g K qSame)) := by
  calc
    _ = pairAverage H (fun K => ∑ i : Fin 26, ((terms1 i).coefficient : ℝ) *
        (∏ j, g K (fun k => (terms1 i).charges k j)).re) := by
      simp only [pairAverage_sum, pairAverage_mul, expanded1, weightedAverage]
    _ = pairAverage H (fun K => 3 * Complex.normSq (pairL K) +
        Complex.normSq (g K alpha * g K qSame)) :=
      pairAverage_congr_hadamard hH (fun _ hK => pair_real_polynomial1 hK)
    _ = _ := by rw [pairAverage_add, pairAverage_mul]

end Certificate.PairTargetSemantics
end MUB6

end

end OAI
