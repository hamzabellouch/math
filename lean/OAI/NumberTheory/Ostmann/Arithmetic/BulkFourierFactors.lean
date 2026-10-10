import OAI.NumberTheory.Ostmann.Arithmetic.BulkLeafPolynomials
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRealSmooth
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFourierVariation

namespace OAI

/-! # Clipped Fourier factors along an original bulk-prime coordinate -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate

noncomputable def bulkFourierFactors {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) : Fin (2 ^ n) → ClippedPolynomialFactor :=
  fun j =>
    let leaf := (movingLeafIndexEquiv n).symm j
    let f := fourierPolynomialFactor (Polynomial.C X⁻¹ * T.bulkLeafPolynomials value i L R leaf)
      ψ (T.leafFrequencies leaf) lo hi hlo hhi
    if treeLeafTupleEquiv Bool n (transferConjugations n false) leaf then f.conjugate else f

theorem bulkFourierFactors_degree {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (d D e : ℕ)
    (hsize : T.SizeLE d) (hregular : T.RegularLengthLE D)
    (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e) (j : Fin (2 ^ n)) :
    (bulkFourierFactors value i T L R ψ X lo hi hlo hhi j).polynomial.natDegree ≤
      2 * (n * d + e) + D := by
  have hp := T.bulkLeafPolynomials_degree value i L R d D e hsize hregular hL hR
    ((movingLeafIndexEquiv n).symm j)
  have hn : (Polynomial.C X⁻¹ * T.bulkLeafPolynomials value i L R
      ((movingLeafIndexEquiv n).symm j)).natDegree ≤ 2 * (n * d + e) + D := by
    exact Polynomial.natDegree_mul_le.trans (by simpa only [Polynomial.natDegree_C, zero_add] using hp)
  dsimp only [bulkFourierFactors]
  split_ifs <;> exact hn

theorem bulkFourierFactors_value {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : T.CompensationAbsent i)
    (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (p : ℝ) :
    smoothPolynomialWeight (bulkFourierFactors value i T L R ψ X lo hi hlo hhi) (p : ℝ) =
      realValueFourierWeight (Function.update value i p) T ψ X lo hi hlo hhi
        (L.eval (p : ℝ)) (R.eval (p : ℝ)) := by
  unfold smoothPolynomialWeight realValueFourierWeight
  rw [← (movingLeafIndexEquiv n).prod_comp]
  apply Finset.prod_congr rfl
  intro leaf _
  have hm := T.bulkLeafPolynomials_eval value i hT L R p leaf
  have he : (Polynomial.C X⁻¹ * T.bulkLeafPolynomials value i L R leaf).eval (p : ℝ) =
      T.realValueLeafModuli (Function.update value i p) (L.eval (p : ℝ)) (R.eval (p : ℝ)) leaf / X := by
    rw [Polynomial.eval_mul, Polynomial.eval_C, hm]
    ring
  simp only [bulkFourierFactors, Equiv.symm_apply_apply]
  split_ifs <;> simp only [ClippedPolynomialFactor.conjugate, ClippedPolynomialFactor.value,
    fourierPolynomialFactor, he, Polynomial.eval_X]

theorem bulkFourierFactors_budget {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : T.Frequencies (fun s => |(s : ℝ)| ≤ V)) :
    smoothPolynomialBudget (bulkFourierFactors value i T L R ψ X lo hi hlo hhi) ≤
      movingFourierVariationBudget ψ V lo hi n := by
  unfold smoothPolynomialBudget movingFourierVariationBudget
  calc
    _ ≤ ∏ _j : Fin (2 ^ n),
        (2 * SchwartzMap.seminorm ℝ 0 0 ψ +
          (SchwartzMap.seminorm ℝ 0 0 ψ + SchwartzMap.seminorm ℝ 0 1 ψ * V) * (hi - lo)) := by
      apply Finset.prod_le_prod₀
      · intro j _
        let f := bulkFourierFactors value i T L R ψ X lo hi hlo hhi j
        exact add_nonneg (mul_nonneg (by norm_num) f.bound_nonneg)
          (mul_nonneg f.lip_nonneg (sub_nonneg.mpr f.lo_le_hi))
      · intro j _
        have hv := T.leafFrequencies_bound V hV ((movingLeafIndexEquiv n).symm j)
        have hd := mul_le_mul_of_nonneg_left hv (schwartz_profile_lip_nonneg ψ)
        have he := mul_le_mul_of_nonneg_right
          (add_le_add (le_rfl : SchwartzMap.seminorm ℝ 0 0 ψ ≤ SchwartzMap.seminorm ℝ 0 0 ψ) hd)
          (sub_nonneg.mpr hhi)
        dsimp only [bulkFourierFactors]
        split_ifs <;> exact add_le_add le_rfl he
    _ = _ := by simp

end Ostmann

end OAI
