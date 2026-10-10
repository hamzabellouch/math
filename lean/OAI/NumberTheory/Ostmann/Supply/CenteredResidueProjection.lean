import OAI.NumberTheory.Ostmann.Characters.SparseResidueProjection

namespace OAI

/-! # Centered support projections annihilate the two values of the residue indicator -/

namespace Ostmann
open scoped Classical BigOperators

theorem centeredSupportProjection_sub {α : Type*}
    (S : Finset α) (f g : α → ℂ) :
    centeredSupportProjection S (fun x => f x - g x) =
      fun x => centeredSupportProjection S f x - centeredSupportProjection S g x := by
  funext x
  unfold centeredSupportProjection finiteSupportMean
  rw [Finset.sum_sub_distrib, mul_sub]
  split_ifs <;> ring

theorem centeredSupportProjection_const_mul {α : Type*}
    (S : Finset α) (a : ℂ) (f : α → ℂ) :
    centeredSupportProjection S (fun x => a * f x) =
      fun x => a * centeredSupportProjection S f x := by
  funext x
  unfold centeredSupportProjection finiteSupportMean
  rw [← Finset.mul_sum]
  split_ifs <;> ring

theorem centeredSupportProjection_constant_on {α : Type*}
    (S : Finset α) (f : α → ℂ) (c : ℂ) (hf : ∀ x ∈ S, f x = c) :
    centeredSupportProjection S f = fun _ => 0 := by
  by_cases hs : S.Nonempty
  · have hc : (S.card : ℂ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
    have hm : finiteSupportMean S f = c := by
      unfold finiteSupportMean
      rw [Finset.sum_congr rfl hf]
      simp only [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    funext x
    by_cases hx : x ∈ S
    · simp only [centeredSupportProjection, ite_eq_left hx, hf x hx, hm, sub_self]
    · exact ite_eq_right hx
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst S
    funext x
    simp only [centeredSupportProjection, Finset.notMem_empty, ite_false]

theorem centeredSupportProjection_residue_zero {p : ℕ}
    (S : Finset (ZMod p)) :
    centeredSupportProjection S (normalizedResidueIndicator S) = fun _ => 0 := by
  apply centeredSupportProjection_constant_on S _
    (((1 - (S.card : ℝ) / p) / Real.sqrt (residueVariance S) : ℝ) : ℂ)
  intro x hx
  simp only [normalizedResidueIndicator, centeredDensity, ite_eq_left hx]

theorem centeredSupportProjection_compl_residue_zero {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) :
    centeredSupportProjection (Finset.univ \ S) (normalizedResidueIndicator S) = fun _ => 0 := by
  apply centeredSupportProjection_constant_on _ _
    (((-(S.card : ℝ) / p) / Real.sqrt (residueVariance S) : ℝ) : ℂ)
  intro x hx
  have hn := (Finset.mem_sdiff.mp hx).2
  simp only [normalizedResidueIndicator, centeredDensity, ite_eq_right hn, zero_sub, neg_div]

/-- Annihilation of the physical indicator turns the sparse projection error
into the small side block required by Lemma 5.2. -/
theorem centered_residue_projection_energy_le {p : ℕ} [NeZero p]
    (S E T : Finset (ZMod p)) (ε : ℝ)
    (hT : centeredSupportProjection T (normalizedResidueIndicator S) = fun _ => 0)
    (herr : (∑ x, ‖normalizedResidueIndicator S x -
      finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2) ≤ ε ^ 2 * p) :
    (∑ x, ‖centeredSupportProjection T
      (finiteSpectralProjection E (normalizedResidueIndicator S)) x‖ ^ 2) ≤ ε ^ 2 * p := by
  have he := centeredSupportProjection_sub T
    (finiteSpectralProjection E (normalizedResidueIndicator S)) (normalizedResidueIndicator S)
  rw [hT] at he
  simp only [sub_zero] at he
  change centeredSupportProjection T
    (fun x => finiteSpectralProjection E (normalizedResidueIndicator S) x - normalizedResidueIndicator S x) =
      centeredSupportProjection T (finiteSpectralProjection E (normalizedResidueIndicator S)) at he
  rw [← he]
  apply (centeredSupportProjection_energy_le T _).trans
  simpa only [norm_sub_rev] using herr

end Ostmann

end OAI
