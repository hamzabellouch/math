import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularOffDiagonal

namespace OAI

/-! # The transfer only tests live retained primes -/
namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

local instance liveCopiedSum_neZero {H K : Type*} (L : H → ℕ) (R : K → ℕ)
    [∀ i, NeZero (L i)] [∀ i, NeZero (R i)] (i : H ⊕ K) :
    NeZero (Sum.elim L R i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

/-- The original coefficient and all its prior factors remain in `W`.
Only the local Fourier arguments are rewritten; no absolute values are
taken and no integer-pivot transform is introduced. -/
theorem movingGiantOffDiagonal_regular_on_live {A H : Type*} [Fintype A] [Fintype H]
    (L : A → H → ℕ) [∀ a i, Fact (L a i).Prime]
    (g : ∀ a i, ZMod (L a i) → ℂ)
    (hg : ∀ a i x, g a i (-x) = conj (g a i x))
    (I : Finset ℕ) (V U D : ℕ) (v : A → ℤ) (w : ℕ → ℝ) (W : ℕ → A → ℂ)
    (hsupport : ∀ p ∈ I, ∀ a, W p a ≠ 0 →
      Pairwise (fun i j => (L a i).Coprime (L a j)) ∧
      (∏ i, L a i).Coprime (p * U) ∧ ∀ i, D.Coprime (L a i))
    (hlarge : ∀ p ∈ I, ∀ a, W p a ≠ 0 →
      ∀ q, q.Prime → q ∣ ∏ i, L a i → V < q) :
    movingGiantOffDiagonal I V U (fun a => ∏ i, L a i) v w
      (movingRegularCoefficient L g D U v W) =
    ∑ s ∈ transferFrequencyRange V, ∑ a, ∑ b,
      if validTransferredPivot I (v a * (∏ i, L b i) - v b * (∏ i, L a i)) (s * U) then
        let p := reconstructedPivot (v a * (∏ i, L b i) - v b * (∏ i, L a i)) (s * U)
        (w p : ℂ) * W p a * conj (W p b) *
          movingRegularTransform (Sum.elim (L a) (L b))
            (fun i => match i with | .inl j => g a j | .inr j => g b j) D s
      else 0 := by
  unfold movingGiantOffDiagonal
  apply Finset.sum_congr rfl
  intro s hsV
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs with hvalid
  · let p := reconstructedPivot (v a * (∏ i, L b i) - v b * (∏ i, L a i)) (s * U)
    change (w p : ℂ) * movingRegularCoefficient L g D U v W p a *
      conj (movingRegularCoefficient L g D U v W p b) =
        (w p : ℂ) * W p a * conj (W p b) * _
    by_cases ha : W p a = 0
    · simp only [movingRegularCoefficient, ha, zero_mul, mul_zero]
    by_cases hb : W p b = 0
    · simp only [movingRegularCoefficient, hb, zero_mul, map_zero, mul_zero]
    have hp : p ∈ I := hvalid.2.2.2
    obtain ⟨hpa, hMa, hDa⟩ := hsupport p hp a ha
    obtain ⟨hpb, hMb, hDb⟩ := hsupport p hp b hb
    have hs : s ≠ 0 := left_ne_zero_of_mul hvalid.1
    have hrel : v a * (∏ i, L b i) - v b * (∏ i, L a i) =
        s * ((p * U : ℕ) : ℤ) := by
      have he := validTransferredPivot_equation I _ _ hvalid
      calc
        _ = (s * (U : ℤ)) * (p : ℤ) := he
        _ = _ := by push_cast; ring
    have hAB := transferred_products_coprime (∏ i, L a i) (∏ i, L b i)
      (v a) (v b) s (p * U) hs hrel
      (fun q hq hqa _ => ((mem_transferFrequencyRange V s).mp hsV).trans_lt
        (hlarge p hp a ha q hq hqa))
      (common_prime_pivot_unit (p * U) _ _ hMa)
    have hcross (i j : H) : (L a i).Coprime (L b j) :=
      (hAB.coprime_dvd_left (Finset.dvd_prod_of_mem (L a) (Finset.mem_univ i))).coprime_dvd_right
        (Finset.dvd_prod_of_mem (L b) (Finset.mem_univ j))
    have hcop : Pairwise (fun i j =>
        (Sum.elim (L a) (L b) i).Coprime (Sum.elim (L a) (L b) j)) := by
      intro i j hij
      cases i with
      | inl i =>
        cases j with
        | inl j => exact hpa (fun he => hij (congrArg Sum.inl he))
        | inr j => exact hcross i j
      | inr i =>
        cases j with
        | inl j => exact (hcross j i).symm
        | inr j => exact hpb (fun he => hij (congrArg Sum.inr he))
    have hM : ∀ i, (p * U).Coprime (Sum.elim (L a) (L b) i) := by
      intro i
      cases i with
      | inl i => exact hMa.symm.coprime_dvd_right (Finset.dvd_prod_of_mem (L a) (Finset.mem_univ i))
      | inr i => exact hMb.symm.coprime_dvd_right (Finset.dvd_prod_of_mem (L b) (Finset.mem_univ i))
    have hD : ∀ i, D.Coprime (Sum.elim (L a) (L b) i) := by
      intro i
      cases i with
      | inl i => exact hDa i
      | inr i => exact hDb i
    have he := moving_regular_transform_transfer (L a) (L b) (g a) (g b) (hg b)
      (p * U) D (v a) (v b) s hcop hM hD hrel
    simp only [movingRegularCoefficient, map_mul (starRingEnd ℂ)]
    calc
      _ = ((w p : ℂ) * W p a * conj (W p b)) *
          (movingRegularTransform (L a) (g a) (p * U * D) (v a) *
            conj (movingRegularTransform (L b) (g b) (p * U * D) (v b))) := by ring
      _ = _ := by
        rw [he]
        congr 1
        unfold movingRegularTransform
        apply Finset.prod_congr rfl
        intro i _
        cases i <;> rfl
  · rfl

end Ostmann

end OAI
