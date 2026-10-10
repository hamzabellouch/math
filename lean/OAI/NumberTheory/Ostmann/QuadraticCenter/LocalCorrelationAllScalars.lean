import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationSupport

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ComplexConjugate

theorem normalized_supported_transform_correlation_le {d e : ℕ} [NeZero d] [NeZero e]
    (f : ZMod d → ℂ) (g : ZMod e → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1)
    (hsf : ∀ x, ¬ IsUnit x → Supply.unitaryDFT f x = 0)
    (hsg : ∀ y, ¬ IsUnit y → Supply.unitaryDFT g y = 0)
    (c : ZMod d) (c' : ZMod e) (h : ZMod (Nat.lcm d e)) :
    ‖normalizedCoefficient (fun s : ZMod (Nat.lcm d e) =>
      Supply.unitaryDFT f (c * ZMod.castHom (Nat.dvd_lcm_left d e) (ZMod d) s) *
      conj (Supply.unitaryDFT g (c' *
        ZMod.castHom (Nat.dvd_lcm_right d e) (ZMod e) s))) h‖ ≤
      (Nat.gcd d e : ℝ) / (Real.sqrt d * Real.sqrt e) := by
  classical
  by_cases hc : IsUnit c
  · by_cases hc' : IsUnit c'
    · obtain ⟨u, rfl⟩ := hc
      obtain ⟨u', rfl⟩ := hc'
      exact normalized_unit_transform_correlation_le f g hf hg u u' h
    · have hz (s : ZMod (Nat.lcm d e)) :
          Supply.unitaryDFT g (c' * ZMod.castHom (Nat.dvd_lcm_right d e) (ZMod e) s) = 0 :=
        hsg _ (fun hh => hc' (isUnit_of_mul_isUnit_left hh))
      simp only [normalizedCoefficient, ZMod.dft_apply, hz, map_zero, mul_zero,
        smul_zero, Finset.sum_const_zero, zero_div, norm_zero]
      positivity
  · have hz (s : ZMod (Nat.lcm d e)) :
        Supply.unitaryDFT f (c * ZMod.castHom (Nat.dvd_lcm_left d e) (ZMod d) s) = 0 :=
      hsf _ (fun hh => hc (isUnit_of_mul_isUnit_left hh))
    simp only [normalizedCoefficient, ZMod.dft_apply, hz, zero_mul,
      smul_zero, Finset.sum_const_zero, zero_div, norm_zero]
    positivity

theorem normalized_centeredProduct_correlation_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℕ) (r : κ → ℕ) [∀ i, NeZero (p i)] [∀ j, NeZero (r j)]
    [NeZero (∏ i, p i)] [NeZero (∏ j, r j)]
    (hp : ∀ i, (p i).Prime) (hr : ∀ j, (r j).Prime)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (hcor : Pairwise (fun i j => (r i).Coprime (r j)))
    (S : ∀ i, Finset (ZMod (p i))) (T : ∀ j, Finset (ZMod (r j)))
    (c : ZMod (∏ i, p i)) (c' : ZMod (∏ j, r j))
    (h : ZMod (Nat.lcm (∏ i, p i) (∏ j, r j))) :
    ‖normalizedCoefficient (fun s =>
      centeredProductTransform p hcop S (c * ZMod.castHom
        (Nat.dvd_lcm_left (∏ i, p i) (∏ j, r j)) (ZMod (∏ i, p i)) s) *
      conj (centeredProductTransform r hcor T (c' * ZMod.castHom
        (Nat.dvd_lcm_right (∏ i, p i) (∏ j, r j)) (ZMod (∏ j, r j)) s))) h‖ ≤
      (Nat.gcd (∏ i, p i) (∏ j, r j) : ℝ) /
        (Real.sqrt ((∏ i, p i : ℕ) : ℝ) * Real.sqrt ((∏ j, r j : ℕ) : ℝ)) := by
  exact normalized_supported_transform_correlation_le
    (centeredProduct p hcop S) (centeredProduct r hcor T)
    (norm_centeredProduct_le_one p hcop S) (norm_centeredProduct_le_one r hcor T)
    (centeredProductTransform_eq_zero_of_not_isUnit p hp hcop S)
    (centeredProductTransform_eq_zero_of_not_isUnit r hr hcor T) c c' h

end Ostmann.QuadraticCenter

end

end OAI
