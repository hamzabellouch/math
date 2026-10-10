import OAI.NumberTheory.EgyptianFractions.CyclicDiscrepancy
import OAI.NumberTheory.EgyptianFractions.FourierFrequencyGap

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.CyclicSmoothing

/-- Low-frequency cancellation itself supplies both numerical modulus
conditions needed for the cyclic localization argument. -/
theorem cyclic_small_interval_of_fourier_automatic {q : ℕ} [NeZero q]
    {Ω : Type*} [Fintype Ω] (x : Ω → ZMod q) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖∑ ω : Ω, ZMod.stdAddChar ((l : ZMod q) * x ω)‖ ≤
        (Fintype.card Ω : ℝ) * δ ^ 3) :
    (δ / 2) * (Fintype.card Ω : ℝ) ≤
      ((Finset.univ.filter (fun ω => ((x ω).val : ℝ) < δ * q)).card : ℝ) := by
  classical
  cases isEmpty_or_nonempty Ω with
  | inl h =>
    let := h
    simp
  | inr h =>
    let := h
    have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
    have hε : δ ^ 3 < 1 := by
      have hδ1 : δ < 1 := by linarith
      exact pow_lt_one₀ hδ.le hδ1 (by decide)
    have hgap : ⌊1 / δ ^ 4⌋₊ < q :=
      modulus_gt_low_frequency_range Finset.univ Finset.univ_nonempty x _ _ hε
        (fun l hl hH => by
          simp only [Finset.card_univ, norm_div, Complex.norm_natCast]
          exact (div_le_iff₀ hN).mpr (by simpa [mul_comm] using hfourier l hl hH))
    have hscale := low_frequency_gap_scale δ q hδ hsmall hgap
    have hdegree : ⌊1 / (64 * δ ^ 3)⌋₊ ≤ q :=
      (fejer_degree_frequency_bound δ hδ hsmall).trans (Nat.le_of_lt hgap)
    exact cyclic_small_interval_of_fourier x δ hδ hsmall hscale hdegree hfourier

end Problem337.CyclicSmoothing

end

end OAI
