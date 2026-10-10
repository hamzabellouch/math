import OAI.NumberTheory.TwoPoint.Fourier.MinorArcDyadicIntegral
import OAI.NumberTheory.TwoPoint.Fourier.MinorArcTypicalIntegral

namespace OAI

/-! The minor-arc short-integral estimate for the actual MRT typical set. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem minor_arc_typical_log_saving :
    ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℕ,
      ∀ {ι : Type*} (I : Finset ι) (P : ι → Finset ℕ),
      (∀ i ∈ I, ∀ p ∈ P i, p.Prime) → Set.PairwiseDisjoint (I : Set ι) P →
      ∀ i ∈ I, ∀ (J : Finset ℕ) (X H N : ℕ), 1 ≤ H → H ≤ X →
      1 ≤ Real.log (H : ℝ) → J ⊆ Icc 1 N →
      (∀ p ∈ P i, Nat.log 2 p ∈ J) → (∀ p ∈ P i, p ≠ 2) →
      (∀ j ∈ J, R₀ ≤ 2 ^ j ∧ 2 ^ j ≤ X) →
      (∀ j ∈ J, (Real.log (H : ℝ)) ^ 5 ≤ (2 : ℝ) ^ j ∧
        (2 : ℝ) ^ j ≤ (H : ℝ) / (Real.log (H : ℝ)) ^ 5) →
      ∀ (F : ℕ → ℂ), Multiplicative F → OneBounded F →
      ∀ (r : ℤ) (q : ℕ), 2 ≤ q →
      (Real.log (H : ℝ)) ^ 5 ≤ (q : ℝ) →
      (q : ℝ) ≤ (H : ℝ) / (Real.log (H : ℝ)) ^ 5 →
      ∀ α : ℝ, IsCoprime (q : ℤ) r →
      |α - (r : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
      shortExponentialIntegral (mrtTypicalCoefficient I P F) X H α ≤
        C * (X : ℝ) * H * (1 + Real.log (N : ℝ)) / Real.log (H : ℝ) +
          3 * (H : ℝ) * (X + H) * ∑ p ∈ P i, 1 / (p : ℝ) ^ 2 := by
  obtain ⟨C, hC, R₀, hbound⟩ := minor_arc_bilinear_log_saving
  refine ⟨C, hC, R₀, ?_⟩
  intro ι I P hP hdis i hi J X H N hH hHX hlogH hJN hPJ hodd hR hgeom
    F hF hFb r q hq hWq hqH α hcop happ
  let B := mrtTypicalCoefficient (I.erase i) P F
  let a := minorArcRamareCofactor (P i) B
  have ha : ∀ m, ‖a m‖ ≤ 1 :=
    minor_arc_ramare_cofactor_bound (P i) B
      (mrtTypicalCoefficient_oneBounded (I.erase i) P F hFb)
  have hc : ∀ p ∈ P i, ‖F p‖ ≤ 1 := fun p hp => hFb p (hP i hi p hp).pos
  have hbil := hbound (P i) J X H N hH hHX hlogH hJN hPJ
    (fun p hp => ⟨hP i hi p hp, hodd p hp⟩) hR hgeom a F ha hc
    r q hq hWq hqH α hcop happ
  have hcut : ∀ p ∈ P i, ∀ k ∈ range X, (k + H) / p < X + H + 1 := by
    intro p _ k hk
    have hkX := mem_range.mp hk
    have hd := Nat.div_le_self (k + H) p
    omega
  have htyp := minor_arc_typical_integral_le I P hP hdis hi F hF hFb
    X H (X + H + 1) hcut α
  exact htyp.trans (add_le_add hbil le_rfl)

end TwoPointCorrelations

end OAI
