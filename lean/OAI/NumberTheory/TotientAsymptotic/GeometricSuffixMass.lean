import OAI.NumberTheory.TotientAsymptotic.GeometricPrefixMass
import OAI.NumberTheory.TotientAsymptotic.PrimeSuffixMass

namespace OAI

/-! A suffix restriction costs its reciprocal totient mass, with the
initial coordinates counted once on the retained geometric simplex. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem geometric_suffix_mass {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ N n : ℕ,N+H=m x → ∀ _hn : n ≤ N,
      ∀ (Q : Finset (Fin N → ℕ)) (T : Finset (Fin (N-n) → ℕ)),
        (∀ p ∈ Q,(∀ i,(p i).Prime) ∧
          primePrefixCoord p ∈ relaxedGeometricFamily (m x) N (B x) c) →
        (∀ p ∈ T,(∀ i,(p i).Prime) ∧ StrictAnti p) →
        (∀ p ∈ Q,primeFinal p n ∈ T) →
      (∑ p ∈ Q,reciprocalShiftWeight p) ≤
        C*G x N*(∑ r ∈ T.image (fun p => ∏ i,p i),(r.totient:ℝ)⁻¹) := by
  obtain ⟨C,hC,hprefix⟩ := geometric_initial_mass_le_base hc
  refine ⟨C,hC,?_⟩
  filter_upwards [hprefix] with H hH
  filter_upwards [hH] with x hx
  intro N n hN hn Q T hQ hT hsuffix
  have hm := prime_mass_split_suffix hn Q T hsuffix
  have hp := hx N n hN hn Q hQ
  rw [←ordered_prime_family_mass T hT]
  exact hm.trans (mul_le_mul_of_nonneg_right hp
    (Finset.sum_nonneg (fun p _ => reciprocalShiftWeight_nonneg p)))

end TotientAsymptotic

end

end OAI
