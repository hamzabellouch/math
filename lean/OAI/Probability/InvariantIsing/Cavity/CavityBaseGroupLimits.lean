import OAI.Probability.InvariantIsing.Cavity.CavityBaseGroups
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Adding finitely many exceptional axes preserves group growth and
limiting spectral masses. The grouped base axes still partition all sites. -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace InvariantIsing

lemma cavityBaseGroupDimension_tendsto {m d : ℕ}
    (k : ℕ → Fin m → ℕ) (g : Fin d → Fin m) (a : Fin m)
    (hk : Tendsto (fun j => k j a) atTop atTop) :
    Tendsto (fun j => cavityBaseGroupDimension (k j) g a) atTop atTop :=
  (tendsto_add_atTop_nat (Fintype.card {i : Fin d // g i=a})).comp hk

lemma cavityBaseGroupDimension_sum {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N) (g : Fin d → Fin m) :
    ∑ a, cavityBaseGroupDimension k g a=N := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using
    Fintype.card_congr (cavityBaseGroupEquiv k e g)

lemma cavityBaseGroupDimension_mass_sum {N m d : ℕ} (hN : 0 < N)
    (k : Fin m → ℕ) (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (g : Fin d → Fin m) :
    ∑ a, (cavityBaseGroupDimension k g a : ℝ)/N=1 := by
  rw [← Finset.sum_div, ← Nat.cast_sum, cavityBaseGroupDimension_sum k e g,
    div_self (Nat.cast_ne_zero.mpr hN.ne')]

lemma cavityBaseGroupDimension_mass_tendsto {m d : ℕ} (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) (k : ℕ → Fin m → ℕ) (g : Fin d → Fin m)
    (a : Fin m) {ρ : ℝ}
    (hk : Tendsto (fun j => (k j a : ℝ)/N j) atTop (𝓝 ρ)) :
    Tendsto (fun j => (cavityBaseGroupDimension (k j) g a : ℝ)/N j) atTop (𝓝 ρ) := by
  have hi : Tendsto (fun j => ((N j : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hc := hi.const_mul (Fintype.card {i : Fin d // g i=a} : ℝ)
  have hh := hk.add hc
  simpa only [cavityBaseGroupDimension, Nat.cast_add, div_eq_mul_inv, add_mul,
    mul_zero, add_zero] using hh

end InvariantIsing

end

end OAI
