import OAI.Probability.InvariantIsing.Cavity.CavityFieldPath

namespace OAI

/-! Uniform height bounds for the actual fields reconstructed from a
finite spectral law. These bounds are independent of the overlap partition. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace InvariantIsing

lemma cavityFieldPrimitive_le {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (p : OverlapPath) {K r : ℝ} (hK : 0 ≤ K) (heig : ∀ a, |eig a| ≤ K)
    (hr : 0 ≤ r) :
    cavityFieldPrimitive ρ eig hρ hsum p r ≤ r * (4 * K ^ 2) := by
  have hb := intervalIntegral.integral_mono_on (μ := volume) hr
    ((continuous_cavityFieldDensity ρ eig hρ hsum p).intervalIntegrable 0 r)
    (intervalIntegrable_const (c := 4 * K ^ 2))
    (fun u _ => cavityRDerivative_le ρ eig hρ hsum hK heig (deficit p u))
  simpa only [cavityFieldPrimitive, intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hb

lemma cavityFieldStep_height_le {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (p : OverlapPath) {K : ℝ} (hK : 0 ≤ K) (heig : ∀ a, |eig a| ≤ K)
    {n : ℕ} (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q) (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i ≤ 1) (i : Fin (n + 1)) :
    (cavityFieldStep ρ eig hρ hsum p cut hcut hfirst hlast q hq hq0).height i ≤ 4 * K ^ 2 := by
  have hb := cavityFieldPrimitive_le ρ eig hρ hsum p hK heig (hq0 i)
  exact hb.trans (mul_le_of_le_one_left (by positivity) (hq1 i))

end InvariantIsing

end

end OAI
