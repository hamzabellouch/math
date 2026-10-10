import OAI.Analysis.Mahler.ConvexMain

namespace OAI

namespace SymmetricMahler
open Set Finset MeasureTheory Filter
open scoped Topology ENNReal

theorem symmetric_mahler_of_finite_strips_ennreal {n : ℕ} (hn : 1 ≤ n)
    (hfinite : ∀ N (A : Fin N → Fin n → ℝ), Function.Injective (measurement A) →
      ENNReal.ofReal ((4 : ℝ)^n / (Nat.factorial n : ℝ)) ≤
        volume (stripBody A) * volume (coordinatePolar (stripBody A)))
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    (4 : ℝ)^n / (Nat.factorial n : ℝ) ≤
      (volume K).toReal * (volume (coordinatePolar K)).toReal := by
  obtain ⟨a, _, _, hrank, hbodies, _, _, _, hlim, hpolar⟩ :=
    exists_finite_strip_approximation hn hK hconv hsym hint
  have hpK := isCompact_coordinatePolar hsym (zero_mem_interior_of_symmetric hconv hsym hint)
  apply ge_of_tendsto (hlim.mul_const (volume (coordinatePolar K)).toReal)
  apply Eventually.of_forall
  intro N
  have hpfin : volume (coordinatePolar (stripBody (fun j : Fin (n+N) => (a j).val))) ≠ ∞ :=
    ne_top_of_le_ne_top hpK.measure_ne_top (measure_mono (hpolar N))
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (hbodies N).1.measure_ne_top hpfin)
    (hfinite (n+N) _ (hrank N))
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono hpK.measure_ne_top (measure_mono (hpolar N))) ENNReal.toReal_nonneg)

end SymmetricMahler

end OAI
