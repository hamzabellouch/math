import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCountMean
import OAI.NumberTheory.TwoPoint.Halasz.HalaszGeneralException

namespace OAI

/-! Localize the Halasz distance hypothesis to the frequency window
actually used by a reciprocal-count cofactor. This allows a distant
frequency to be treated even when the minimizing twist is close to zero. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical ComplexConjugate

theorem halasz_local_count_exception : ∃ C X₀ : ℝ, 0 < C ∧
    ∀ N : ℕ, X₀ ≤ N →
    ∀ F : ℕ → ℂ, F 1 = 1 → Multiplicative F → OneBounded F →
    ∀ Q P : Finset ℕ, (∀ p ∈ Q, p.Prime) → (∀ p ∈ P, p.Prime) →
    ∀ t τ M : ℝ, 0 ≤ M →
      (∀ v : ℝ, |v-t| ≤ Real.log (N:ℝ)^8 →
        1/2 ≤ |v-τ| → 2*M ≤ squaredDistance F (mrtArchimedeanTwist v) N) →
      ‖∑ n ∈ Icc 1 N, (mrtMissingCoefficient F Q n * conj (mrtArchimedeanTwist t n)) /
        ((finitePrimeDivisorCount P n : ℂ)+1)‖ ≤
      C*N*((min M (Real.log (1+|τ-t|))+1)*Real.exp (-min M (Real.log (1+|τ-t|)))+
          Real.log (Real.log N)/Real.log N) := by
  obtain ⟨C, X₀, hC, hmean⟩ := halasz_general_exceptional_mean
  refine ⟨C, X₀, hC, ?_⟩
  intro N hN F hF1 hFm hFb Q P hQ hP t τ M hM hd
  apply mrt_reciprocal_count_polynomial_bound (Icc 1 N) P
    (fun n => mrtMissingCoefficient F Q n * conj (mrtArchimedeanTwist t n))
  intro u hu hu1
  let G := mrtCountMaskedCoefficient (mrtMissingCoefficient F Q) P u
  have hG1 : G 1 = 1 := mrt_missing_count_one F hF1 Q P hQ hP u
  have hGm : Multiplicative G :=
    (mrtMissingCoefficient_multiplicative F hFm Q hQ).mrtCountMaskedCoefficient P hP u
  have hGb : OneBounded G :=
    (mrtMissingCoefficient_oneBounded F hFb Q).mrtCountMaskedCoefficient P hu hu1
  have hh := hmean N hN (halaszTwistedFunction G t)
    (halasz_twisted_one G hG1 t) (halasz_twisted_multiplicative G hGm t)
    (halasz_twisted_oneBounded G hGb t) M (τ-t) hM (by
      intro v hv hvout
      rw [halasz_twisted_distance]
      have hv' : |(t+v)-t| ≤ Real.log (N:ℝ)^8 := by
        simpa only [add_sub_cancel_left] using abs_le.mpr ⟨hv.1.le,hv.2⟩
      have haway : 1/2 ≤ |(t+v)-τ| := by
        by_contra! hh
        have he : |v-(τ-t)| = |(t+v)-τ| := by congr 1; ring
        rw [← he] at hh
        have hb := abs_lt.mp hh
        exact hvout ⟨by linarith [hb.1],by linarith [hb.2]⟩
      have hl := hd (t+v) hv' haway
      have hm := mrt_missing_count_mask_distance F (mrtArchimedeanTwist (t+v)) Q P hu hu1 N
        (fun p hp => hFb p ((mem_filter.mp hp).2.pos))
        (fun p _ => by rw [mrtArchimedeanTwist_norm])
      change squaredDistance F (mrtArchimedeanTwist (t+v)) N ≤
        2*squaredDistance G (mrtArchimedeanTwist (t+v)) N at hm
      linarith)
  convert hh using 1
  congr 1
  apply sum_congr rfl
  intro n _
  simp only [halaszTwistedFunction, G, mrtCountMaskedCoefficient]
  ring

end TwoPointCorrelations

end OAI
