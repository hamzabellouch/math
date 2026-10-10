import OAI.NumberTheory.TwoPoint.Halasz.HalaszNearScales
import OAI.NumberTheory.TwoPoint.Halasz.HalaszBandPowerCost
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalWindow

namespace OAI

/-! Summing the phase-shaped near-center approximation over missing-band
masks. The error is summed before integration; the centered typical prefix
is retained, so its density contribution will be squared in energy. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma mrt_typical_phase_mean_expansion {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (t u : ℝ) (k : ℕ) :
    halaszPhaseMean (halaszTwistedFunction (mrtTypicalCoefficient J P F) t) u k =
      ∑ I ∈ J.powerset, (-1 : ℂ)^I.card *
        halaszPhaseMean (halaszTwistedFunction (mrtMissingCoefficient F (I.biUnion P)) t) u k := by
  unfold halaszPhaseMean halaszTwistedFunction
  simp_rw [mrtTypicalCoefficient_expansion, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro I _
  rw [mul_sum]
  apply sum_congr rfl
  intro n _
  ring

lemma mrt_typical_phase_error {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (t u : ℝ) (k : ℕ) (E : ℝ)
    (hE : ∀ I ∈ J.powerset,
      ‖halaszPhaseMean (halaszTwistedFunction (mrtMissingCoefficient F (I.biUnion P)) t) u k -
        (halaszPowerPhase u k / (1 + (-u : ℂ)*Complex.I)) *
          halaszPhaseMean (halaszTwistedFunction (mrtMissingCoefficient F (I.biUnion P)) t) 0 k‖ ≤ E) :
    ‖halaszPhaseMean (halaszTwistedFunction (mrtTypicalCoefficient J P F) t) u k -
      (halaszPowerPhase u k / (1 + (-u : ℂ)*Complex.I)) *
        halaszPhaseMean (halaszTwistedFunction (mrtTypicalCoefficient J P F) t) 0 k‖ ≤
      (2 : ℝ)^J.card * E := by
  rw [mrt_typical_phase_mean_expansion, mrt_typical_phase_mean_expansion, mul_sum,
    ← sum_sub_distrib]
  calc
    _ ≤ ∑ I ∈ J.powerset, ‖(-1 : ℂ)^I.card *
        halaszPhaseMean (halaszTwistedFunction (mrtMissingCoefficient F (I.biUnion P)) t) u k -
      (halaszPowerPhase u k / (1 + (-u : ℂ)*Complex.I)) *
        ((-1 : ℂ)^I.card *
          halaszPhaseMean (halaszTwistedFunction (mrtMissingCoefficient F (I.biUnion P)) t) 0 k)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ I ∈ J.powerset, E := by
      apply sum_le_sum
      intro I hI
      have he (a b c d : ℂ) : a*b-c*(a*d)=a*(b-c*d) := by ring
      rw [he, norm_mul, norm_pow]
      simpa only [norm_neg, norm_one, one_pow, one_mul] using hE I hI
    _ = _ := by simp [sum_const, nsmul_eq_mul, card_powerset]

/-- A missing-prime mask is allowed uniformly at each prefix, while the
small-distance hypothesis stays at the single original cutoff `2*N`. -/
theorem mrt_missing_near_prefix :
    ∀ᶠ N : ℕ in atTop, ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, (p : ℝ) ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ t : ℝ, squaredDistance F (mrtArchimedeanTwist t) (2*N) ≤
        Real.log (Real.log (2*N : ℕ))/10 →
      ∀ u : ℝ, |u| ≤ (Real.log N)^(1/(16:ℝ)) →
      ∀ k ∈ Icc N (2*N),
      ‖halaszPhaseMean (halaszTwistedFunction (mrtMissingCoefficient F Q) t) u k -
        (halaszPowerPhase u k / (1 + (-u : ℂ)*Complex.I)) *
          halaszPhaseMean (halaszTwistedFunction (mrtMissingCoefficient F Q) t) 0 k‖ ≤
        (36*(halaszPrimePowerLogConstant+1)*Real.exp 8) *
          (Real.log N)^(-1/(16:ℝ)) * k := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp halasz_near_renormalization
  have hLL : ∀ᶠ N : ℕ in atTop, 4*Real.log 3 ≤ Real.log (Real.log (N:ℝ)) :=
    (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop K,eventually_ge_atTop 4,hLL] with N hNK hN4 hLLN
  intro F hF1 hFm hFb Q hQ hQcut t hD u hu k hk
  have hNk := (mem_Icc.mp hk).1
  have hk2 := (mem_Icc.mp hk).2
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hLN : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hLNk : Real.log (N:ℝ) ≤ Real.log k := Real.log_le_log hN0 (by exact_mod_cast hNk)
  have hLLNk : Real.log (Real.log (N:ℝ)) ≤ Real.log (Real.log k) :=
    Real.log_le_log hLN hLNk
  have hpow : 2*N ≤ N^3 := by
    have hs : 2 ≤ N^2 := by nlinarith
    calc
      2*N ≤ N^2*N := Nat.mul_le_mul_right N hs
      _ = N^3 := by ring
  have hLL2 := halasz_loglog_power_cutoff N (2*N) (by omega) (by omega) hpow
  have hDk : squaredDistance F (mrtArchimedeanTwist t) k ≤ Real.log (Real.log k)/8 := by
    have hm := halasz_distance_monotone F hFb t hk2
    linarith
  have hcut (p : ℕ) (hp : p ∈ Q) : (p:ℝ) ≤ Real.exp (Real.sqrt (Real.log k)) :=
    (hQcut p hp).trans (Real.exp_le_exp.mpr (Real.sqrt_le_sqrt hLNk))
  have huk : |u| ≤ (Real.log k)^(1/(16:ℝ)) :=
    hu.trans (Real.rpow_le_rpow hLN.le hLNk (by norm_num))
  have hh := hK k (hNK.trans hNk) F hF1 hFm hFb Q hQ hcut t hDk u huk
  apply hh.trans
  have hr := Real.rpow_le_rpow_of_nonpos hLN hLNk (by norm_num : (-1/(16:ℝ))≤0)
  have hc : 0 ≤ 36*(halaszPrimePowerLogConstant+1)*Real.exp 8 := by
    unfold halaszPrimePowerLogConstant
    positivity
  calc
    _ ≤ (36*(halaszPrimePowerLogConstant+1)*Real.exp 8) * k *
        (Real.log N)^(-1/(16:ℝ)) := by gcongr
    _ = _ := by ring

/-- Finite inclusion-exclusion preserves the centered typical prefix. -/
theorem mrt_typical_near_renormalization :
    ∀ᶠ N : ℕ in atTop, ∀ {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ),
      (∀ j ∈ J, ∀ p ∈ P j, p.Prime) →
      (∀ j ∈ J, ∀ p ∈ P j, (p:ℝ) ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ t : ℝ, squaredDistance F (mrtArchimedeanTwist t) (2*N) ≤
        Real.log (Real.log (2*N : ℕ))/10 →
      ∀ u : ℝ, |u| ≤ (Real.log N)^(1/(16:ℝ)) →
      ∀ k ∈ Icc N (2*N),
      ‖halaszPhaseMean (halaszTwistedFunction (mrtTypicalCoefficient J P F) t) u k -
        (halaszPowerPhase u k / (1 + (-u : ℂ)*Complex.I)) *
          halaszPhaseMean (halaszTwistedFunction (mrtTypicalCoefficient J P F) t) 0 k‖ ≤
        (2:ℝ)^J.card * (36*(halaszPrimePowerLogConstant+1)*Real.exp 8) *
          (Real.log N)^(-1/(16:ℝ)) * k := by
  filter_upwards [mrt_missing_near_prefix] with N hn
  intro ι J P hP hcut F hF1 hFm hFb t hD u hu k hk
  have hh := mrt_typical_phase_error J P F t u k
    ((36*(halaszPrimePowerLogConstant+1)*Real.exp 8) * (Real.log N)^(-1/(16:ℝ)) * k) ?_
  · convert hh using 1; ring
  intro I hI
  apply hn F hF1 hFm hFb (I.biUnion P) _ _ t hD u hu k hk
  · intro p hp
    obtain ⟨j,hj,hp⟩ := mem_biUnion.mp hp
    exact hP j (mem_powerset.mp hI hj) p hp
  · intro p hp
    obtain ⟨j,hj,hp⟩ := mem_biUnion.mp hp
    exact hcut j (mem_powerset.mp hI hj) p hp

end TwoPointCorrelations

end OAI
