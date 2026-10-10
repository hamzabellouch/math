import OAI.NumberTheory.Ostmann.Dirichlet.PrimeSeriesTailScale
import OAI.NumberTheory.Ostmann.Dirichlet.SplitPrimeMassExplicit

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Dirichlet
open Filter

lemma eventually_log_add_le_linear (A : ℝ) {epsilon : ℝ} (he : 0 < epsilon) :
    ∀ᶠ L : ℝ in atTop, Real.log L + A ≤ epsilon * L := by
  have h := (Real.isLittleO_log_id_atTop.add
    (Asymptotics.isLittleO_const_id_atTop A)).bound he
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with L h hL
  simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg hL] at h
  exact (le_abs_self _).trans h

theorem exists_eventually_splitPrimeMass_manuscript_lower :
    ∃ etaMax : ℝ, 0 < etaMax ∧ etaMax ≤ 1 / 1000 ∧ ∀ A : ℝ,
      ∀ᶠ X : ℝ in atTop, ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaMax →
        ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
          chi ≠ 1 → chi.IsQuadratic →
          Real.log q ≤ Real.log 4 + 2 * eta * Real.log X →
          ∀ M : ℕ, 1 ≤ M → q ∣ M → Real.log M ≤ A * Real.log X →
            (3 / 100 : ℝ) * Real.log X ≤
              splitPrimeMass chi M (X ^ (1 / 2 - 5 * eta : ℝ)) := by
  obtain ⟨K, B, hK, hB, hb⟩ := exists_splitPrimeMass_lower_with_errors
  let etaMax : ℝ := min (1 / 1000) (1 / (1000 * (K + 1)))
  have hetaPos : 0 < etaMax := lt_min (by norm_num) (by positivity)
  have hetaSmall : etaMax ≤ 1 / 1000 := min_le_left _ _
  have hKeta : 2 * K * etaMax ≤ 1 / 100 := by
    have h := min_le_right (1 / 1000 : ℝ) (1 / (1000 * (K + 1)))
    have hd : 0 < 1000 * (K + 1) := by positivity
    have hm := (le_div_iff₀ hd).mp h
    change etaMax * (1000 * (K + 1)) ≤ 1 at hm
    nlinarith
  refine ⟨etaMax, hetaPos, hetaSmall, ?_⟩
  intro A
  have hremove := Real.tendsto_log_atTop.eventually
    (eventually_log_add_le_linear (Real.log 4 + 4 + A)
      (by norm_num : (0 : ℝ) < 1 / 200))
  have hconst := Real.tendsto_log_atTop.eventually_ge_atTop
    (100 * (K * (Real.log 4 + Real.log 6) + B))
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 100, hremove, hconst]
      with X hX hlog hremove hconst
  intro eta heta0 heta q _ chi hchi hquad hq M hM hqM hsize
  have hL : 0 < Real.log X := by linarith
  have hs : 1 < 1 + 10 / Real.log X := by
    have := div_pos (by norm_num : (0 : ℝ) < 10) hL
    linarith
  have hs2 : 1 + 10 / Real.log X ≤ 2 := by
    have : 10 / Real.log X ≤ 1 := (div_le_one hL).mpr (by linarith)
    linarith
  have hQ : 0 < X ^ (1 / 2 - 5 * eta : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hmain := hb q chi hchi hquad M hqM
    (X ^ (1 / 2 - 5 * eta : ℝ)) (1 + 10 / Real.log X) hQ.le hs hs2
  have hr := tsum_removedPrimeSeries_le_loglog M hM hs.le (by linarith) hsize
  change (∑' n, removedPrimeSeriesTerm M (1 + 10 / Real.log X) n) ≤ _ at hr
  have ht := ordinaryPrimeTail_manuscript_small hX hlog (heta.trans hetaSmall)
  change (∑' n, ordinaryPrimeTailTerm (1 + 10 / Real.log X)
    (X ^ (1 / 2 - 5 * eta : ℝ)) n) ≤ _ at ht
  rw [← tailPrimeSeriesTerm_eq] at ht
  have hnorm : (1 + 10 / Real.log X - 1)⁻¹ = Real.log X / 10 := by
    rw [add_sub_cancel_left, inv_div]
  rw [hnorm] at hmain
  have hheight : K * modulusHeight q 0 + B ≤ Real.log X / 50 := by
    have hketa : 2 * K * eta ≤ 1 / 100 :=
      (mul_le_mul_of_nonneg_left heta (by positivity)).trans hKeta
    have hq' := mul_le_mul_of_nonneg_left hq hK.le
    have hprod := mul_le_mul_of_nonneg_right hketa hL.le
    simp only [modulusHeight, abs_zero, zero_add]
    nlinarith
  change Real.log (Real.log X) + (Real.log 4 + 4 + A) ≤
    (1 / 200 : ℝ) * Real.log X at hremove
  linarith

end Ostmann.Dirichlet

end

end OAI
