import OAI.Analysis.IrrationalRotation.Sampling.CharacterPhaseRealization
import OAI.Analysis.IrrationalRotation.Sampling.StrictPhaseTrials

namespace OAI

namespace Invariant233.PrescribedPhaseRealization

open Filter Set
open scoped Topology
open ProductPhases

theorem exists_strict_character_block {θ : ℝ} (hθ : Irrational θ)
    (m : ℕ) {N : ℝ} (hN : 2 < N) (hm : 100 ≤ (m : ℝ))
    (hB : failureBound m < 1) (R : ℕ) {q₀ : ℕ} (hq₀ : 0 < q₀) :
    ∃ q : ℕ → ℕ, q 0 = q₀ ∧ (∀ i, 0 < q i) ∧ StrictMono q ∧
      (∀ i, q i ∣ q (i + 1)) ∧ (∀ i < m, R * q i ≤ q (i + 1)) ∧
      (∀ i : Fin m, Int.fract ((q (i.val + 1) : ℝ) * θ) ∈ Ioo (1 / N) (2 / N)) ∧
      strictLargePhaseCondition Finset.univ N
        (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ)) := by
  classical
  have hNpos : 0 < N := by linarith
  obtain ⟨target, htarget, hspread⟩ := exists_strict_phase_block m hNpos hm hB
  let target' : ℕ → ℝ := fun i => if hi : i < m then target ⟨i, hi⟩ else 1 / 2
  have htarget₀ : ∀ i, 0 < target' i := by
    intro i
    dsimp [target']
    split_ifs with hi
    · exact (by positivity : (0 : ℝ) < 1 / N).trans (htarget ⟨i, hi⟩).1
    · norm_num
  have htarget₁ : ∀ i, target' i < 1 := by
    intro i
    dsimp [target']
    split_ifs with hi
    · exact (htarget ⟨i, hi⟩).2.trans ((div_lt_one hNpos).mpr hN)
    · norm_num
  obtain ⟨q, hzero, hpos, hstrict, hdiv, hgap, hphase⟩ :=
    exists_phase_approximation_family hθ target' htarget₀ htarget₁ hq₀
  have hp : Tendsto
      (fun (j : ℕ) (i : Fin m) => Int.fract ((q j (i.val + 1) : ℝ) * θ)) atTop
      (𝓝 target) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [target', dite_eq_left i.isLt] using hphase i.val
  have hs : ∀ᶠ j in atTop, strictLargePhaseCondition Finset.univ N
      (fun i : Fin m => Int.fract ((q j (i.val + 1) : ℝ) * θ)) :=
    hp.eventually (eventually_strictLargePhaseCondition Finset.univ
      (by simpa using (show 0 < m by exact_mod_cast (show (0 : ℝ) < m by linarith)))
      hNpos target hspread)
  have hb : ∀ᶠ j in atTop, ∀ i : Fin m,
      Int.fract ((q j (i.val + 1) : ℝ) * θ) ∈ Ioo (1 / N) (2 / N) := by
    apply Filter.eventually_all.mpr
    intro i
    have hi : Tendsto (fun j => Int.fract ((q j (i.val + 1) : ℝ) * θ)) atTop
        (𝓝 (target i)) := by simpa only [target', dite_eq_left i.isLt] using hphase i.val
    exact hi.eventually_mem (isOpen_Ioo.mem_nhds (htarget i))
  have hr : ∀ᶠ j in atTop, ∀ i < m, R * q j i ≤ q j (i + 1) := by
    have hfinite : ∀ᶠ j in atTop, ∀ i ∈ Finset.range m,
        (R : ℝ) ≤ (q j (i + 1) : ℝ) / (q j i : ℝ) := by
      apply (Filter.eventually_all_finset (Finset.range m)).mpr
      intro i _hi
      exact (hgap i).eventually_ge_atTop R
    filter_upwards [hfinite] with j hj
    intro i hi
    have hh := (le_div_iff₀ (by exact_mod_cast hpos j i)).mp
      (hj i (Finset.mem_range.mpr hi))
    exact_mod_cast hh
  obtain ⟨j, hjspread, hjbounds, hjratio⟩ := (hs.and (hb.and hr)).exists
  exact ⟨q j, hzero j, hpos j, hstrict j, hdiv j, hjratio, hjbounds, hjspread⟩

theorem eventually_exists_strict_character_block {θ : ℝ} (hθ : Irrational θ) :
    ∀ᶠ m : ℕ in atTop, ∀ (N : ℝ), 2 < N → ∀ (R q₀ : ℕ), 0 < q₀ →
      ∃ q : ℕ → ℕ, q 0 = q₀ ∧ (∀ i, 0 < q i) ∧ StrictMono q ∧
        (∀ i, q i ∣ q (i + 1)) ∧ (∀ i < m, R * q i ≤ q (i + 1)) ∧
        (∀ i : Fin m, Int.fract ((q (i.val + 1) : ℝ) * θ) ∈ Ioo (1 / N) (2 / N)) ∧
        strictLargePhaseCondition Finset.univ N
          (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ)) := by
  have hb : ∀ᶠ m : ℕ in atTop, failureBound m ≤ Real.exp (-(m : ℝ)) :=
    tendsto_natCast_atTop_atTop.eventually eventually_failureBound_le_exp
  filter_upwards [hb, eventually_ge_atTop (100 : ℕ)] with m hbound hm
  intro N hN R q₀ hq₀
  apply exists_strict_character_block hθ m hN (by exact_mod_cast hm) _ R hq₀
  apply hbound.trans_lt
  apply Real.exp_lt_one_iff.mpr
  have hmpos : (0 : ℝ) < m := by exact_mod_cast
    (lt_of_lt_of_le (by norm_num : 0 < 100) hm)
  linarith

end Invariant233.PrescribedPhaseRealization

end OAI
