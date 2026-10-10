import OAI.NumberTheory.Ostmann.Construction.SelectedSchedulePrimeData
import OAI.NumberTheory.Ostmann.Construction.SmoothGiantActiveSupport

namespace OAI

/-! # The selected giant shell is separated from every regular prime -/
namespace Ostmann
open Filter

theorem eventual_scheduled_giant_lower : ∀ᶠ L : ℝ in atTop,
    ∀ lo G : ℝ, Real.exp ((1 / 20 : ℝ) * L) ≤ lo → lo - 2 ≤ G →
      2 ≤ G ∧ Real.exp ((49 / 1000 : ℝ) * L) ≤ G - 1 := by
  have hg : Tendsto (fun L : ℝ => Real.exp ((1 / 1000 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [hg.eventually (eventually_ge_atTop (4 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with L hratio hL lo G hlo hG
  have he : Real.exp ((1 / 20 : ℝ) * L) =
      Real.exp ((49 / 1000 : ℝ) * L) * Real.exp ((1 / 1000 : ℝ) * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE : 1 ≤ Real.exp ((49 / 1000 : ℝ) * L) := Real.one_le_exp (by positivity)
  have hm := mul_le_mul_of_nonneg_left hratio
    (Real.exp_nonneg ((49 / 1000 : ℝ) * L))
  rw [← he] at hm
  constructor <;> nlinarith only [hm, hlo, hG, hE]

theorem scheduled_giant_regular_separation (L G : ℝ) (hL : 0 < L)
    (hG : Real.exp ((49 / 1000 : ℝ) * L) ≤ G - 1)
    (p : smoothGiantPrimeRange G)
    (hp : smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G p ≠ 0)
    (q : ℕ) (hq : q ∈ initialRegularPrimeRange L) : (p : ℕ) ≠ q := by
  have hlo := (smoothGiantPrior_active_bounds (smoothGiantPrimeRange G)
    (smoothGiantPrimeRange_prime G) logCellProfile G
    logCellProfile_zero_outside p hp).1
  have hu := initialRegularPrimeRange_upper L q hq
  have hsmall : Real.exp ((11 / 1000 : ℝ) * L) < G - 1 :=
    (Real.exp_lt_exp.mpr (by linarith)).trans_le hG
  have hq' : (q : ℝ) < (p : ℝ) :=
    hu.trans_lt ((Real.exp_lt_exp.mpr hsmall).trans hlo)
  intro heq
  exact (ne_of_lt hq') (by exact_mod_cast heq.symm)

theorem completedCompensationSets_upper_used (A B : Set ℕ) (N hi : ℕ) (Y : ℝ)
    (D : Finset ℕ) (top : ℕ) (cs : List ℕ) (n : ℕ) (hn : n < cs.length)
    (p : ℕ) (hp : p ∈ completedCompensationSets A B N Y hi D top cs n) :
    (p : ℝ) ≤ Real.exp (((cs.drop n).headD 0 : ℝ) + 1) := by
  unfold completedCompensationSets at hp
  rw [completedCompensationCell_used top cs n hn] at hp
  obtain ⟨hpp, _, _, hhi⟩ :=
    mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hp).1).1
  exact (Real.log_le_iff_le_exp (by exact_mod_cast hpp.pos)).mp hhi

end Ostmann

end OAI
