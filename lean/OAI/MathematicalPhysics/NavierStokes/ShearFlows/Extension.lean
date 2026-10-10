import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Profiles

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

open Set MeasureTheory
open scoped BigOperators ContDiff Topology
namespace ShearFlows

def periodize {E : Type*} [NormedAddCommGroup E] (L : ℝ) (f : ℝ → E) (x : ℝ) : E :=
  ∑' n : ℤ, f (x - L * (n : ℝ))

theorem periodize_periodic {E : Type*} [NormedAddCommGroup E]
    (L : ℝ) (f : ℝ → E) : Function.Periodic (periodize L f) L := by
  intro x
  unfold periodize
  calc
    (∑' n : ℤ, f (x + L - L * (n : ℝ))) =
        ∑' n : ℤ, f (x - L * ((n + (-1 : ℤ) : ℤ) : ℝ)) := by
      congr 1
      funext n
      congr 1
      push_cast
      ring
    _ = ∑' n : ℤ, f (x - L * (n : ℝ)) :=
      by simpa using (Equiv.addRight (-1 : ℤ)).tsum_eq (fun n : ℤ => f (x - L * (n : ℝ)))

theorem periodize_local_sum {E : Type*} [NormedAddCommGroup E]
    {L a b : ℝ} (hL : 0 < L) {f : ℝ → E}
    (hs : Function.support f ⊆ Icc a b) (x : ℝ) :
    ∃ J : Finset ℤ, ∀ᶠ y in 𝓝 x,
      periodize L f y = ∑ n ∈ J, f (y - L * (n : ℝ)) := by
  let lo : ℤ := ⌊(x - 1 - b) / L⌋
  let hi : ℤ := ⌈(x + 1 - a) / L⌉
  refine ⟨Finset.Icc lo hi, ?_⟩
  filter_upwards [Ioo_mem_nhds (show x - 1 < x by linarith)
    (show x < x + 1 by linarith)] with y hy
  apply tsum_eq_sum
  intro n hn
  by_contra hfn
  have hb := hs hfn
  have hnlo : (x - 1 - b) / L ≤ (n : ℝ) := by
    apply (div_le_iff₀ hL).2
    nlinarith [hb.2, hy.1]
  have hnhi : (n : ℝ) ≤ (x + 1 - a) / L := by
    apply (le_div_iff₀ hL).2
    nlinarith [hb.1, hy.2]
  have hlo : lo ≤ n := by
    exact_mod_cast (Int.floor_le ((x - 1 - b) / L)).trans hnlo
  have hhi : n ≤ hi := by
    exact_mod_cast hnhi.trans (Int.le_ceil ((x + 1 - a) / L))
  exact hn (Finset.mem_Icc.mpr ⟨hlo, hhi⟩)

theorem periodize_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L a b : ℝ} (hL : 0 < L) {f : ℝ → E}
    (hs : Function.support f ⊆ Icc a b) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (periodize L f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  obtain ⟨J, hJ⟩ := periodize_local_sum hL hs x
  have hsum : ContDiff ℝ ∞ (fun y => ∑ n ∈ J, f (y - L * (n : ℝ))) := by
    apply ContDiff.sum
    intro n _
    exact hf.comp (contDiff_id.sub contDiff_const)
  exact hsum.contDiffAt.congr_of_eventuallyEq hJ

theorem periodize_eq_in_chart {E : Type*} [NormedAddCommGroup E]
    {L A B : ℝ} (hL : 0 < L) (hlen : B - A ≤ L) {f : ℝ → E}
    (hs : Function.support f ⊆ Ioo A B) {x : ℝ} (hx : x ∈ Icc A B) :
    periodize L f x = f x := by
  have hz (n : ℤ) (hn : n ≠ 0) : f (x - L * (n : ℝ)) = 0 := by
    by_contra hfn
    have hf := hs hfn
    rcases lt_or_gt_of_ne hn with hn | hn
    · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      nlinarith [hx.1, hf.2]
    · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      nlinarith [hx.2, hf.1]
  rw [periodize, tsum_eq_single 0 hz]
  simp

theorem periodic_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {L : ℝ} (hp : Function.Periodic f L) :
    Function.Periodic (deriv f) L := by
  intro x
  have heq : (fun y => f (y + L)) = f := funext hp
  rw [← deriv_comp_add_const f L x, heq]

theorem periodic_deriv_integral_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} {L : ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f L) :
    (∫ x in (0 : ℝ)..L, deriv f x) = 0 := by
  rw [intervalIntegral.integral_deriv_eq_sub]
  · simpa using sub_eq_zero.mpr (hp 0)
  · intro x _
    exact hf.differentiable (by simp) x
  · exact (contDiff_infty_iff_deriv.mp hf).2.continuous.intervalIntegrable _ _

theorem closedCutoff_support {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    Function.support (closedCutoff a b c d) ⊆ Ioo a d := by
  intro x hx
  exact ⟨lt_of_not_ge (fun h => hx (closedCutoff_before hab h)),
    lt_of_not_ge (fun h => hx (closedCutoff_after hcd h))⟩

theorem maskPotential_support {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (p : ℝ) : Function.support (fun x => (x - p) * closedCutoff a b c d x) ⊆ Icc a d := by
  intro x hx
  have hc : closedCutoff a b c d x ≠ 0 := by
    intro h
    exact hx (by simp [h])
  exact Ioo_subset_Icc_self (closedCutoff_support hab hcd hc)

theorem derivativeMask_support {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (p : ℝ) : Function.support (derivativeMask a b c d p) ⊆ Icc a d :=
  support_deriv_subset.trans (closure_minimal (maskPotential_support hab hcd p) isClosed_Icc)

def circleMask (L a b c d p : ℝ) : ℝ → ℝ :=
  deriv (periodize L (fun x => (x - p) * closedCutoff a b c d x))

theorem circleMask_smooth {L a b c d : ℝ} (hL : 0 < L) (hab : a < b) (hcd : c < d)
    (p : ℝ) : ContDiff ℝ ∞ (circleMask L a b c d p) := by
  apply (contDiff_infty_iff_deriv.mp ?_).2
  exact periodize_smooth hL (maskPotential_support hab hcd p)
    ((contDiff_id.sub contDiff_const).mul (closedCutoff_smooth a b c d))

theorem circleMask_periodic (L a b c d p : ℝ) :
    Function.Periodic (circleMask L a b c d p) L :=
  periodic_deriv (periodize_periodic L _)

theorem circleMask_integral_zero {L a b c d : ℝ} (hL : 0 < L)
    (hab : a < b) (hcd : c < d) (p : ℝ) :
    (∫ x in (0 : ℝ)..L, circleMask L a b c d p x) = 0 := by
  apply periodic_deriv_integral_zero
  · exact periodize_smooth hL (maskPotential_support hab hcd p)
      ((contDiff_id.sub contDiff_const).mul (closedCutoff_smooth a b c d))
  · exact periodize_periodic L _

theorem circleMask_eq_in_chart {L A B a b c d p x : ℝ}
    (hL : 0 < L) (hlen : B - A ≤ L) (hAa : A < a) (hdB : d < B)
    (hab : a < b) (hcd : c < d) (hx : x ∈ Ioo A B) :
    circleMask L a b c d p x = derivativeMask a b c d p x := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  apply periodize_eq_in_chart hL hlen
  · intro z hz
    have hz' := maskPotential_support hab hcd p hz
    exact ⟨hAa.trans_le hz'.1, hz'.2.trans_lt hdB⟩
  · exact Ioo_subset_Icc_self hy

theorem circleMask_plateau {L A B a b c d p x : ℝ}
    (hL : 0 < L) (hlen : B - A ≤ L) (hAa : A < a) (hdB : d < B)
    (hab : a < b) (hcd : c < d) (hx : x ∈ Ioo b c) :
    circleMask L a b c d p x = 1 := by
  rw [circleMask_eq_in_chart hL hlen hAa hdB hab hcd
    ⟨hAa.trans (hab.trans hx.1), (hx.2.trans hcd).trans hdB⟩]
  exact derivativeMask_plateau hab hcd hx

theorem circleMask_zero_in_chart {L A B a b c d p x : ℝ}
    (hL : 0 < L) (hlen : B - A ≤ L) (hAa : A < a) (hdB : d < B)
    (hab : a < b) (hcd : c < d) (hx : x ∈ Ioo A B) (hout : x ∉ Icc a d) :
    circleMask L a b c d p x = 0 := by
  rw [circleMask_eq_in_chart hL hlen hAa hdB hab hcd hx]
  by_contra h
  exact hout (derivativeMask_support hab hcd p h)

theorem smoothPulse_support {a b : ℝ} (hab : a < b) :
    Function.support (smoothPulse a b) ⊆ Ioo a b := by
  intro x hx
  exact ⟨lt_of_not_ge (fun h => hx (smoothPulse_before hab h)),
    lt_of_not_ge (fun h => hx (smoothPulse_after hab h))⟩

def periodPulse (j : Fin 7) : ℝ → ℝ :=
  periodize 1 (smoothPulse (stageStart j) (stageFinish j))

theorem periodPulse_periodic (j : Fin 7) : Function.Periodic (periodPulse j) 1 :=
  periodize_periodic 1 _

theorem periodPulse_smooth (j : Fin 7) : ContDiff ℝ ∞ (periodPulse j) := by
  apply periodize_smooth (by norm_num)
  · exact (smoothPulse_support (by exact_mod_cast (stage_intervals j).2.1)).trans
      Ioo_subset_Icc_self
  · exact smoothPulse_smooth _ _

theorem periodPulse_eq_on_period (j : Fin 7) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    periodPulse j t = smoothPulse (stageStart j) (stageFinish j) t := by
  apply periodize_eq_in_chart (A := 0) (B := 1) (by norm_num) (by norm_num)
  · intro x hx
    have hx' := smoothPulse_support (show (stageStart j : ℝ) < stageFinish j
      by exact_mod_cast (stage_intervals j).2.1) hx
    have ha : (0 : ℝ) < stageStart j := by exact_mod_cast (stage_intervals j).1
    have hb : (stageFinish j : ℝ) < 1 := by exact_mod_cast (stage_intervals j).2.2
    exact ⟨ha.trans hx'.1, hx'.2.trans hb⟩
  · exact ht

theorem periodPulses_separated : ∀ t i j,
    periodPulse i t ≠ 0 → periodPulse j t ≠ 0 → i = j := by
  intro t i j hi hj
  let s : ℝ := t - (⌊t⌋ : ℝ)
  have hs : s ∈ Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have heq (k : Fin 7) : periodPulse k t = periodPulse k s := by
    have h := (periodPulse_periodic k).int_mul ⌊t⌋ s
    simpa [s] using h
  rw [heq i, periodPulse_eq_on_period i hs] at hi
  rw [heq j, periodPulse_eq_on_period j hs] at hj
  exact standardPulses_separated s i j hi hj

theorem periodPulse_nonneg (j : Fin 7) (t : ℝ) : 0 ≤ periodPulse j t := by
  apply tsum_nonneg
  intro n
  exact smoothPulse_nonneg (by exact_mod_cast (stage_intervals j).2.1) _

theorem periodPulse_integral (j : Fin 7) :
    (∫ t in (0 : ℝ)..1, periodPulse j t) = 1 := by
  have heq : (∫ t in (0 : ℝ)..1, periodPulse j t) =
      ∫ t in (0 : ℝ)..1, smoothPulse (stageStart j) (stageFinish j) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact periodPulse_eq_on_period j (by simpa using ht)
  rw [heq, smoothPulse, intervalIntegral.integral_deriv_eq_sub]
  · have hab : (stageStart j : ℝ) < stageFinish j := by
      exact_mod_cast (stage_intervals j).2.1
    rw [smoothRamp_after hab (by exact_mod_cast (stage_intervals j).2.2.le),
      smoothRamp_before hab (by exact_mod_cast (stage_intervals j).1.le)]
    norm_num
  · intro t _
    exact (smoothRamp_smooth _ _).differentiable (by simp) t
  · exact (smoothPulse_smooth _ _).continuous.intervalIntegrable _ _

theorem periodPulses_vanish_near_integers (k : ℤ) {t : ℝ}
    (ht : |t - (k : ℝ)| < (1 / 32 : ℝ)) (j : Fin 7) : periodPulse j t = 0 := by
  have hmin : (1 / 16 : ℝ) ≤ stageStart j := by
    fin_cases j <;> norm_num [stageStart]
  have hmax : (stageFinish j : ℝ) ≤ 7 / 8 := by
    fin_cases j <;> norm_num [stageFinish]
  have hab : (stageStart j : ℝ) < stageFinish j := by
    exact_mod_cast (stage_intervals j).2.1
  let s : ℝ := t - (k : ℝ)
  have hs : -(1 / 32 : ℝ) < s ∧ s < 1 / 32 := abs_lt.mp ht
  have heq : periodPulse j t = periodPulse j s := by
    simpa [s] using (periodPulse_periodic j).int_mul k s
  rw [heq]
  by_cases hsign : 0 ≤ s
  · rw [periodPulse_eq_on_period j ⟨hsign, by linarith⟩]
    exact smoothPulse_before hab (by linarith)
  · rw [← periodPulse_periodic j s,
      periodPulse_eq_on_period j ⟨by linarith, by linarith⟩]
    exact smoothPulse_after hab (by linarith)

end ShearFlows

end

end OAI
