import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import OAI.NumberTheory.Jacobsthal.Estimates.PairedDeficitPositivity
import OAI.NumberTheory.Jacobsthal.Sieve.BuchstabBridge

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.NormalizedDeficits

open Filter Set
open scoped Topology
open LinearSieveFunctions BuchstabBridge

noncomputable def lowerDeficit (s : ℝ) : ℝ := 1 - f sieveA s
noncomputable def upperDeficit (s : ℝ) : ℝ := F sieveA s - 1
noncomputable def gap (s : ℝ) : ℝ := F sieveA s - f sieveA s

theorem deficit_sum (s : ℝ) : lowerDeficit s + upperDeficit s = gap s := by
  unfold lowerDeficit upperDeficit gap
  ring

theorem gap_eq_rho {s : ℝ} (hs : 1 ≤ s) : gap s = sieveA * Dickman.rho (s - 1) / s :=
  gap_identity sieveA hs

theorem lowerDeficit_continuous : Continuous lowerDeficit :=
  continuous_const.sub (f_continuous sieveA)

theorem upperDeficit_continuousOn : ContinuousOn upperDeficit (Ici 1) :=
  ((F_continuousOn sieveA).mono (by intro s hs; change 0 < s; exact lt_of_lt_of_le zero_lt_one hs)).sub continuousOn_const

theorem gap_continuousOn : ContinuousOn gap (Ici 1) := by
  have h := lowerDeficit_continuous.continuousOn.add upperDeficit_continuousOn
  have heq : gap = fun s => lowerDeficit s + upperDeficit s := funext (fun s => (deficit_sum s).symm)
  rw [heq]
  exact h

theorem gap_pos {s : ℝ} (hs : 1 ≤ s) : 0 < gap s :=
  LinearSieveFunctions.gap_pos sieveA_pos hs

theorem lowerDeficit_mass_deriv {s : ℝ} (hs : 2 < s) :
    HasDerivAt (fun t => t * lowerDeficit t) (-upperDeficit (s - 1)) s := by
  convert! (hasDerivAt_id s).sub (mass_f_hasDerivAt sieveA hs) using 1
  · ext t
    change t * (1 - f sieveA t) = t - t * f sieveA t
    ring
  · simp only [upperDeficit]
    ring

theorem upperDeficit_mass_deriv {s : ℝ} (hs : 2 < s) :
    HasDerivAt (fun t => t * upperDeficit t) (-lowerDeficit (s - 1)) s := by
  convert! (mass_F_hasDerivAt sieveA hs).sub (hasDerivAt_id s) using 1
  · ext t
    change t * (F sieveA t - 1) = t * F sieveA t - t
    ring
  · simp only [lowerDeficit]
    ring

theorem gap_mass_deriv {s : ℝ} (hs : 2 < s) :
    HasDerivAt (fun t => t * gap t) (-gap (s - 1)) s := by
  convert! (mass_F_hasDerivAt sieveA hs).sub (mass_f_hasDerivAt sieveA hs) using 1
  · ext t
    change t * (F sieveA t - f sieveA t) = t * F sieveA t - t * f sieveA t
    ring
  · simp only [gap]
    ring

theorem lowerDeficit_tendsto_zero : Tendsto lowerDeficit atTop (𝓝 0) := by
  convert! normalized_f_tendsto_one.const_sub 1 using 1
  simp

theorem upperDeficit_tendsto_zero : Tendsto upperDeficit atTop (𝓝 0) := by
  convert! normalized_F_tendsto_one.sub_const 1 using 1
  simp

theorem gap_tendsto_zero : Tendsto gap atTop (𝓝 0) := pair_gap_tendsto_zero sieveA

theorem deficits_pos {s : ℝ} (hs : 1 ≤ s) : 0 < lowerDeficit s ∧ 0 < upperDeficit s := by
  apply PairedDeficitPositivity.paired_pos lowerDeficit_continuous.continuousOn
    upperDeficit_continuousOn ?_ ?_ ?_ (fun _ h => lowerDeficit_mass_deriv h)
    (fun _ h => upperDeficit_mass_deriv h) lowerDeficit_tendsto_zero upperDeficit_tendsto_zero s hs
  · intro t ht
    simp only [lowerDeficit, f_initial sieveA ht.2, sub_zero, zero_lt_one]
  · intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    change 0 < F sieveA t - 1
    rw [F_initial sieveA ht0 (by linarith [ht.2])]
    have h := (lt_div_iff₀ ht0).mpr (show 1 * t < sieveA by linarith [sieveA_gt_two, ht.2])
    linarith
  · intro t ht
    rw [deficit_sum]
    exact gap_pos ht

theorem deficit_offsets_pos {δ : ℝ} (hhalf : δ < 1 / 2)
    (hδA : δ * sieveA < 1) (hδA2 : δ * sieveA < sieveA - 2)
    {s : ℝ} (hs : 1 ≤ s) :
    0 < lowerDeficit s - δ * gap s ∧ 0 < upperDeficit s - δ * gap s := by
  let a : ℝ → ℝ := fun t => lowerDeficit t - δ * gap t
  let c : ℝ → ℝ := fun t => upperDeficit t - δ * gap t
  have ha : ContinuousOn a (Ici 1) :=
    lowerDeficit_continuous.continuousOn.sub (continuousOn_const.mul gap_continuousOn)
  have hc : ContinuousOn c (Ici 1) :=
    upperDeficit_continuousOn.sub (continuousOn_const.mul gap_continuousOn)
  have hginit : ∀ t ∈ Icc 1 2, gap t = sieveA / t := by
    intro t ht
    simp only [gap, f_initial sieveA ht.2, sub_zero,
      F_initial sieveA (s := t) (by linarith [ht.1]) (by linarith [ht.2])]
  have hai : ∀ t ∈ Icc 1 2, 0 < a t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have hdiv : δ * sieveA / t < 1 := (div_lt_one ht0).mpr (lt_of_lt_of_le hδA ht.1)
    dsimp [a, lowerDeficit]
    rw [f_initial sieveA ht.2, hginit t ht]
    have heq : δ * (sieveA / t) = δ * sieveA / t := by ring
    rw [heq]
    linarith
  have hci : ∀ t ∈ Icc 1 2, 0 < c t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have hdiv : 0 < (sieveA - δ * sieveA - t) / t :=
      div_pos (by linarith [ht.2]) ht0
    dsimp [c, upperDeficit]
    rw [F_initial sieveA ht0 (by linarith [ht.2]), hginit t ht]
    convert! hdiv using 1
    field_simp
    ring
  have hsum : ∀ t, 1 ≤ t → 0 < a t + c t := by
    intro t ht
    have heq : a t + c t = (1 - 2 * δ) * gap t := by
      dsimp [a, c]
      rw [← deficit_sum t]
      ring
    rw [heq]
    exact mul_pos (by linarith) (gap_pos ht)
  have hda : ∀ t, 2 < t → HasDerivAt (fun u => u * a u) (-c (t - 1)) t := by
    intro t ht
    convert! (lowerDeficit_mass_deriv ht).sub ((gap_mass_deriv ht).const_mul δ) using 1
    · ext u
      change u * (lowerDeficit u - δ * gap u) = u * lowerDeficit u - δ * (u * gap u)
      ring
    · dsimp [c]
      ring
  have hdc : ∀ t, 2 < t → HasDerivAt (fun u => u * c u) (-a (t - 1)) t := by
    intro t ht
    convert! (upperDeficit_mass_deriv ht).sub ((gap_mass_deriv ht).const_mul δ) using 1
    · ext u
      change u * (upperDeficit u - δ * gap u) = u * upperDeficit u - δ * (u * gap u)
      ring
    · dsimp [a]
      ring
  have hla : Tendsto a atTop (𝓝 0) := by
    simpa only [mul_zero, sub_zero] using lowerDeficit_tendsto_zero.sub (gap_tendsto_zero.const_mul δ)
  have hlc : Tendsto c atTop (𝓝 0) := by
    simpa only [mul_zero, sub_zero] using upperDeficit_tendsto_zero.sub (gap_tendsto_zero.const_mul δ)
  exact PairedDeficitPositivity.paired_pos ha hc hai hci hsum hda hdc hla hlc s hs

theorem deficits_uniform_comparison : ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
    ∀ s : ℝ, 1 ≤ s →
      δ * gap s < lowerDeficit s ∧ lowerDeficit s < (1 - δ) * gap s ∧
      δ * gap s < upperDeficit s ∧ upperDeficit s < (1 - δ) * gap s := by
  let δ : ℝ := min 1 (sieveA - 2) / (4 * sieveA)
  have hδpos : 0 < δ := div_pos (lt_min zero_lt_one (sub_pos.mpr sieveA_gt_two))
    (mul_pos (by norm_num) sieveA_pos)
  have heq : δ * sieveA = min 1 (sieveA - 2) / 4 := by
    dsimp [δ]
    field_simp [ne_of_gt sieveA_pos]
  have hδA : δ * sieveA < 1 := by rw [heq]; linarith [min_le_left (1 : ℝ) (sieveA - 2)]
  have hδA2 : δ * sieveA < sieveA - 2 := by
    rw [heq]
    linarith [min_le_right (1 : ℝ) (sieveA - 2), sieveA_gt_two]
  have hhalf : δ < 1 / 2 := by nlinarith [sieveA_gt_two]
  refine ⟨δ, hδpos, hhalf, ?_⟩
  intro s hs
  obtain ⟨ha, hc⟩ := deficit_offsets_pos hhalf hδA hδA2 hs
  have hsum := deficit_sum s
  constructor
  · linarith
  constructor
  · nlinarith
  constructor
  · linarith
  · nlinarith

end NumberTheoryLean.NormalizedDeficits

end

section

namespace NumberTheoryLean.DeficitFutureIntegrals

open Filter Set MeasureTheory
open scoped Topology
open LinearSieveFunctions BuchstabBridge NormalizedDeficits

theorem future_integral_of_mass {a b : ℝ → ℝ} {base : ℝ} (hbase : 1 ≤ base)
    (ha : ContinuousOn a (Ioi 0))
    (hb : ∀ t, base - 1 < t → 0 ≤ b t)
    (hd : ∀ t, base < t → HasDerivAt (fun u => u * a u) (-b (t - 1)) t)
    (hl : Tendsto (fun t => t * a t) atTop (𝓝 0))
    {s : ℝ} (hs : base ≤ s) :
    IntegrableOn b (Ioi (s - 1)) ∧ s * a s = ∫ t in Ioi (s - 1), b t := by
  let H : ℝ → ℝ := fun t => (t + 1) * a (t + 1)
  have hs0 : 0 < s := lt_of_lt_of_le (by linarith : 0 < base) hs
  have hc : ContinuousWithinAt H (Ici (s - 1)) (s - 1) := by
    have hm : ContinuousAt (fun t => t * a t) s :=
      continuousAt_id.mul (ha.continuousAt (Ioi_mem_nhds hs0))
    have hm' : ContinuousAt (fun t => t * a t) ((s - 1) + 1) := by simpa only [sub_add_cancel] using hm
    have hc' := hm'.comp (f := fun t : ℝ => t + 1) (x := s - 1)
      ((continuous_id.add continuous_const : Continuous (fun t : ℝ => t + 1)).continuousAt)
    convert! hc'.continuousWithinAt using 1
  have hder : ∀ t ∈ Ioi (s - 1), HasDerivAt H (-b t) t := by
    intro t ht
    have hdt := (hd (t + 1) (by change s - 1 < t at ht; linarith)).comp t
      ((hasDerivAt_id t).add_const 1)
    convert! hdt using 1
    simp
  have hnonpos : ∀ t ∈ Ioi (s - 1), -b t ≤ 0 := by
    intro t ht
    exact neg_nonpos.mpr (hb t (by change s - 1 < t at ht; linarith))
  have hshift : Tendsto (fun t : ℝ => t + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro v
    exact eventually_atTop.mpr ⟨v - 1, fun t ht => by linarith⟩
  have hlim : Tendsto H atTop (𝓝 0) := hl.comp hshift
  have hint := integrableOn_Ioi_deriv_of_nonpos hc hder hnonpos hlim
  have heq := integral_Ioi_of_hasDerivAt_of_nonpos hc hder hnonpos hlim
  constructor
  · exact integrable_neg_iff.mp hint
  · simp only [integral_neg, H, sub_add_cancel, zero_sub] at heq
    linarith

theorem deficit_mass_bounds {s : ℝ} (hs : 1 ≤ s) :
    (0 ≤ s * lowerDeficit s ∧ s * lowerDeficit s ≤ sieveA * Dickman.rho (s - 1)) ∧
    (0 ≤ s * upperDeficit s ∧ s * upperDeficit s ≤ sieveA * Dickman.rho (s - 1)) := by
  obtain ⟨ha, hc⟩ := deficits_pos hs
  have hsum := deficit_sum s
  have hg : s * gap s = sieveA * Dickman.rho (s - 1) := by
    rw [gap_eq_rho hs]
    field_simp
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hbA : s * lowerDeficit s ≤ s * gap s :=
    mul_le_mul_of_nonneg_left (by linarith) hs0.le
  have hbC : s * upperDeficit s ≤ s * gap s :=
    mul_le_mul_of_nonneg_left (by linarith) hs0.le
  exact ⟨⟨mul_nonneg hs0.le ha.le, by simpa only [hg] using hbA⟩,
    ⟨mul_nonneg hs0.le hc.le, by simpa only [hg] using hbC⟩⟩

theorem lowerDeficit_mass_tendsto_zero :
    Tendsto (fun s => s * lowerDeficit s) atTop (𝓝 0) := by
  have hshift : Tendsto (fun s : ℝ => s - 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro v
    exact eventually_atTop.mpr ⟨v + 1, fun s hs => by linarith⟩
  have hlim := (DickmanDecay.rho_tendsto_zero.comp hshift).const_mul sieveA
  simp only [mul_zero] at hlim
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    exact (deficit_mass_bounds hs).1.1
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    exact (deficit_mass_bounds hs).1.2

theorem upperDeficit_mass_tendsto_zero :
    Tendsto (fun s => s * upperDeficit s) atTop (𝓝 0) := by
  have hshift : Tendsto (fun s : ℝ => s - 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro v
    exact eventually_atTop.mpr ⟨v + 1, fun s hs => by linarith⟩
  have hlim := (DickmanDecay.rho_tendsto_zero.comp hshift).const_mul sieveA
  simp only [mul_zero] at hlim
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    exact (deficit_mass_bounds hs).2.1
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    exact (deficit_mass_bounds hs).2.2

theorem upperDeficit_mass_deriv_of_one_lt {s : ℝ} (hs : 1 < s) :
    HasDerivAt (fun t => t * upperDeficit t) (-lowerDeficit (s - 1)) s := by
  by_cases hs2 : 2 < s
  · exact upperDeficit_mass_deriv hs2
  · have heq : (fun t => t * upperDeficit t) =ᶠ[𝓝 s] (fun t => sieveA - t) := by
      filter_upwards [Ioo_mem_nhds (show 0 < s by linarith) (show s < 3 by linarith)] with t ht
      change t * (F sieveA t - 1) = sieveA - t
      rw [F_initial sieveA ht.1 ht.2.le]
      field_simp [ne_of_gt ht.1]
    have h := ((hasDerivAt_const s sieveA).sub (hasDerivAt_id s)).congr_of_eventuallyEq heq
    convert! h using 1
    simp only [lowerDeficit, f_initial sieveA (s := s - 1) (by linarith), sub_zero, zero_sub]

theorem lowerDeficit_nonneg (s : ℝ) : 0 ≤ lowerDeficit s := by
  by_cases hs : 1 ≤ s
  · exact (deficits_pos hs).1.le
  · simp only [lowerDeficit, f_initial sieveA (by linarith : s ≤ 2), sub_zero, zero_le_one]

theorem lower_future_integral {s : ℝ} (hs : 2 ≤ s) :
    IntegrableOn upperDeficit (Ioi (s - 1)) ∧
      s * lowerDeficit s = ∫ t in Ioi (s - 1), upperDeficit t := by
  exact future_integral_of_mass (a := lowerDeficit) (b := upperDeficit) (base := 2) (by norm_num)
    lowerDeficit_continuous.continuousOn (fun t ht => (deficits_pos (s := t) (by linarith)).2.le)
    (fun _ ht => lowerDeficit_mass_deriv ht) lowerDeficit_mass_tendsto_zero hs

theorem upper_future_integral {s : ℝ} (hs : 1 ≤ s) :
    IntegrableOn lowerDeficit (Ioi (s - 1)) ∧
      s * upperDeficit s = ∫ t in Ioi (s - 1), lowerDeficit t := by
  exact future_integral_of_mass (a := upperDeficit) (b := lowerDeficit) (base := 1) le_rfl
    ((F_continuousOn sieveA).sub continuousOn_const) (fun t _ => lowerDeficit_nonneg t)
    (fun _ ht => upperDeficit_mass_deriv_of_one_lt ht) upperDeficit_mass_tendsto_zero hs

end NumberTheoryLean.DeficitFutureIntegrals

end

section

namespace NumberTheoryLean.DerivativeWeights

open Filter Set MeasureTheory
open scoped Topology
open LinearSieveFunctions BuchstabBridge NormalizedDeficits DeficitFutureIntegrals

noncomputable def evenInitial (s : ℝ) : ℝ :=
  sieveA * (s / (s - 1) - Real.log (s - 1))

noncomputable def phiEven (s : ℝ) : ℝ :=
  if s ≤ 2 then evenInitial s else s * (lowerDeficit s + upperDeficit (s - 1))

noncomputable def phiOdd (s : ℝ) : ℝ :=
  if s ≤ 3 then sieveA else s * (upperDeficit s + lowerDeficit (s - 1))

noncomputable def W (t : ℝ) : ℝ := (t + 1) / t ^ 2

theorem phiOdd_initial {s : ℝ} (hs : s ≤ 3) : phiOdd s = sieveA := by
  simp only [phiOdd, ite_eq_left hs]

theorem phiEven_initial {s : ℝ} (hs : s ≤ 2) : phiEven s = evenInitial s := by
  simp only [phiEven, ite_eq_left hs]

theorem phiEven_eq_deficits {s : ℝ} (hs : 2 ≤ s) :
    phiEven s = s * (lowerDeficit s + upperDeficit (s - 1)) := by
  rcases eq_or_lt_of_le hs with h | h
  · subst s
    norm_num [phiEven, evenInitial, lowerDeficit, upperDeficit,
      f_initial, F_initial sieveA (s := 1) (by norm_num) (by norm_num)]
    ring
  · exact ite_eq_right (not_le_of_gt h)

theorem phiOdd_eq_deficits {s : ℝ} (hs : 1 ≤ s) :
    phiOdd s = s * (upperDeficit s + lowerDeficit (s - 1)) := by
  by_cases hs3 : s ≤ 3
  · rw [phiOdd_initial hs3]
    simp only [upperDeficit, lowerDeficit, f_initial sieveA (s := s - 1) (by linarith),
      F_initial sieveA (s := s) (by linarith) hs3]
    field_simp
    ring
  · exact ite_eq_right hs3

theorem phiEven_explicit {s : ℝ} (hs : 1 < s) (hs4 : s ≤ 4) :
    phiEven s = evenInitial s := by
  by_cases hs2 : s ≤ 2
  · exact phiEven_initial hs2
  · rw [phiEven_eq_deficits (by linarith)]
    unfold lowerDeficit upperDeficit evenInitial
    rw [f_first_formula sieveA (by linarith) hs4,
      F_initial sieveA (s := s - 1) (by linarith) (by linarith)]
    field_simp
    ring

theorem hasDerivAt_of_mass {g : ℝ → ℝ} {s v : ℝ} (hs : s ≠ 0)
    (hm : HasDerivAt (fun t => t * g t) v s) :
    HasDerivAt g ((v - g s) / s) s := by
  have heq : g =ᶠ[𝓝 s] (fun t => (t * g t) / t) := by
    filter_upwards [eventually_ne_nhds hs] with t ht
    field_simp
  have h := (hm.div (hasDerivAt_id s) hs).congr_of_eventuallyEq heq
  convert! h using 1
  simp only [id_eq, mul_one]
  field_simp

theorem lowerDeficit_hasDerivAt {s : ℝ} (hs : 2 < s) :
    HasDerivAt lowerDeficit (-phiEven s / s ^ 2) s := by
  have h := hasDerivAt_of_mass (by linarith : s ≠ 0) (lowerDeficit_mass_deriv hs)
  convert! h using 1
  rw [phiEven_eq_deficits hs.le]
  field_simp
  ring

theorem upperDeficit_hasDerivAt {s : ℝ} (hs : 1 < s) :
    HasDerivAt upperDeficit (-phiOdd s / s ^ 2) s := by
  have h := hasDerivAt_of_mass (by linarith : s ≠ 0) (upperDeficit_mass_deriv_of_one_lt hs)
  convert! h using 1
  rw [phiOdd_eq_deficits hs.le]
  field_simp
  ring

theorem evenInitial_hasDerivAt {s : ℝ} (hs : 1 < s) :
    HasDerivAt evenInitial (-s / (s - 1) ^ 2 * sieveA) s := by
  have hn : s - 1 ≠ 0 := by linarith
  have h := (((hasDerivAt_id s).div ((hasDerivAt_id s).sub_const 1) hn).sub
    (((hasDerivAt_id s).sub_const 1).log hn)).const_mul sieveA
  convert! h using 1
  simp only [id_eq, one_mul, mul_one]
  field_simp
  ring

theorem phiEven_hasDerivAt {s : ℝ} (hs : 1 < s) :
    HasDerivAt phiEven (-s / (s - 1) ^ 2 * phiOdd (s - 1)) s := by
  by_cases hs3 : s < 3
  · have heq : phiEven =ᶠ[𝓝 s] evenInitial := by
      filter_upwards [Ioo_mem_nhds hs hs3] with t ht
      exact phiEven_explicit ht.1 (by linarith [ht.2])
    rw [phiOdd_initial (s := s - 1) (by linarith)]
    exact (evenInitial_hasDerivAt hs).congr_of_eventuallyEq heq
  · have hs2 : 2 < s := by linarith
    have hU := (upperDeficit_hasDerivAt (s := s - 1) (by linarith)).comp s
      ((hasDerivAt_id s).sub_const 1)
    have h := (hasDerivAt_id s).mul ((lowerDeficit_hasDerivAt hs2).add hU)
    have heq : phiEven =ᶠ[𝓝 s] (fun t => t * (lowerDeficit t + upperDeficit (t - 1))) := by
      filter_upwards [Ioi_mem_nhds hs2] with t ht
      exact phiEven_eq_deficits ht.le
    have hd := h.congr_of_eventuallyEq heq
    convert! hd using 1
    simp only [id_eq, Pi.add_apply, Function.comp_apply, one_mul, mul_one]
    rw [phiEven_eq_deficits hs2.le]
    field_simp
    ring

theorem phiOdd_hasDerivAt {s : ℝ} (hs : 3 < s) :
    HasDerivAt phiOdd (-s / (s - 1) ^ 2 * phiEven (s - 1)) s := by
  have hA := (lowerDeficit_hasDerivAt (s := s - 1) (by linarith)).comp s
    ((hasDerivAt_id s).sub_const 1)
  have h := (hasDerivAt_id s).mul ((upperDeficit_hasDerivAt (by linarith : 1 < s)).add hA)
  have heq : phiOdd =ᶠ[𝓝 s] (fun t => t * (upperDeficit t + lowerDeficit (t - 1))) := by
    filter_upwards [Ioi_mem_nhds (show 1 < s by linarith)] with t ht
    exact phiOdd_eq_deficits ht.le
  have hd := h.congr_of_eventuallyEq heq
  convert! hd using 1
  simp only [id_eq, Pi.add_apply, Function.comp_apply, one_mul, mul_one]
  rw [phiOdd_eq_deficits (by linarith)]
  field_simp
  ring

theorem phiEven_pos {s : ℝ} (hs : 1 < s) : 0 < phiEven s := by
  by_cases hs2 : 2 ≤ s
  · rw [phiEven_eq_deficits hs2]
    exact mul_pos (by linarith) (add_pos (deficits_pos (by linarith)).1
      (deficits_pos (s := s - 1) (by linarith)).2)
  · rw [phiEven_initial (by linarith)]
    unfold evenInitial
    have hlog : Real.log (s - 1) < 0 := Real.log_neg (by linarith) (by linarith)
    exact mul_pos sieveA_pos (sub_pos.mpr (lt_trans hlog (div_pos (by linarith) (by linarith))))

theorem phiOdd_pos (s : ℝ) : 0 < phiOdd s := by
  by_cases hs3 : s ≤ 3
  · rw [phiOdd_initial hs3]
    exact sieveA_pos
  · rw [phiOdd_eq_deficits (by linarith)]
    exact mul_pos (by linarith) (add_pos (deficits_pos (by linarith)).2
      (deficits_pos (s := s - 1) (by linarith)).1)

theorem phiEven_continuousAt {s : ℝ} (hs : 1 < s) : ContinuousAt phiEven s :=
  (phiEven_hasDerivAt hs).continuousAt

theorem phiOdd_continuous : Continuous phiOdd := by
  apply continuous_iff_continuousAt.mpr
  intro s
  by_cases hs3 : s < 3
  · have heq : phiOdd =ᶠ[𝓝 s] (fun _ => sieveA) := by
      filter_upwards [Iio_mem_nhds hs3] with t ht
      exact phiOdd_initial ht.le
    exact continuousAt_const.congr_of_eventuallyEq heq
  · have heq : phiOdd =ᶠ[𝓝 s] (fun t => t * (upperDeficit t + lowerDeficit (t - 1))) := by
      filter_upwards [Ioi_mem_nhds (show 1 < s by linarith)] with t ht
      exact phiOdd_eq_deficits ht.le
    have hcU : ContinuousAt upperDeficit s :=
      (F_continuousAt sieveA (by linarith)).sub continuousAt_const
    have hcA : ContinuousAt (fun t => lowerDeficit (t - 1)) s :=
      (lowerDeficit_continuous.comp (continuous_id.sub continuous_const)).continuousAt
    exact (continuousAt_id.mul (hcU.add hcA)).congr_of_eventuallyEq heq

theorem f_hasDerivAt {s : ℝ} (hs : 2 < s) :
    HasDerivAt (f sieveA) (phiEven s / s ^ 2) s := by
  convert! (lowerDeficit_hasDerivAt hs).const_sub 1 using 1
  · ext t
    change f sieveA t = 1 - (1 - f sieveA t)
    ring
  · ring

theorem F_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt (F sieveA) (-phiOdd s / s ^ 2) s := by
  by_cases hs1 : 1 < s
  · convert! (upperDeficit_hasDerivAt hs1).add_const 1 using 1
    ext t
    change F sieveA t = (F sieveA t - 1) + 1
    ring
  · have heq : F sieveA =ᶠ[𝓝 s] (fun t => sieveA / t) := by
      filter_upwards [Ioo_mem_nhds hs (show s < 3 by linarith)] with t ht
      exact F_initial sieveA ht.1 ht.2.le
    have hd := ((hasDerivAt_const s sieveA).div (hasDerivAt_id s) (ne_of_gt hs)).congr_of_eventuallyEq heq
    convert! hd using 1
    rw [phiOdd_initial (by linarith)]
    simp only [id_eq, zero_mul, zero_sub, mul_one]

theorem startingExtension_hasDerivAt {s : ℝ} (hs : 1 < s) :
    HasDerivAt (startingExtension sieveA) (evenInitial s / s ^ 2) s := by
  have hn : s - 1 ≠ 0 := by linarith
  have hd := ((((hasDerivAt_id s).sub_const 1).log hn).const_mul sieveA).div
    (hasDerivAt_id s) (by linarith : s ≠ 0)
  convert! hd using 1
  simp only [evenInitial, id_eq, mul_one]
  field_simp

theorem f_right_derivative_two :
    HasDerivWithinAt (f sieveA) (phiEven 2 / 2 ^ 2) (Ici 2) 2 := by
  rw [phiEven_initial le_rfl]
  apply (startingExtension_hasDerivAt (s := 2) (by norm_num)).hasDerivWithinAt.congr_of_eventuallyEq_of_mem
  · filter_upwards [self_mem_nhdsWithin,
      (nhdsWithin_le_nhds (Iio_mem_nhds (show (2 : ℝ) < 4 by norm_num)))] with t ht ht4
    exact (startingExtension_eq_f sieveA ht ht4.le).symm
  · exact self_mem_Ici

theorem phiEven_eq_deriv {s : ℝ} (hs : 2 < s) :
    phiEven s = s ^ 2 * deriv (f sieveA) s := by
  rw [(f_hasDerivAt hs).deriv]
  field_simp

theorem phiOdd_eq_deriv {s : ℝ} (hs : 0 < s) :
    phiOdd s = -s ^ 2 * deriv (F sieveA) s := by
  rw [(F_hasDerivAt hs).deriv]
  field_simp

theorem phiEven_eq_right_deriv_two :
    phiEven 2 = 2 ^ 2 * derivWithin (f sieveA) (Ici 2) 2 := by
  rw [f_right_derivative_two.derivWithin (uniqueDiffWithinAt_Ici (2 : ℝ))]
  ring

theorem phiEven_strictAntiOn : StrictAntiOn phiEven (Ioi 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 1)
  · intro s hs
    exact (phiEven_continuousAt hs).continuousWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    change 1 < s at hs
    rw [(phiEven_hasDerivAt hs).deriv]
    exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by linarith)
      (sq_pos_of_pos (by linarith))) (phiOdd_pos _)

theorem phiOdd_antitone : Antitone phiOdd := by
  have htail : AntitoneOn phiOdd (Ici 3) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 3) phiOdd_continuous.continuousOn
    · intro s hs
      rw [interior_Ici] at hs
      exact (phiOdd_hasDerivAt hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      change 3 < s at hs
      rw [(phiOdd_hasDerivAt hs).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
        (phiEven_pos (by linarith)).le
  intro x y hxy
  by_cases hy : y ≤ 3
  · rw [phiOdd_initial hy, phiOdd_initial (le_trans hxy hy)]
  · by_cases hx : x ≤ 3
    · rw [phiOdd_initial hx, ← phiOdd_initial (s := 3) le_rfl]
      exact htail (by simp) (le_of_not_ge hy) (le_of_not_ge hy)
    · exact htail (le_of_not_ge hx) (le_of_not_ge hy) hxy

end NumberTheoryLean.DerivativeWeights

end

section

namespace NumberTheoryLean.WeightFutureIntegrals

open Filter Set MeasureTheory
open scoped Topology
open NormalizedDeficits DeficitFutureIntegrals DerivativeWeights

theorem phiEven_tendsto_zero : Tendsto phiEven atTop (𝓝 0) := by
  have hshift : Tendsto (fun s : ℝ => s - 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro v
    exact eventually_atTop.mpr ⟨v + 1, fun s hs => by linarith⟩
  have hl := lowerDeficit_mass_tendsto_zero.add
    ((upperDeficit_mass_tendsto_zero.comp hshift).add (upperDeficit_tendsto_zero.comp hshift))
  simp only [add_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
  rw [phiEven_eq_deficits hs]
  simp only [Function.comp_apply]
  ring

theorem phiOdd_tendsto_zero : Tendsto phiOdd atTop (𝓝 0) := by
  have hshift : Tendsto (fun s : ℝ => s - 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro v
    exact eventually_atTop.mpr ⟨v + 1, fun s hs => by linarith⟩
  have hl := upperDeficit_mass_tendsto_zero.add
    ((lowerDeficit_mass_tendsto_zero.comp hshift).add (lowerDeficit_tendsto_zero.comp hshift))
  simp only [add_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
  rw [phiOdd_eq_deficits hs]
  simp only [Function.comp_apply]
  ring

theorem W_pos {t : ℝ} (ht : 0 < t) : 0 < W t := by
  unfold W
  positivity

theorem future_integral_of_shifted_deriv {P B : ℝ → ℝ} {s : ℝ}
    (hc : ContinuousAt P s)
    (hd : ∀ t, s < t → HasDerivAt P (-B (t - 1)) t)
    (hb : ∀ t, s - 1 < t → 0 ≤ B t)
    (hl : Tendsto P atTop (𝓝 0)) :
    IntegrableOn B (Ioi (s - 1)) ∧ P s = ∫ t in Ioi (s - 1), B t := by
  let H : ℝ → ℝ := fun t => P (t + 1)
  have hc' : ContinuousWithinAt H (Ici (s - 1)) (s - 1) := by
    have hcs : ContinuousAt P ((s - 1) + 1) := by simpa only [sub_add_cancel] using hc
    exact (hcs.comp (f := fun t : ℝ => t + 1) (x := s - 1)
      (continuous_id.add continuous_const).continuousAt).continuousWithinAt
  have hder : ∀ t ∈ Ioi (s - 1), HasDerivAt H (-B t) t := by
    intro t ht
    have h := (hd (t + 1) (by change s - 1 < t at ht; linarith)).comp t
      ((hasDerivAt_id t).add_const 1)
    convert! h using 1
    simp
  have hn : ∀ t ∈ Ioi (s - 1), -B t ≤ 0 := fun t ht => neg_nonpos.mpr (hb t ht)
  have hshift : Tendsto (fun t : ℝ => t + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro v
    exact eventually_atTop.mpr ⟨v - 1, fun t ht => by linarith⟩
  have hlim : Tendsto H atTop (𝓝 0) := hl.comp hshift
  have hint := integrableOn_Ioi_deriv_of_nonpos hc' hder hn hlim
  have heq := integral_Ioi_of_hasDerivAt_of_nonpos hc' hder hn hlim
  constructor
  · exact integrable_neg_iff.mp hint
  · simp only [integral_neg, H, sub_add_cancel, zero_sub] at heq
    linarith

theorem phiEven_future_integral {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t => W t * phiOdd t) (Ioi (s - 1)) ∧
      phiEven s = ∫ t in Ioi (s - 1), W t * phiOdd t := by
  apply future_integral_of_shifted_deriv (phiEven_continuousAt hs) ?_ ?_ phiEven_tendsto_zero
  · intro t ht
    convert! phiEven_hasDerivAt (lt_trans hs ht) using 1
    simp only [W, sub_add_cancel]
    ring
  · intro t ht
    exact (mul_pos (W_pos (by linarith)) (phiOdd_pos t)).le

theorem phiOdd_future_integral (s : ℝ) :
    IntegrableOn (fun t => W t * phiEven t) (Ioi (max 2 (s - 1))) ∧
      phiOdd s = ∫ t in Ioi (max 2 (s - 1)), W t * phiEven t := by
  have hc := phiOdd_continuous.continuousAt (x := max 3 s)
  have hder : ∀ t, max 3 s < t →
      HasDerivAt phiOdd (-(W (t - 1) * phiEven (t - 1))) t := by
    intro t ht
    convert! phiOdd_hasDerivAt (lt_of_le_of_lt (le_max_left _ _) ht) using 1
    simp only [W, sub_add_cancel]
    ring
  have hn : ∀ t, max 3 s - 1 < t → 0 ≤ W t * phiEven t := by
    intro t ht
    have ht1 : 1 < t := by linarith [le_max_left (3 : ℝ) s]
    exact (mul_pos (W_pos (by linarith)) (phiEven_pos ht1)).le
  have h := future_integral_of_shifted_deriv hc hder hn phiOdd_tendsto_zero
  have hmax : max 3 s - 1 = max 2 (s - 1) := by
    by_cases hs : s ≤ 3
    · rw [max_eq_left hs, max_eq_left (by linarith)]
      norm_num
    · rw [max_eq_right (le_of_not_ge hs), max_eq_right (by linarith)]
  have heq : phiOdd (max 3 s) = phiOdd s := by
    by_cases hs : s ≤ 3
    · rw [max_eq_left hs, phiOdd_initial le_rfl, phiOdd_initial hs]
    · rw [max_eq_right (le_of_not_ge hs)]
  simpa only [hmax, heq] using h

end NumberTheoryLean.WeightFutureIntegrals

end

end Erdos970

end OAI
