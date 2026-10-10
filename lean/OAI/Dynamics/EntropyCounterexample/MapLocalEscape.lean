import OAI.Dynamics.EntropyCounterexample.MapPassageSchedule
import OAI.Dynamics.EntropyCounterexample.MapConcretePassage
import OAI.Dynamics.EntropyCounterexample.MapPreparationRadius
import OAI.Dynamics.EntropyCounterexample.MapRecoveredReadout

namespace OAI

noncomputable section

namespace Problem340.Construction

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

theorem concrete_unbounded_clock_local_escape
    (L : ℝ) (hL : 2 < L) (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1)
    (hunbounded : ¬ BddAbove (Set.range (rawClockLift (concreteData L hL) x t₀)))
    (z : ℕ → ℂ)
    (hz : ∀ n, (z n : Sphere) = ((concreteMap L hL)^[n] x).2.1)
    (k : ℤ) (hk : t₀ < 100 * (k : ℝ)) :
    ∃ s hi : ℕ, 100 * (k : ℝ) ≤ rawClockLift (concreteData L hL) x t₀ s ∧
      rawClockLift (concreteData L hL) x t₀ s < 100 * (k : ℝ) + 74 ∧
      100 * (k : ℝ) + 80 ≤ rawClockLift (concreteData L hL) x t₀ hi ∧
      (∀ n, s ≤ n → n < hi → ‖z n‖ ^ 2 ≤ ‖z (n + 1)‖) ∧
      ∃ j, s ≤ j ∧ j ≤ hi ∧ 1 < ‖z j‖ := by
  classical
  let D := concreteData L hL
  let y : ℕ → RawManifold := fun n => (concreteMap L hL)^[n] x
  let t : ℕ → ℝ := rawClockLift D x t₀
  let u : ℕ → ℝ := fun n => t n - 100 * (k : ℝ)
  have hy : ∀ n, y (n + 1) = concreteMap L hL (y n) := by
    intro n
    exact Function.iterate_succ_apply' (concreteMap L hL) n x
  have hmono : Monotone u := by
    intro a b hab
    exact sub_le_sub_right (monotone_rawClockLift D
      (concrete_gate_mem_Icc L hL) x t₀ hab) _
  have hlift : ∀ n, (u n : AddCircle (100 : ℝ)) = (y n).1 :=
    coe_rawClockLift_sub_period D x t₀ h₀ k
  have hclock : ∀ n, u (n + 1) = u n + Clock.increment (u n) (D.gate (y n).2.1) :=
    rawClockLift_sub_period_succ D x t₀ h₀ k
  have hscheduled := rawOrbit_hasScheduledPassageAt D
    (concrete_gate_mem_Icc L hL) x t₀ h₀ hunbounded k hk
  rcases hscheduled with
    ⟨lo, hi, hlohi, hlo, hhi, hinside, hne, hcard, hprep,
      ⟨r, hr, hr0, hr1, hrbefore⟩, ⟨j, hj, hj0, hj1, l, hl⟩⟩
  let I := (Finset.Ico lo hi).filter (fun i => 0 < preparationCoeff (u i))
  change I.Nonempty at hne
  have hinside' : ∀ n, lo ≤ n → n < hi → u n ∈ Set.Ico (0 : ℝ) 100 := hinside
  obtain ⟨s, K, hsI, hlos, hsK, hKhi, hIK, hearly, hus⟩ :=
    complete_passage_phase_window y u hmono hlift lo hi hinside' hne
  have hsI' : s ∈ I := hsI
  have hshi : s < hi := hsK.trans_le hKhi
  have hreset : ∀ l : Fin 3, (y s).2.2 l = ((0 : ℂ) : Sphere) := by
    apply complete_passage_register_reset_at_first_preparation L hL y hy u hlift
      lo hi r s (Finset.mem_Ico.mp hr).1 (hrbefore s hsI') hshi
      (show u r ∈ Set.Icc 2 5 from ⟨hr0, by linarith⟩) hinside'
    intro i hiI
    exact (hIK i hiI).1
  have hhalf : ∀ i ∈ I, (1 / 2 : ℝ) < ‖z i‖ := by
    intro i hiI
    have hiprep : preparationCoeff (u i) ≠ 0 := ne_of_gt (Finset.mem_filter.mp hiI).2
    have hisupport : u i ∈ Set.Ioo 8 12 := by
      rwa [← preparationCoeff_support, Function.mem_support]
    apply concrete_preparation_radius L hL x t₀ h₀ hunbounded z hz i k
    simpa only [u, t, mul_comm (100 : ℝ) (k : ℝ)] using hisupport
  have hzs : z s ≠ 0 := by
    intro hzero
    have hh := hhalf s hsI'
    rw [hzero, norm_zero] at hh
    norm_num at hh
  have hregister : ∀ n, s ≤ n → n < hi → ∀ l : Fin 3,
      orbitReadoutCoeff y n l ≠ 0 →
      orbitSaturatedRegister D y n l = ((orbitReadoutCoeff y n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (passageWeight D u z i : ℂ) *
          PassagePhase.phase (z i) ^ (2 ^ (n - i + 1)) := by
    intro n hsn hnhi l hnread
    have hnstrip := hinside' n (hlos.trans hsn) hnhi
    have hcoeff := orbitReadoutCoeff_eq_of_clock_lift y u hlift n hnstrip l
    have hread : readoutCoeff l (u n) ≠ 0 := by rwa [hcoeff] at hnread
    have hset : passagePreparationIndices u s n = I := by
      ext i
      constructor
      · intro hiI
        obtain ⟨hist, hip⟩ := Finset.mem_filter.mp hiI
        obtain ⟨hsi, hin⟩ := Finset.mem_Ico.mp hist
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
          ⟨hlos.trans hsi, hin.trans hnhi⟩,
          lt_of_le_of_ne (preparationCoeff_nonneg _) (Ne.symm hip)⟩
      · intro hiI
        have hip : preparationCoeff (u i) ≠ 0 := ne_of_gt (Finset.mem_filter.mp hiI).2
        have hin := preparation_before_readout hmono hip hread
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨(hIK i hiI).1, hin⟩, hip⟩
    apply rawMap_recovered_readout_of_gain_profile D (by change 1 ≤ L; linarith)
      (fun w => (concrete_gate_mem_Icc L hL w).1) (concrete_cutoff_mem_Icc L hL)
      ?_ ?_ y hy u hlift hclock z I l s n hsn (by linarith [hus.1])
      (hreset l) hset (fun i _ => hz i) hnstrip hnread
    · intro w hw
      exact saturation_eq_self (3 * L) (by linarith) hw
    · intro a ha
      exact gainProfile_eq_gain L ha
  have hz' : ∀ n, s ≤ n → n ≤ hi → (z n : Sphere) = (y n).2.1 :=
    fun n _ _ => hz n
  have hstep : ∀ n, s ≤ n → n < hi → y (n + 1) = concreteMap L hL (y n) :=
    fun n _ _ => hy n
  have hread : ∃ n, s ≤ n ∧ n < hi ∧ ∃ l : Fin 3, orbitReadoutCoeff y n l = 1 := by
    have hjstrip := hinside' j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
    have hcoeff := orbitReadoutCoeff_eq_of_clock_lift y u hlift j hjstrip l
    have hprepS : preparationCoeff (u s) ≠ 0 := ne_of_gt (Finset.mem_filter.mp hsI').2
    have hsltj := preparation_before_readout hmono hprepS
      (show readoutCoeff l (u j) ≠ 0 by rw [hl]; norm_num)
    exact ⟨j, hsltj.le, (Finset.mem_Ico.mp hj).2, l, hcoeff.trans hl⟩
  have hsquare := concreteMap_passage_square_le L hL y u z I s K hi
    hzs hz' hIK hearly hregister hstep
  have hlarge := concreteMap_passage_escape L hL y u z I s K hi
    hzs hz' hIK hearly hregister hstep hKhi hhalf hprep hread
  refine ⟨s, hi, ?_, ?_, ?_, hsquare, hlarge⟩
  · change 100 * (k : ℝ) ≤ t s
    have hu := hus.1
    change 8 < t s - 100 * (k : ℝ) at hu
    linarith
  · change t s < 100 * (k : ℝ) + 74
    have hu := hus.2
    change t s - 100 * (k : ℝ) < 12 at hu
    linarith
  · change 100 * (k : ℝ) + 80 ≤ t hi
    have hu := hhi.1
    change 100 ≤ t hi - 100 * (k : ℝ) at hu
    linarith

end Problem340.Construction

end

end OAI
