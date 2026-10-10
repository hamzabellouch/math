import OAI.Dynamics.EntropyCounterexample.GainProfile
import OAI.Dynamics.EntropyCounterexample.ClockPeriodization

namespace OAI

noncomputable section

namespace Problem340

def periodicGain (L : ℝ) (t : ℝ) : ℝ :=
  ClockPeriodization.periodize 100 (fun x : ℝ × ℝ => gainProfile L x.1) (t, 0)

lemma gainProfile_nonzero_mem {L t : ℝ} (h : gainProfile L t ≠ 0) :
    t ∈ Set.Ioo (6 : ℝ) 96 := by
  by_contra ht
  exact h (gainProfile_zero_outside ht)

lemma periodicGain_contDiff (L : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (periodicGain L) := by
  apply (ClockPeriodization.contDiff_periodize (P := 100) (a := 6) (b := 96)
    (by norm_num) ((gainProfile_contDiff L).comp contDiff_fst) ?_).comp
    (contDiff_id.prodMk contDiff_const)
  intro x hx
  exact ⟨(gainProfile_nonzero_mem hx).1.le, (gainProfile_nonzero_mem hx).2.le⟩

lemma periodicGain_periodic (L : ℝ) : Function.Periodic (periodicGain L) 100 := by
  intro t
  exact ClockPeriodization.periodize_add_period 100
    (fun x : ℝ × ℝ => gainProfile L x.1) t 0

lemma periodicGain_mem_Icc {L : ℝ} (hL : 0 ≤ L) (t : ℝ) :
    periodicGain L t ∈ Set.Icc (0 : ℝ) L := by
  apply ClockPeriodization.periodize_mem_Icc (a := 6) (b := 96)
    (by norm_num) (by norm_num) hL
  · intro x hx
    exact gainProfile_nonzero_mem hx
  · intro x
    exact gainProfile_mem_Icc hL x.1

lemma periodicGain_eq {L t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 100) :
    periodicGain L t = gainProfile L t := by
  apply ClockPeriodization.periodize_eq_on_fundamental (by norm_num) ?_ ht (0 : ℝ)
  intro x hx
  obtain ⟨hx0, hx1⟩ := gainProfile_nonzero_mem hx
  constructor <;> linarith

lemma periodicGain_eq_gain (L : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (7 : ℝ) 90) :
    periodicGain L t = L := by
  rw [periodicGain_eq (by constructor <;> linarith [ht.1, ht.2])]
  exact gainProfile_eq_gain L ht

lemma periodicGain_eq_zero (L : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (2 : ℝ) 5) :
    periodicGain L t = 0 := by
  rw [periodicGain_eq (by constructor <;> linarith [ht.1, ht.2])]
  exact gainProfile_eq_zero L ht

theorem exists_periodic_gain {L : ℝ} (hL : 0 ≤ L) :
    ∃ a : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) a ∧ Function.Periodic a 100 ∧
      (∀ t, a t ∈ Set.Icc (0 : ℝ) L) ∧
      (∀ t ∈ Set.Icc (2 : ℝ) 5, a t = 0) ∧
      (∀ t ∈ Set.Icc (7 : ℝ) 90, a t = L) :=
  ⟨periodicGain L, periodicGain_contDiff L, periodicGain_periodic L,
    periodicGain_mem_Icc hL, fun _ ht => periodicGain_eq_zero L ht,
    fun _ ht => periodicGain_eq_gain L ht⟩

section CircleLift

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

lemma gainProfile_liftIco_coe_eq_periodicGain (L t : ℝ) :
    AddCircle.liftIco (100 : ℝ) 0 (gainProfile L) (t : AddCircle (100 : ℝ)) =
      periodicGain L t := by
  let r := AddCircle.equivIco (100 : ℝ) 0 (t : AddCircle (100 : ℝ))
  have hr : (r : ℝ) ∈ Set.Icc (0 : ℝ) 100 := by
    simpa only [zero_add] using Set.Ico_subset_Icc_self r.property
  have hrep : ((r : ℝ) : AddCircle (100 : ℝ)) = (t : AddCircle (100 : ℝ)) :=
    AddCircle.coe_equivIco
  have hp := periodicGain_periodic L
  calc
    AddCircle.liftIco (100 : ℝ) 0 (gainProfile L) (t : AddCircle (100 : ℝ)) =
        gainProfile L r := rfl
    _ = periodicGain L r := (periodicGain_eq hr).symm
    _ = hp.lift ((r : ℝ) : AddCircle (100 : ℝ)) := (hp.lift_coe _).symm
    _ = hp.lift (t : AddCircle (100 : ℝ)) := congrArg hp.lift hrep
    _ = periodicGain L t := hp.lift_coe t

lemma gainProfile_liftIco_coe_contDiff (L : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ =>
      AddCircle.liftIco (100 : ℝ) 0 (gainProfile L) (t : AddCircle (100 : ℝ))) := by
  simpa only [gainProfile_liftIco_coe_eq_periodicGain] using periodicGain_contDiff L

end CircleLift

end Problem340

end

end OAI
