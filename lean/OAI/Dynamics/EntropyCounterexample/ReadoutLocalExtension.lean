import OAI.Dynamics.EntropyCounterexample.ReadoutCover
import OAI.Dynamics.EntropyCounterexample.ClockPeriodization
import OAI.Dynamics.EntropyCounterexample.C1CoordinatePullback

namespace OAI

noncomputable section

open scoped ContDiff

namespace Problem340

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

private lemma reader_nonzero_mem (i : Fin 3) {t : ℝ} (h : readoutCoeff i t ≠ 0) :
    t ∈ Set.Ioo (74 : ℝ) 80 := by
  apply readoutInterval_subset i
  rw [← readoutCoeff_support]
  exact h

def periodicReadoutReal (i : Fin 3) (t : ℝ) : ℝ :=
  ClockPeriodization.periodize 100 (fun x : ℝ × ℝ => readoutCoeff i x.1) (t, 0)

lemma periodicReadoutReal_contDiff (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (periodicReadoutReal i) := by
  apply (ClockPeriodization.contDiff_periodize (P := 100) (a := 74) (b := 80)
    (by norm_num) ((readoutCoeff_contDiff i).comp contDiff_fst) ?_).comp
    (contDiff_id.prodMk contDiff_const)
  intro x hx
  exact ⟨(reader_nonzero_mem i hx).1.le, (reader_nonzero_mem i hx).2.le⟩

lemma periodicReadoutReal_periodic (i : Fin 3) :
    Function.Periodic (periodicReadoutReal i) 100 := by
  intro t
  exact ClockPeriodization.periodize_add_period 100
    (fun x : ℝ × ℝ => readoutCoeff i x.1) t 0

lemma periodicReadoutReal_eq (i : Fin 3) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 100) :
    periodicReadoutReal i t = readoutCoeff i t := by
  apply ClockPeriodization.periodize_eq_on_fundamental (by norm_num) ?_ ht (0 : ℝ)
  intro x hx
  obtain ⟨hx0, hx1⟩ := reader_nonzero_mem i hx
  constructor <;> linarith

lemma readoutCoeff_liftIco_coe_eq_periodic (i : Fin 3) (t : ℝ) :
    AddCircle.liftIco (100 : ℝ) 0 (readoutCoeff i) (t : AddCircle (100 : ℝ)) =
      periodicReadoutReal i t := by
  let r := AddCircle.equivIco (100 : ℝ) 0 (t : AddCircle (100 : ℝ))
  have hr : (r : ℝ) ∈ Set.Icc (0 : ℝ) 100 := by
    simpa only [zero_add] using Set.Ico_subset_Icc_self r.property
  have hrep : ((r : ℝ) : AddCircle (100 : ℝ)) = (t : AddCircle (100 : ℝ)) :=
    AddCircle.coe_equivIco
  have hp := periodicReadoutReal_periodic i
  calc
    AddCircle.liftIco (100 : ℝ) 0 (readoutCoeff i) (t : AddCircle (100 : ℝ)) =
        readoutCoeff i r := rfl
    _ = periodicReadoutReal i r := (periodicReadoutReal_eq i hr).symm
    _ = hp.lift ((r : ℝ) : AddCircle (100 : ℝ)) := (hp.lift_coe _).symm
    _ = hp.lift (t : AddCircle (100 : ℝ)) := congrArg hp.lift hrep
    _ = periodicReadoutReal i t := hp.lift_coe t

def standardReader (i : Fin 3) (x : StandardClock) : ℝ :=
  AddCircle.liftIco (100 : ℝ) 0 (readoutCoeff i) (clockHomeomorph.symm x)

lemma standardReader_param (i : Fin 3) (t : ℝ) :
    standardReader i (clockHomeomorph (t : AddCircle (100 : ℝ))) =
      periodicReadoutReal i t := by
  simp only [standardReader, clockHomeomorph.symm_apply_apply,
    readoutCoeff_liftIco_coe_eq_periodic]

lemma standardReader_mem_Icc (i : Fin 3) (x : StandardClock) :
    standardReader i x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨readoutCoeff_nonneg i _, readoutCoeff_le_one i _⟩

theorem standardReader_hasLocalC1Extension (i : Fin 3) :
    HasLocalC1Extension (fun x : StandardClock => x.1) (standardReader i) := by
  apply hasLocalC1Extension_of_clock_lift
  simpa only [standardReader_param] using (periodicReadoutReal_contDiff i).of_le
    (show (1 : ℕ∞ω) ≤ (⊤ : ℕ∞) by simp)

theorem standardReader_hasLocalC1Extension_manifold (i : Fin 3) (q : ℕ) :
    HasLocalC1Extension (standardEmbedding q)
      (fun x : CounterexampleManifold q => standardReader i x.1) :=
  (standardReader_hasLocalC1Extension i).clock_coordinate

end Problem340

end

end OAI
