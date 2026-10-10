import OAI.Dynamics.EntropyCounterexample.ClockPeriodizationLocal
import OAI.Dynamics.EntropyCounterexample.ClockLocalExtension

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace Problem340.ClockQuotient
local instance : Fact (0 < (100 : ℝ)) := ⟨by norm_num⟩

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in

theorem liftIco_clockHomeomorph_periodic {f : ℝ × E → F}
    (hp : ∀ z, Periodic (fun t => f (t, z)) 100) (p : ℝ × E) :
    AddCircle.liftIco (100 : ℝ) 0 (fun t => f (t, p.2))
      (clockHomeomorph.symm (clockHomeomorph (p.1 : AddCircle (100 : ℝ)))) = f p := by
  rw [clockHomeomorph.symm_apply_apply]
  exact (liftPeriodic_eq_liftIco f hp ((p.1 : AddCircle (100 : ℝ)), p.2)).symm.trans
    (liftPeriodic_coe f hp p.1 p.2)

theorem hasLocalC1Extension_liftIco_of_periodic {f : ℝ × E → F}
    (hp : ∀ z, Periodic (fun t => f (t, z)) 100) (hf : ContDiff ℝ 1 f) :
    HasLocalC1Extension (fun x : StandardClock × E => (x.1.1, x.2))
      (fun x => AddCircle.liftIco (100 : ℝ) 0 (fun t => f (t, x.2))
        (clockHomeomorph.symm x.1)) := by
  apply hasLocalC1Extension_of_clock_lift_with_parameters
  simpa only [liftIco_clockHomeomorph_periodic hp] using hf

theorem hasLocalC1Extension_liftIco_of_periodic_on {V : Set E} (hV : IsOpen V)
    {f : ℝ × E → F} (hp : ∀ z, Periodic (fun t => f (t, z)) 100)
    (hf : ContDiffOn ℝ 1 f (univ ×ˢ V)) :
    HasLocalC1Extension (fun x : StandardClock × V => (x.1.1, x.2.1))
      (fun x => AddCircle.liftIco (100 : ℝ) 0 (fun t => f (t, x.2.1))
        (clockHomeomorph.symm x.1)) := by
  refine hasLocalC1Extension_of_clock_lift_on hV
    (fun x : StandardClock × E => AddCircle.liftIco (100 : ℝ) 0
      (fun t => f (t, x.2)) (clockHomeomorph.symm x.1)) ?_
  simpa only [liftIco_clockHomeomorph_periodic hp] using hf

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in

theorem liftIco_clockHomeomorph_strip {f : ℝ × E → F}
    (hs : ∀ x, f x ≠ 0 → x.1 ∈ Ioo 0 100) (p : ℝ × E) :
    AddCircle.liftIco (100 : ℝ) 0 (fun t => f (t, p.2))
      (clockHomeomorph.symm (clockHomeomorph (p.1 : AddCircle (100 : ℝ)))) =
        periodize 100 f p := by
  rw [clockHomeomorph.symm_apply_apply]
  exact (liftPeriodize_eq_liftIco hs ((p.1 : AddCircle (100 : ℝ)), p.2)).symm.trans
    (liftPeriodize_coe 100 f p.1 p.2)

theorem hasLocalC1Extension_liftIco_of_strip_support {f : ℝ × E → F}
    (hf : ContDiff ℝ 1 f) (hs : ∀ x, f x ≠ 0 → x.1 ∈ Ioo 0 100) :
    HasLocalC1Extension (fun x : StandardClock × E => (x.1.1, x.2))
      (fun x => AddCircle.liftIco (100 : ℝ) 0 (fun t => f (t, x.2))
        (clockHomeomorph.symm x.1)) := by
  apply hasLocalC1Extension_of_clock_lift_with_parameters
  have hs' : ∀ x, f x ≠ 0 → x.1 ∈ Icc 0 100 :=
    fun x hx => ⟨(hs x hx).1.le, (hs x hx).2.le⟩
  simpa only [liftIco_clockHomeomorph_strip hs] using
    contDiff_periodize (by norm_num : (0 : ℝ) < 100) hf hs'

theorem hasLocalC1Extension_liftIco_of_strip_support_on {V : Set E} (hV : IsOpen V)
    {f : ℝ × E → F} (hf : ContDiffOn ℝ 1 f (univ ×ˢ V))
    (hs : ∀ x, f x ≠ 0 → x.1 ∈ Ioo 0 100) :
    HasLocalC1Extension (fun x : StandardClock × V => (x.1.1, x.2.1))
      (fun x => AddCircle.liftIco (100 : ℝ) 0 (fun t => f (t, x.2.1))
        (clockHomeomorph.symm x.1)) := by
  refine hasLocalC1Extension_of_clock_lift_on hV
    (fun x : StandardClock × E => AddCircle.liftIco (100 : ℝ) 0
      (fun t => f (t, x.2)) (clockHomeomorph.symm x.1)) ?_
  have hs' : ∀ x, f x ≠ 0 → x.1 ∈ Icc 0 100 :=
    fun x hx => ⟨(hs x hx).1.le, (hs x hx).2.le⟩
  simpa only [liftIco_clockHomeomorph_strip hs] using
    contDiffOn_periodize (by norm_num : (0 : ℝ) < 100) hf hs'

end Problem340.ClockQuotient

end

end OAI
