import Mathlib
import OAI.Probability.Ballisticity.Stationary.StationaryArrayLaw
import OAI.Probability.Ballisticity.Stationary.StationaryProfile2

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

theorem crossing_estimate {d : ℕ} (hd : 2≤d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) (D : ℝ) (hD : 0≤D) :
    ∀ᶠ N : ℕ in atTop, (environmentLaw ν).real (badCrossingEvent e N (1/2)) < (N:ℝ)^(-D) := by
  have : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  obtain ⟨f,hf⟩ := exists_ne e.1
  obtain ⟨C⟩ := operational_constants_exist ν hue e (f,true) (Ne.symm hf) htrans D hD
  by_contra hh
  have hfreq : ∃ᶠ N : ℕ in atTop, (N:ℝ)^(-D)≤(environmentLaw ν).real (badCrossingEvent e N (1/2)) := by
    simpa only [not_lt] using not_eventually.mp hh
  have hfloor : ∀ᶠ N : ℕ in atTop, C.sfloor≤(N:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have hlog : Tendsto (fun N : ℕ => (1/2:ℝ)*Real.log (N:ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
  have hlarge : ∀ᶠ N : ℕ in atTop, 32*C.b≤(1/2:ℝ)*Real.log (N:ℝ) :=
    hlog.eventually (eventually_ge_atTop _)
  have hex := frequently_atTop.mp (hfreq.and_eventually (hfloor.and hlarge))
  choose Ns hNs hmass hfloor hlarge using hex
  obtain ⟨L⟩ := C.bad_stationary_array_law (Ne.symm hf) hD Ns
    (tendsto_atTop_mono hNs tendsto_id) hfloor hlarge hmass
  exact L.impossible hue htrans f (Ne.symm hf)

end DirectionalTransience

end

end OAI
