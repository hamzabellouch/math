import Mathlib
import OAI.Probability.Ballisticity.Stationary.ArrayProfileConsistency
import OAI.Probability.Ballisticity.Estimates.SurvivalLimit
import OAI.Probability.Ballisticity.Walk.ArrayCostGrowth
import OAI.Probability.Ballisticity.Estimates.AllIndexMarks
import OAI.Probability.Ballisticity.Stationary.BadFiniteArray
import OAI.Probability.Ballisticity.Stationary.BadArrayElliptic

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

structure StationaryArrayLaw {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν] (e : Direction d) where
  law : ProbabilityMeasure (ActualEpisodeArray e)
  preserving : MeasurePreserving StationaryCompact.shift (law : Measure (ActualEpisodeArray e)) (law : Measure (ActualEpisodeArray e))
  symmetric : ∀ σ, MeasurePreserving (arrayPerm e σ) (law : Measure (ActualEpisodeArray e)) (law : Measure (ActualEpisodeArray e))
  consistent : ∀ᵐ Y ∂(law : Measure (ActualEpisodeArray e)), ArrayOffsetsConsistent e Y ∧ ArrayProfilesConsistent e Y
  sampling : ∀ᵐ Y ∂(law : Measure (ActualEpisodeArray e)), ∀ p j z,
    Tendsto (fun n => arraySamplingError e p j z (2^n) Y) atTop (𝓝 0)
  zero_sampling : ∀ᵐ Y ∂(law : Measure (ActualEpisodeArray e)), ∀ p q z, p≠q →
    arrayProfileTest e q.1 p z Y=0 → arrayOffsetTest e p q z Y=0
  finite_marks : ∀ᵐ Y ∂(law : Measure (ActualEpisodeArray e)), ∀ i,
    0<(Y.1 i).1 ∧ (Y.1 i).1<⊤ ∧ (Y.1 i).2.1<⊤ ∧ (Y.1 i).2.2<⊤
  integrable_cost : Integrable (arrayRealCost e) (law : Measure (ActualEpisodeArray e))
  positive_cost : 0<∫ Y, arrayRealCost e Y ∂(law : Measure (ActualEpisodeArray e))
  integrable_logheight : Integrable (fun Y => Real.log (1+((Y.1 0).1.toNat:ℝ))) (law : Measure (ActualEpisodeArray e))
  continuation : ∀ᵐ Y ∂(law : Measure (ActualEpisodeArray e)), ArrayContinuation e Y
  survival : ∀ᵐ Y ∂(law : Measure (ActualEpisodeArray e)), ArrayAveragedSurvival e Y
  κ : ℝ≥0
  κ_pos : 0<κ
  elliptic : ∀ᵐ Y ∂(law : Measure (ActualEpisodeArray e)), ArrayElliptic e κ Y
  entropyConstant : ℝ
  entropy : ∀ i m, let W:=(law : Measure (ActualEpisodeArray e)).map (typedCurrentArrayWindow e i m)
    klDiv W (W.fst.compProd (currentWindowReference e ν))≤ENNReal.ofReal ((m:ℝ)*entropyConstant)

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}
lemma entropy_finite (L : StationaryArrayLaw ν e) (i : ℤ) (m : ℕ) :
    let W:=(L.law : Measure (ActualEpisodeArray e)).map (typedCurrentArrayWindow e i m)
    klDiv W (W.fst.compProd (currentWindowReference e ν))≠⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (L.entropy i m)
end StationaryArrayLaw

namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e f : Direction d} {D : ℝ}

theorem bad_stationary_array_law (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop)
    (hN : ∀ n, C.sfloor≤(Ns n:ℝ)) (hlarge : ∀ n, 32*C.b≤(1/2:ℝ)*Real.log (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D)≤(environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2))) :
    Nonempty (StationaryArrayLaw ν e) := by
  obtain ⟨ρ,φ,hφ,hlim,hstat,hsample,hzero,hmarks,hJ,hh,hc,hcp⟩ := C.bad_array_finite_marks hef hD Ns hNs hN hlarge hmass
  let Ns' := fun n => Ns (φ n)
  have hN' := fun n => hN (φ n)
  have hlarge' := fun n => hlarge (φ n)
  have hmass' := fun n => hmass (φ n)
  exact ⟨{
    law := ρ
    preserving := hstat
    symmetric := C.bad_limit_perm hef Ns' hN' hmass' ρ hlim
    consistent := C.bad_limit_consistent hef Ns' hN' hmass' ρ hlim
    sampling := hsample
    zero_sampling := hzero
    finite_marks := stationary_finite_marks_all e _ hstat hmarks
    integrable_cost := hc
    positive_cost := C.hb.trans_le hcp
    integrable_logheight := hh
    continuation := C.bad_limit_continuation hef Ns' hN' hmass' ρ hlim
    survival := C.bad_limit_averaged_survival hef Ns' hN' hmass' ρ hlim
    κ := C.κ
    κ_pos := C.hκ0
    elliptic := C.bad_limit_elliptic hef Ns' hN' hmass' ρ hlim
    entropyConstant := C.windowEntropyConstant
    entropy := C.stationary_window_entropy hef hD Ns' hN' hlarge' hmass' ρ hlim hstat
  }⟩

end OperationalConstants
end DirectionalTransience

end

end OAI
