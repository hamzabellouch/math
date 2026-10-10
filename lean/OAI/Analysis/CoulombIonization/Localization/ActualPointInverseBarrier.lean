import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BandInverseNumericsBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped Topology

namespace CoulombAtom
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget

lemma measureReal_remove_cutoff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {A : Set Ω} {g : Ω → ℝ} {Q p : ℝ}
    (hA : μ.real {z | z ∈ A ∧ g z ≤ Q} < p)
    (hQ : μ.real {z | Q < g z} < p) : μ.real A < 2*p := by
  have hm : A ⊆ {z | z ∈ A ∧ g z ≤ Q} ∪ {z | Q < g z} := by
    intro z hz
    by_cases h : g z ≤ Q
    · exact Or.inl ⟨hz,h⟩
    · exact Or.inr (lt_of_not_ge h)
  exact (measureReal_mono hm).trans_lt
    ((measureReal_union_le _ _).trans_lt (by linarith only [hA,hQ]))

 def originalQueryDensity {N K : ℕ} (F : fermionGraph N)
    (r : ℝ) (j : ℕ) (c₁ r₀ s : ℝ)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) (y : Space) : ℝ :=
  jointMasterPosterior (graphRawLaw F) (fun k : Fin K => dyadicObservationWidth r k)
    j c₁ r₀ s canonicalRealPacket
    (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j z) y

 def originalQueryField {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) (c₁ r₀ s : ℝ)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) (y : Space) : ℝ :=
  Z/‖y‖-lam-tfPotential (originalQueryDensity F r j c₁ r₀ s z) y

 theorem TailTiltState.point_inverse_events {Z lam r : ℝ} (hZ : 0 ≤ Z)
    (hlam : 0 < lam) (hr : 0 < r) {N K : ℕ} {F : fermionGraph N}
    {p₀ : Fin (K+1) → ℝ} {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j)
    (hstate : TailTiltState Z lam r K p₀ δ F)
    {c₁ r₀ s h xi : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (hxi : 0 < xi) (hxih : xi < 2*h)
    (j : Fin (K+1)) (k : Fin K) (hk : j.val ≤ k.val)
    {y : Space} (hy : y ≠ 0) (hry : r₀ ≤ ‖y‖)
    (hgeom : InverseFiniteGeometry c₁ r₀ s (dyadicObservationWidth r k) y)
    (hlow : LowInverseNumerics c₁ r₀ s (dyadicObservationWidth r k)
      (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) h xi quantumInverseCountConstant y)
    (hhigh : HighInverseNumerics c₁ r₀ s (dyadicObservationWidth r k)
      (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) h xi quantumInverseCountConstant y)
    (hcount : universalCellCountConstant*
      (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)^2 <
      (quantumInverseCountConstant/(localCellRadius y)^3)^2) :
    (physicalObservationLaw (graphRawLaw F) K).real
      {z | (h+xi)/(localCellRadius y)^4 ≤ originalQueryField F Z lam r j c₁ r₀ s z y ∧
        originalQueryDensity F r j c₁ r₀ s z y ≤ localTFResponse h/(localCellRadius y)^6} < 2*p₀ j ∧
    (physicalObservationLaw (graphRawLaw F) K).real
      {z | originalQueryField F Z lam r j c₁ r₀ s z y ≤ (h-xi)/(localCellRadius y)^4 ∧
        localTFResponse h/(localCellRadius y)^6 ≤ originalQueryDensity F r j c₁ r₀ s z y} < 2*p₀ j := by
  have ha := localCellRadius_pos hy
  have hw := masterWidth_pos hc hr₀ hs y
  have hHlo : 0 ≤ (h+xi/2)/(localCellRadius y)^4 := div_nonneg (by linarith) (by positivity)
  have hHhi : 0 ≤ (h-xi/2)/(localCellRadius y)^4 := div_nonneg (by linarith) (by positivity)
  have heta : 0 < (localCellRadius y)^(-7+(1/100:ℝ)) := Real.rpow_pos_of_pos ha _
  have hm : 0 < (localCellRadius y)^(-3+(1/100:ℝ)) := Real.rpow_pos_of_pos ha _
  have hlo := hstate.low_inverse_event hZ hlam hr h₀ hc hcL hr₀ hs hs1 j k hk hy
    hgeom.radius_le hry hgeom.cut_pos hgeom.cut_le hgeom.probe_pos hgeom.probe_fit
    hgeom.probe_margin hgeom.collar (by linarith [hgeom.master_fit]) hHlo heta
    (fun t ht => (hlow t ht).1) (fun t ht => (hlow t ht).2)
  have hhi := hstate.high_inverse_event hZ hlam hr h₀ hc hcL hr₀ hs hs1 j k hk hy
    hgeom.radius_le hry hgeom.cut_pos hgeom.cut_le hgeom.probe_pos hgeom.probe_fit
    hgeom.probe_margin hgeom.collar hgeom.master_fit hHhi heta hm
    (fun t ht => (hhigh t ht).1) (fun t ht => (hhigh t ht).2.1) (fun t ht => (hhigh t ht).2.2)
  have hcnt := hstate.local_count_failure hZ hlam hr j k hk hy
    (2*masterWidth c₁ r₀ s y+Real.sqrt 3*((localCellRadius y)^(6/5:ℝ)+dyadicObservationWidth r k))
    (quantumInverseCountConstant/(localCellRadius y)^3)
    (div_nonneg quantumInverseCountConstant_pos.le (by positivity))
    (by linarith only [hgeom.count_fit]) hcount
  constructor
  · apply measureReal_remove_cutoff (physicalObservationLaw (graphRawLaw F) K) (hQ := hcnt)
    unfold originalQueryField originalQueryDensity
    simpa only [mem_ofPred_eq,and_assoc,Measure.real] using hlo
  · apply measureReal_remove_cutoff (physicalObservationLaw (graphRawLaw F) K) (hQ := hcnt)
    unfold originalQueryField originalQueryDensity
    simpa only [mem_ofPred_eq,and_assoc,Measure.real] using hhi

end CoulombAtom

end

end OAI
