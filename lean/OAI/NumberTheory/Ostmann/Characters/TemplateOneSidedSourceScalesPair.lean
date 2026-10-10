import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSourceScalesShells

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSourceScales
open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate Template
open DiagonalEstimate HigherBiasSourceWord Template.OneSidedPhase InitialCharacterScale
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀}
    (w : FixedConfigurationWitness s c BD)

theorem source_edge_log_bounds (j : ℕ) (hj : j≤k)
    (P R : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)))
    (hshape : ∃z : Word k j × Fin (wordSize k L), ∃a : Fin j, ∃b : Bool,
      (P=.inl (copiedBulk w.configuration (wordSize k L) j z) ∧
        R=.inr (copiedRetiredOutside w.configuration (wordSize k L) j hj false a b)) ∨
      (P=.inr (copiedRetiredOutside w.configuration (wordSize k L) j hj true a b) ∧
        R=.inl (copiedBulk w.configuration (wordSize k L) j z))) :
    ∃big : Bool,
      (∀p∈sourceSurvivorShells w j R,Real.log p.val ≤ Real.exp (shortUpper s.locations big)) ∧
      (∀p∈sourceSurvivorShells w j P,Real.exp (longLower s.locations big) ≤ Real.log p.val) := by
  obtain ⟨z,a,b,h | h⟩ := hshape
  · obtain ⟨rfl,rfl⟩ := h
    refine ⟨false,?_,?_⟩
    · intro p hp
      exact (sourceSurvivorShells_retired_log_bounds w j hj false a b p hp).2
    · intro p hp
      rw [sourceSurvivorShells_bulk] at hp
      exact (boundedInterval_log_bounds s.locations.primes s.locations.B
        (s.locations.B+s.locations.w) p hp).1.le
  · obtain ⟨rfl,rfl⟩ := h
    refine ⟨true,?_,?_⟩
    · intro p hp
      rw [sourceSurvivorShells_bulk] at hp
      exact (boundedInterval_log_bounds s.locations.primes s.locations.B
        (s.locations.B+s.locations.w) p hp).2
    · intro p hp
      exact (sourceSurvivorShells_retired_log_bounds w j hj true a b p hp).1

theorem source_edge_grid (hα : 0<α) (hγ : 0<γ) (hL : 0<L)
    (hband : ∀p∈E,α*L≤Real.log (Real.log p) ∧ Real.log (Real.log p)≤β*L)
    (j : ℕ) (hj : j≤k)
    (P R : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)))
    (hshape : ∃z : Word k j × Fin (wordSize k L), ∃a : Fin j, ∃b : Bool,
      (P=.inl (copiedBulk w.configuration (wordSize k L) j z) ∧
        R=.inr (copiedRetiredOutside w.configuration (wordSize k L) j hj false a b)) ∨
      (P=.inr (copiedRetiredOutside w.configuration (wordSize k L) j hj true a b) ∧
        R=.inl (copiedBulk w.configuration (wordSize k L) j z))) :
    ∃n : Fin (scaleCount β γ),0<n.val ∧
      0<lowerExponent α γ ∧ lowerExponent α γ ≤ shortExponent γ n.val ∧
      shortExponent γ n.val<longExponent γ n.val ∧
      (∀p∈sourceSurvivorShells w j R,
        Real.exp (lowerExponent α γ*L)≤Real.log p.val ∧
          Real.log p.val≤Real.exp (shortExponent γ n.val*L)) ∧
      (∀p∈sourceSurvivorShells w j P,
        Real.exp ((longExponent γ n.val+scaleStep γ)*L)≤Real.log p.val ∧
          Real.log p.val≤Real.exp (β*L)) := by
  obtain ⟨big,hshort,hlong⟩ := source_edge_log_bounds w j hj P R hshape
  obtain ⟨n,hn,hns,hnl⟩ := actual_location_grid s.locations hγ hL big
  have he := scale_exponents hα hγ hn
  refine ⟨n,hn,he.1,he.2.1,he.2.2,?_,?_⟩
  · intro p hp
    constructor
    · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (min_le_left _ _) hL.le)).trans
        (sourceSurvivorShells_log_bounds w hband j R p hp).1
    · exact (hshort p hp).trans (Real.exp_le_exp.mpr hns)
  · intro p hp
    exact ⟨(Real.exp_le_exp.mpr hnl).trans (hlong p hp),
      (sourceSurvivorShells_log_bounds w hband j P p hp).2⟩

theorem source_edge_coprime (hγ : 0<γ) (hL : 0<L) (j : ℕ) (hj : j≤k)
    (P R : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)))
    (hshape : ∃z : Word k j × Fin (wordSize k L), ∃a : Fin j, ∃b : Bool,
      (P=.inl (copiedBulk w.configuration (wordSize k L) j z) ∧
        R=.inr (copiedRetiredOutside w.configuration (wordSize k L) j hj false a b)) ∨
      (P=.inr (copiedRetiredOutside w.configuration (wordSize k L) j hj true a b) ∧
        R=.inl (copiedBulk w.configuration (wordSize k L) j z))) :
    ∀p∈sourceSurvivorShells w j P,∀q∈sourceSurvivorShells w j R,p.val.Coprime q.val := by
  obtain ⟨big,hshort,hlong⟩ := source_edge_log_bounds w j hj P R hshape
  have hg := (actual_location_gap s.locations hγ hL big).2.2
  have hsep : shortUpper s.locations big<longLower s.locations big := by
    linarith [mul_pos hγ hL]
  intro p hp q hq
  apply (primeUpTo_prime p).coprime_iff_not_dvd.mpr
  intro hdiv
  have heq : p.val=q.val := ((primeUpTo_prime q).eq_one_or_self_of_dvd p.val hdiv).resolve_left
    (primeUpTo_prime p).ne_one
  have hs := (hshort q hq).trans_lt (Real.exp_lt_exp.mpr hsep)
  have hl := hlong p hp
  rw [heq] at hl
  exact (not_lt_of_ge hl) hs

end
end Ostmann.Characters.TemplateOneSidedSourceScales

end

end OAI
