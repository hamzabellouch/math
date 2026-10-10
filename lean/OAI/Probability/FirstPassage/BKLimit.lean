import OAI.Probability.FirstPassage.BKPathMeasurability

namespace OAI

namespace PlanarFPP
open MeasureTheory Filter Set
open scoped ENNReal

theorem strict_disjoint_measure_le_of_rounded {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (τ : Edge → Ω → ℝ) (S : Finset Edge)
    (Fs : List (Set StrictPathWitness)) (C : ℝ≥0∞)
    (hbound : ∀ t, P {ω | RoundedDisjointPaths S Fs t (fun e => τ e ω)} ≤ C) :
    P {ω | StrictDisjointPaths S Fs (fun e => τ e ω)} ≤ C := by
  let E : ℕ → Set Ω := fun N => ⋂ t ≥ N, {ω | RoundedDisjointPaths S Fs t (fun e => τ e ω)}
  have he : {ω | StrictDisjointPaths S Fs (fun e => τ e ω)} = ⋃ N, E N := by
    ext ω
    simp only [mem_ofPred_eq,mem_iUnion,mem_iInter,E]
    rw [strict_disjoint_eventual_rounded_iff,eventually_atTop]
  have hmono : Monotone E := by
    intro N M hNM ω hω
    simp only [E,mem_iInter] at hω ⊢
    exact fun t ht => hω t (hNM.trans ht)
  have hE : ∀ N, P (E N) ≤ C := by
    intro N
    apply (measure_mono ?_).trans (hbound N)
    intro ω hω
    exact mem_iInter.mp (mem_iInter.mp hω N) le_rfl
  rw [he,hmono.measure_iUnion]
  exact iSup_le hE

end PlanarFPP

end OAI
