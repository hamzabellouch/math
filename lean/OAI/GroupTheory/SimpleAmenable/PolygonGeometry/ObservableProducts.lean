import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ObservableDistance

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ObservableProducts
open Classical MeasureTheory Set

theorem ObservableClose.refl {X : Type*} [MeasurableSpace X] (μ : Measure X) :
    ObservableClose μ μ 0 := by
  intro f hf hb
  simp

theorem ObservableClose.trans {X : Type*} [MeasurableSpace X]
    {μ ν ρ : Measure X} {ε δ : ℝ} (h : ObservableClose μ ν ε) (k : ObservableClose ν ρ δ) :
    ObservableClose μ ρ (ε+δ) := by
  intro f hf hb
  exact (abs_sub_le _ _ _).trans (add_le_add (h f hf hb) (k f hf hb))

theorem ObservableClose.prod_left {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ρ : Measure X) [IsProbabilityMeasure ρ] {ε : ℝ} (h : ObservableClose μ ν ε) :
    ObservableClose (ρ.prod μ) (ρ.prod ν) ε := by
  have hh := (h.prod_right ρ).map measurable_swap
  simpa only [Measure.prod_swap] using hh

theorem ObservableClose.prod {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ρ σ : Measure Y} [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ]
    {ε δ : ℝ} (h : ObservableClose μ ν ε) (k : ObservableClose ρ σ δ) :
    ObservableClose (μ.prod ρ) (ν.prod σ) (ε+δ) :=
  (h.prod_right ρ).trans (k.prod_left ν)

theorem ObservableClose.fin_pi (n : ℕ) {X : Fin n → Type*} [∀i,MeasurableSpace (X i)]
    (μ ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (ε : Fin n → ℝ) (h : ∀i,ObservableClose (μ i) (ν i) (ε i)) :
    ObservableClose (Measure.pi μ) (Measure.pi ν) (∑i,ε i) := by
  induction n with
  | zero =>
    have he : μ=ν := by funext i; exact Fin.elim0 i
    subst ν
    simpa using ObservableClose.refl (Measure.pi μ)
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove X (0 : Fin (n+1))
    have hμ := (measurePreserving_piFinSuccAbove μ (0 : Fin (n+1))).symm.map_eq
    have hν := (measurePreserving_piFinSuccAbove ν (0 : Fin (n+1))).symm.map_eq
    have hi := ih (fun i => μ ((0 : Fin (n+1)).succAbove i))
      (fun i => ν ((0 : Fin (n+1)).succAbove i))
      (fun i => ε ((0 : Fin (n+1)).succAbove i)) (fun i => h _)
    have hh := ((h 0).prod hi).map e.symm.measurable
    rw [hμ,hν] at hh
    simpa only [Fin.succAbove_zero,Fin.sum_univ_succ] using hh

end ObservableProducts

end SimpleAmenable
end
end

end OAI
