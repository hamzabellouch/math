import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace Problem336.Observation

theorem gaussianPDFReal_binary_shift (t : ℝ≥0) (ht : t ≠ 0)
    (x y : ℝ) (hx : x = 0 ∨ x = 1) :
    gaussianPDFReal ((t : ℝ) * x) t y =
      gaussianPDFReal 0 t y * Real.exp ((y - (t : ℝ) / 2) * x) := by
  rcases hx with rfl | rfl
  · simp
  · have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
    simp only [mul_one, gaussianPDFReal, sub_zero]
    simp only [mul_assoc]
    rw [← Real.exp_add]
    congr 2
    field_simp
    ring

theorem gaussianPDFReal_binary_shift_prod {I : Type*} (s : Finset I)
    (t : ℝ≥0) (ht : t ≠ 0) (x y : I → ℝ)
    (hx : ∀ i ∈ s, x i = 0 ∨ x i = 1) :
    (∏ i ∈ s, gaussianPDFReal ((t : ℝ) * x i) t (y i)) =
      (∏ i ∈ s, gaussianPDFReal 0 t (y i)) *
        Real.exp (∑ i ∈ s, (y i - (t : ℝ) / 2) * x i) := by
  calc
    _ = ∏ i ∈ s, gaussianPDFReal 0 t (y i) *
        Real.exp ((y i - (t : ℝ) / 2) * x i) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact gaussianPDFReal_binary_shift t ht (x i) (y i) (hx i hi)
    _ = _ := by rw [Finset.prod_mul_distrib, Real.exp_sum]

def finiteObservationFiltration {Ω I : Type*} {mΩ : MeasurableSpace Ω}
    (coordinate : I → MeasurableSpace Ω) (hcoordinate : ∀ i, coordinate i ≤ mΩ)
    (S : ℕ → Finset I) (hS : Monotone S) : Filtration ℕ mΩ where
  seq n := ⨆ i ∈ S n, coordinate i
  mono' := by
    intro n m hnm
    exact iSup_le fun i => iSup_le fun hi =>
      le_iSup_of_le i (le_iSup_of_le (hS hnm hi) le_rfl)
  le' n := iSup_le fun i => iSup_le fun _ => hcoordinate i

theorem iSup_finiteObservationFiltration {Ω I : Type*} {mΩ : MeasurableSpace Ω}
    (coordinate : I → MeasurableSpace Ω) (hcoordinate : ∀ i, coordinate i ≤ mΩ)
    (S : ℕ → Finset I) (hS : Monotone S) (hcover : ∀ i, ∃ n, i ∈ S n) :
    (⨆ n, finiteObservationFiltration coordinate hcoordinate S hS n) =
      ⨆ i, coordinate i := by
  apply le_antisymm
  · exact iSup_le fun _ => iSup_le fun i => iSup_le fun _ => le_iSup coordinate i
  · refine iSup_le fun i => ?_
    obtain ⟨n, hi⟩ := hcover i
    exact le_iSup_of_le n (le_iSup_of_le i (le_iSup_of_le hi le_rfl))

theorem tendsto_posterior_of_finite_stage
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsFiniteMeasure P] (F : Filtration ℕ mΩ) (X : Ω → ℝ)
    (posterior : ℕ → Ω → ℝ)
    (hposterior : ∀ n, posterior n =ᵐ[P] P[X | F n]) :
    ∀ᵐ ω ∂P, Tendsto (fun n => posterior n ω) atTop
      (nhds ((P[X | ⨆ n, F n]) ω)) := by
  have hall : ∀ᵐ ω ∂P, ∀ n, posterior n ω = (P[X | F n]) ω :=
    ae_all_iff.mpr hposterior
  filter_upwards [hall, MeasureTheory.tendsto_ae_condExp (μ := P) (ℱ := F) X]
    with ω hω hlim
  exact hlim.congr (fun n => (hω n).symm)

theorem limsup_posterior_of_finite_stage
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsFiniteMeasure P] (F : Filtration ℕ mΩ) (X : Ω → ℝ)
    (posterior : ℕ → Ω → ℝ)
    (hposterior : ∀ n, posterior n =ᵐ[P] P[X | F n]) :
    (fun ω => limsup (fun n => posterior n ω) atTop) =ᵐ[P]
      P[X | ⨆ n, F n] := by
  filter_upwards [tendsto_posterior_of_finite_stage P F X posterior hposterior]
    with ω hω
  exact hω.limsup_eq

theorem limsup_posterior_all_coordinates
    {Ω I : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsFiniteMeasure P] (coordinate : I → MeasurableSpace Ω)
    (hcoordinate : ∀ i, coordinate i ≤ mΩ)
    (S : ℕ → Finset I) (hS : Monotone S) (hcover : ∀ i, ∃ n, i ∈ S n)
    (X : Ω → ℝ) (posterior : ℕ → Ω → ℝ)
    (hposterior : ∀ n, posterior n =ᵐ[P] P[X | ⨆ i ∈ S n, coordinate i]) :
    (fun ω => limsup (fun n => posterior n ω) atTop) =ᵐ[P]
      P[X | ⨆ i, coordinate i] := by
  have h := limsup_posterior_of_finite_stage P
    (finiteObservationFiltration coordinate hcoordinate S hS) X posterior hposterior
  simpa only [iSup_finiteObservationFiltration coordinate hcoordinate S hS hcover] using h

end Problem336.Observation

end

end OAI
