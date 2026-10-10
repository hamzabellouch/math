import OAI.GroupTheory.PolycyclicRecognition.Geometry.RootIntervalSupports

namespace OAI

/-! # Conjugated interval laws used by second-sheet source switches -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Metric

variable {L N I : Type*} [AddCommGroup L] [Module ℝ L] [Group N]
  [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N] [T2Space N]

def coupledRootIntervalSample (Exp : L → N) {m : ℕ} (letters : Fin m → I)
    (X : I → L) (s : I → ℝ) (r : ℝ) (k : ℕ → N) (j : ℕ) (t : ℝ) : N :=
  k j * rootIntervalSample Exp letters X s r j t * (k j)⁻¹

def coupledRootIntervalLaw (Exp : L → N) {m : ℕ} (letters : Fin m → I)
    (X : I → L) (s : I → ℝ) (r ρ : ℝ) (k : ℕ → N) (j : ℕ) : Measure N :=
  Measure.map (coupledRootIntervalSample Exp letters X s r k j) (uniformIntervalLaw ρ)

omit [MeasurableSpace N] [BorelSpace N] [T2Space N] in
theorem continuous_coupledRootIntervalSample (Exp : L → N)
    (hc : ∀ v : L, Continuous (fun t : ℝ => Exp (t • v)))
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ)
    (r : ℝ) (k : ℕ → N) (j : ℕ) :
    Continuous (coupledRootIntervalSample Exp letters X s r k j) :=
  (continuous_const.mul (hc _)).mul continuous_const

omit [T2Space N] in
theorem measurePreserving_coupledRootIntervalSample (Exp : L → N)
    (hc : ∀ v : L, Continuous (fun t : ℝ => Exp (t • v)))
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ)
    (r ρ : ℝ) (k : ℕ → N) (j : ℕ) :
    MeasurePreserving (coupledRootIntervalSample Exp letters X s r k j)
      (uniformIntervalLaw ρ) (coupledRootIntervalLaw Exp letters X s r ρ k j) :=
  ⟨(continuous_coupledRootIntervalSample Exp hc letters X s r k j).measurable, rfl⟩

omit [TopologicalSpace N] [IsTopologicalGroup N] [BorelSpace N] [T2Space N] in
theorem coupledRootIntervalLaw_isProbability (Exp : L → N)
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ)
    (r : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ → N) (j : ℕ) :
    IsProbabilityMeasure (coupledRootIntervalLaw Exp letters X s r ρ k j) := by
  let := uniformIntervalLaw_isProbability hρ
  unfold coupledRootIntervalLaw
  infer_instance

theorem coupledRootIntervalLaw_ae_mem_support (Exp : L → N)
    (hc : ∀ v : L, Continuous (fun t : ℝ => Exp (t • v)))
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ)
    (r ρ : ℝ) (k : ℕ → N) (j : ℕ) :
    ∀ᵐ u ∂coupledRootIntervalLaw Exp letters X s r ρ k j,
      u ∈ (fun v => k j * v * (k j)⁻¹) '' rootIntervalSupport Exp letters X s r ρ j := by
  have hcompact : IsCompact ((fun v => k j * v * (k j)⁻¹) ''
      rootIntervalSupport Exp letters X s r ρ j) :=
    (isCompact_rootIntervalSupport Exp hc letters X s r ρ j).image
    ((continuous_const.mul continuous_id).mul continuous_const)
  apply (ae_map_iff (continuous_coupledRootIntervalSample Exp hc letters X s r k j).measurable.aemeasurable
    hcompact.measurableSet).mpr
  exact (ProbabilityTheory.ae_cond_mem measurableSet_closedBall).mono
    (fun t ht => ⟨rootIntervalSample Exp letters X s r j t, ⟨t, ht, rfl⟩, rfl⟩)

omit [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N] [T2Space N] in
theorem coupledRootIntervalSample_sub (Exp : L → N)
    (hneg : ∀ v, Exp (-v) = (Exp v)⁻¹)
    (hadd : ∀ (v : L) (u t : ℝ), Exp ((u + t) • v) = Exp (u • v) * Exp (t • v))
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ)
    (r : ℝ) (k : ℕ → N) (j : ℕ) (u t : ℝ) :
    coupledRootIntervalSample Exp letters X s r k j u *
      (coupledRootIntervalSample Exp letters X s r k j t)⁻¹ =
        coupledRootIntervalSample Exp letters X s r k j (u - t) := by
  have he := rootIntervalSample_sub Exp hneg hadd letters X s r j u t
  dsimp only [coupledRootIntervalSample]
  rw [← he]
  group

end PolycyclicRecognition

end

end OAI
