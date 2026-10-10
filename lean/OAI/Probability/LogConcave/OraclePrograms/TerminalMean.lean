import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.Program

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace LogConcaveSampling.SeedCompiler
open OracleCompiler
open OracleCompiler.Program

def terminalMean (d : ℕ) (r σ : ℝ) :
    Program (Point d × (Fin 2 → Point d)) d 1 (Point d) :=
  oneQuery (fun p => p.1 + r • p.2 0) (by fun_prop)
    (fun p => p.2.2 + σ • p.1.2 1) (by fun_prop)

def terminalSample (d : ℕ) (r η : ℝ) :
    Program (Point d × (Fin 3 → Point d)) d 1 (Point d) :=
  oneQuery (fun p => p.1 + r • p.2 0) (by fun_prop)
    (fun p => p.1.2 0 - r • p.2.2 + (Real.sqrt 3 * η / 2) • p.1.2 1 +
      (η / 2) • p.1.2 2) (by fun_prop)

lemma terminalMean_run {d : ℕ} (r σ : ℝ) (V : Point d → ℝ)
    (x : Point d) (g : Fin 2 → Point d) :
    (terminalMean d r σ).run V (x,g) = gradient V (x+r • g 0) + σ • g 1 := by
  rw [terminalMean, oneQuery_run]
  rfl

lemma terminalSample_run {d : ℕ} (r η : ℝ) (V : Point d → ℝ)
    (x : Point d) (g : Fin 3 → Point d) :
    (terminalSample d r η).run V (x,g) = g 0 - r • gradient V (x+r • g 0) +
      (Real.sqrt 3 * η / 2) • g 1 + (η / 2) • g 2 := by
  rw [terminalSample, oneQuery_run]
  rfl

def terminalShift (n : ℕ) : Fin (n+1) → ℝ := fun i => if i = 0 then -1 else 0

lemma terminalShift_energy (n : ℕ) : (∑ i, terminalShift n i ^ 2) = 1 := by
  simp [terminalShift]

lemma terminalQuery_invariant {d n : ℕ} (x Δ : Point d) (r : ℝ)
    (g : Fin (n+1) → Point d) :
    (x + r • Δ) + r • (g 0 + terminalShift n 0 • Δ) = x+r • g 0 := by
  simp only [terminalShift, ite_true, neg_smul, one_smul]
  module

lemma terminalMean_shift {d : ℕ} (r σ : ℝ) (V : Point d → ℝ) :
    ShiftInvariant r (terminalShift 1) (fun x g => (terminalMean d r σ).run V (x,g)) := by
  intro x Δ g
  simp only [terminalMean_run, terminalQuery_invariant]
  simp [terminalShift]

lemma terminalSample_shift {d : ℕ} (r η : ℝ) (V : Point d → ℝ)
    (x Δ : Point d) (g : Fin 3 → Point d) :
    (terminalSample d r η).run V (x+r • Δ, fun i => g i + terminalShift 2 i • Δ) =
      (terminalSample d r η).run V (x,g) - Δ := by
  simp only [terminalSample_run, terminalQuery_invariant]
  simp only [terminalShift, Fin.reduceEq, ite_true, ite_false,
    neg_smul, one_smul, zero_smul, add_zero]
  module

lemma terminalMean_history_shift {d : ℕ} (r σ : ℝ) (V : Point d → ℝ)
    (x Δ : Point d) (g : Fin 2 → Point d) :
    (terminalMean d r σ).history V (x+r • Δ,fun i => g i+terminalShift 1 i • Δ) 1 =
      (terminalMean d r σ).history V (x,g) 1 := by
  simp only [Program.history, terminalMean, oneQuery, Nat.lt_add_one, dite_eq_left,
    terminalQuery_invariant]

lemma terminalSample_history_shift {d : ℕ} (r η : ℝ) (V : Point d → ℝ)
    (x Δ : Point d) (g : Fin 3 → Point d) :
    (terminalSample d r η).history V (x+r • Δ,fun i => g i+terminalShift 2 i • Δ) 1 =
      (terminalSample d r η).history V (x,g) 1 := by
  simp only [Program.history, terminalSample, oneQuery, Nat.lt_add_one, dite_eq_left,
    terminalQuery_invariant]

end LogConcaveSampling.SeedCompiler

end
end

end

section

noncomputable section
namespace LogConcaveSampling.SeedCompiler
open MeasureTheory ProbabilityTheory Function
open scoped BigOperators

variable {Ω A ι E : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem restored_from_joint_law (κ : Measure Ω) [SFinite κ] (μ : Measure A) [SFinite μ]
    (anchor : Ω → A) (noise : Ω → E) (ha : Measurable anchor) (hz : Measurable noise)
    (hlaw : κ.map (fun w => (anchor w,noise w))=μ.prod (stdGaussian E))
    (a : ι → ℝ) (ha2 : (∑i,a i^2)≤1) :
    (κ.prod (Measure.pi fun _ : ι => stdGaussian E)).map
      (fun z => (anchor z.1,restored (sqrtCoefficient a) a (z.2,noise z.1)))=
        μ.prod (Measure.pi fun _ : ι => stdGaussian E) := by
  let γ : Measure (ι → E) := Measure.pi fun _ => stdGaussian E
  have hAZ : MeasurePreserving (fun w => (anchor w,noise w)) κ (μ.prod (stdGaussian E)) :=
    ⟨ha.prodMk hz,hlaw⟩
  have hp := hAZ.prod (MeasurePreserving.id γ)
  have hs := (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ:=stdGaussian E) (ν:=γ))
  have ht := hs.comp ((measurePreserving_prodAssoc μ (stdGaussian E) γ).comp hp)
  have hr : MeasurePreserving (Prod.map id (restored (sqrtCoefficient a) a))
      (μ.prod (γ.prod (stdGaussian E))) (μ.prod γ) :=
    ⟨by fun_prop,restored_with_anchors μ a ha2⟩
  exact (hr.comp ht).map_eq

theorem restored_error_integral (κ : Measure Ω) [SFinite κ] (μ : Measure A) [SFinite μ]
    (anchor : Ω → A) (noise : Ω → E) (ha : Measurable anchor) (hz : Measurable noise)
    (hlaw : κ.map (fun w => (anchor w,noise w))=μ.prod (stdGaussian E))
    (a : ι → ℝ) (ha2 : (∑i,a i^2)≤1) (f : A × (ι → E) → ℝ)
    (hf : Integrable f (μ.prod (Measure.pi fun _ : ι => stdGaussian E))) :
    Integrable (fun z : Ω × (ι → E) =>
      f (anchor z.1,restored (sqrtCoefficient a) a (z.2,noise z.1)))
      (κ.prod (Measure.pi fun _ : ι => stdGaussian E)) ∧
    (∫z : Ω × (ι → E),f (anchor z.1,restored (sqrtCoefficient a) a (z.2,noise z.1))
      ∂κ.prod (Measure.pi fun _ : ι => stdGaussian E))=
        ∫z,f z ∂μ.prod (Measure.pi fun _ : ι => stdGaussian E) := by
  let T : Ω × (ι → E) → A × (ι → E) := fun z =>
    (anchor z.1,restored (sqrtCoefficient a) a (z.2,noise z.1))
  have hm : Measurable T := (ha.comp measurable_fst).prodMk ((restored (sqrtCoefficient a) a).measurable.comp
    (measurable_snd.prodMk (hz.comp measurable_fst)))
  have he : (κ.prod (Measure.pi fun _ : ι => stdGaussian E)).map T=
      μ.prod (Measure.pi fun _ : ι => stdGaussian E) :=
    restored_from_joint_law κ μ anchor noise ha hz hlaw a ha2
  have hi : Integrable f ((κ.prod (Measure.pi fun _ : ι => stdGaussian E)).map T) := he ▸ hf
  exact ⟨hi.comp_measurable hm,(integral_map hm.aemeasurable hi.aestronglyMeasurable).symm.trans
    (by rw [he])⟩
end LogConcaveSampling.SeedCompiler

end

end

end

end OAI
