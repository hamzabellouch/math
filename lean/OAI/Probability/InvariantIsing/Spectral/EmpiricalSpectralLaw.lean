import OAI.Probability.InvariantIsing.Spectral.FiniteSpectralMeasure
import Mathlib.MeasureTheory.Measure.Portmanteau

namespace OAI

/-! The empirical spectral probability measure and its finite-set masses. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology Classical

namespace InvariantIsing

lemma empiricalSpectralWeight_sum {N : ℕ} (hN : 0 < N) :
    ∑ _i : Fin N, (1 : ℝ)/N=1 := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

def empiricalSpectralLaw {N : ℕ} (hN : 0 < N) (eig : Fin N → ℝ) : ProbabilityMeasure ℝ :=
  ⟨finiteSpectralMeasure (fun _ => (1 : ℝ)/N) eig,
    finiteSpectralMeasure_probability _ _ (fun _ => by positivity) (empiricalSpectralWeight_sum hN)⟩

lemma empiricalSpectralLaw_integral {N : ℕ} (hN : 0 < N) (eig : Fin N → ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂(empiricalSpectralLaw hN eig : Measure ℝ))=(1 : ℝ)/N*∑ i, f (eig i) := by
  change (∫ x, f x ∂finiteSpectralMeasure (fun _ => (1 : ℝ)/N) eig)=_
  rw [integral_finiteSpectralMeasure _ _ (fun _ => by positivity)]
  rw [Finset.mul_sum]

lemma empiricalSpectralLaw_mass {N : ℕ} (hN : 0 < N) (eig : Fin N → ℝ)
    (S : Set ℝ) (hS : MeasurableSet S) :
    (empiricalSpectralLaw hN eig : Measure ℝ).real S=
      ((Finset.univ.filter (fun i => eig i∈S)).card : ℝ)/N := by
  classical
  have hh := empiricalSpectralLaw_integral hN eig (S.indicator (fun _ => (1 : ℝ)))
  rw [integral_indicator hS,integral_const] at hh
  simp only [measureReal_def,Measure.restrict_apply_univ,smul_eq_mul,mul_one] at hh ⊢
  rw [hh]
  simp only [Set.indicator_apply,Finset.sum_ite,Finset.sum_const_zero,add_zero,
    Finset.sum_const,nsmul_eq_mul,mul_one]
  ring

lemma empiricalSpectralLaw_map {N : ℕ} (hN : 0 < N) (eig : Fin N → ℝ)
    (f : ℝ → ℝ) (hf : Measurable f) :
    Measure.map f (empiricalSpectralLaw hN eig : Measure ℝ)=
      (empiricalSpectralLaw hN (fun i => f (eig i)) : Measure ℝ) := by
  change Measure.map f (finiteSpectralMeasure (fun _ : Fin N => (1 : ℝ)/N) eig)=
    finiteSpectralMeasure (fun _ : Fin N => (1 : ℝ)/N) (fun i => f (eig i))
  unfold finiteSpectralMeasure
  rw [Measure.map_sum hf.aemeasurable]
  congr 1
  funext i
  rw [Measure.map_smul _ hf.aemeasurable,Measure.map_dirac]

end InvariantIsing

end

end OAI
