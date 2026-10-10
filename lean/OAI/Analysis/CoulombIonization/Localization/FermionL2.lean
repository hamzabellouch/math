import Mathlib
import OAI.Analysis.CoulombIonization.Localization.SpinCorrelated
import OAI.Analysis.CoulombIonization.Fermionic.Pauli
import OAI.Analysis.CoulombIonization.Ionization.PullAdjoint

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
namespace CoulombPackets
open CoulombPauli
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
section SpinIntegral
variable {B : Type*} [MeasurableSpace B] {ν : Measure B} [SigmaFinite ν]
  [SeparableSpace (Lp ℂ 2 ν)]
lemma spinPartialOccupation_integrable (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1)
    (ψ : Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν)) (s : Fin 2) :
    Integrable (spinPartialOccupation g ψ s) ((volume : Measure V).prod volume) := by
  have hp (p : V × V) : 0 ≤ spinPartialOccupation g ψ s p := sq_nonneg _
  have hm := spinPartialOccupation_measurable g hg ψ s
  have hm' : AEStronglyMeasurable (spinPartialOccupation g ψ s) ((volume : Measure V).prod volume) := by
    have h := hm.ennreal_toReal.aestronglyMeasurable
    simpa only [Function.comp_def, ENNReal.toReal_ofReal (hp _)] using h
  refine ⟨hm', ?_⟩
  rw [HasFiniteIntegral]
  simp only [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hp _)]
  apply lt_of_le_of_lt (b := ENNReal.ofReal (‖ψ‖^2)) _ ENNReal.ofReal_lt_top
  calc
    _ ≤ ∑ t : Fin 2, ∫⁻ p, ENNReal.ofReal (spinPartialOccupation g ψ t p)
        ∂((volume : Measure V).prod volume) :=
      Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ s)
    _ = _ := spinPartialOccupation_mass g hg ψ

lemma spinPartialOccupation_total_integral (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1)
    (ψ : Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν)) :
    (∫ p, ∑ s : Fin 2, spinPartialOccupation g ψ s p
      ∂((volume : Measure V).prod volume)) = ‖ψ‖^2 := by
  rw [integral_finsetSum Finset.univ (fun s _ => spinPartialOccupation_integrable g hg ψ s)]
  apply (ENNReal.ofReal_eq_ofReal_iff
    (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _) (sq_nonneg _)).1
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => integral_nonneg fun _ => sq_nonneg _)]
  calc
    _ = ∑ s : Fin 2, ∫⁻ p, ENNReal.ofReal (spinPartialOccupation g ψ s p)
        ∂((volume : Measure V).prod volume) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact ofReal_integral_eq_lintegral_ofReal (spinPartialOccupation_integrable g hg ψ s)
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    _ = _ := spinPartialOccupation_mass g hg ψ
end SpinIntegral

local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

abbrev fermionL2 (N : ℕ) := sectorL2 N (spinSpaceMeasure (V := V))

def splitFermion {N : ℕ} (i : Fin (N+1)) (ψ : fermionL2 (V := V) (N+1)) :
    Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod (configMeasure N (spinSpaceMeasure (V := V)))) :=
  pull (splitAt i).symm ((splitAt_preserving (μ := spinSpaceMeasure (V := V)) i).symm (splitAt i)) ψ

lemma splitFermion_norm {N : ℕ} (i : Fin (N+1)) (ψ : fermionL2 (V := V) (N+1)) :
    ‖splitFermion i ψ‖ = ‖ψ‖ := pull_norm _ _ _

lemma insert_adjoint_split {N : ℕ} (i : Fin (N+1)) (u : Lp ℂ 2 (spinSpaceMeasure (V := V)))
    (ψ : fermionL2 (V := V) (N+1)) :
    (insertOrbital i u).adjoint ψ = (tensorLeft u).adjoint (splitFermion i ψ) := by
  rw [insertOrbital, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
    pull_adjoint_symm]
  rfl

def fermionHusimi {N : ℕ} (g : 𝓢(V, ℝ)) (i : Fin (N+1))
    (ψ : fermionL2 (V := V) (N+1)) (p : V × V) : ℝ :=
  (N+1 : ℝ) * ∑ s : Fin 2, ‖(insertOrbital i (spinPacket g s p)).adjoint ψ‖^2

lemma fermionHusimi_eq {N : ℕ} (g : 𝓢(V, ℝ)) (i : Fin (N+1))
    (ψ : fermionL2 (V := V) (N+1)) (p : V × V) :
    fermionHusimi g i ψ p =
    (N+1 : ℝ) * ∑ s : Fin 2, spinPartialOccupation g (splitFermion i ψ) s p := by
  simp only [fermionHusimi, spinPartialOccupation, insert_adjoint_split]

lemma fermionHusimi_integrable {N : ℕ} (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1)
    (i : Fin (N+1)) (ψ : fermionL2 (V := V) (N+1)) :
    Integrable (fermionHusimi g i ψ) ((volume : Measure V).prod volume) := by
  simp_rw [show fermionHusimi g i ψ = fun p =>
    (N+1 : ℝ) * ∑ s : Fin 2, spinPartialOccupation g (splitFermion i ψ) s p from
      funext (fermionHusimi_eq g i ψ)]
  exact (integrable_finsetSum Finset.univ
    (fun s _ => spinPartialOccupation_integrable g hg (splitFermion i ψ) s)).const_mul _

lemma fermionHusimi_mass {N : ℕ} (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1)
    (i : Fin (N+1)) (ψ : fermionL2 (V := V) (N+1)) :
    (∫ p, fermionHusimi g i ψ p ∂((volume : Measure V).prod volume)) =
      (N+1 : ℝ) * ‖ψ‖^2 := by
  simp_rw [fermionHusimi_eq]
  rw [integral_const_mul, spinPartialOccupation_total_integral g hg, splitFermion_norm]

lemma fermionHusimi_nonneg {N : ℕ} (g : 𝓢(V, ℝ)) (i : Fin (N+1))
    (ψ : fermionL2 (V := V) (N+1)) (p : V × V) : 0 ≤ fermionHusimi g i ψ p :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma fermionHusimi_le_two {N : ℕ} (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1)
    (i : Fin (N+1)) (ψ : fermionL2 (V := V) (N+1))
    (ha : ∀ i j : Fin (N+1), i ≠ j → permute (Equiv.swap i j) ψ = -ψ)
    (p : V × V) : fermionHusimi g i ψ p ≤ 2 * ‖ψ‖^2 := by
  unfold fermionHusimi
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ _s : Fin 2, ‖ψ‖^2 := Finset.sum_le_sum (fun s _ =>
      occupation_le_one i (spinPacket g s p) (spinPacket_norm g hg s p) ψ ha)
    _ = _ := by simp

end CoulombPackets

open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal

end

end OAI
