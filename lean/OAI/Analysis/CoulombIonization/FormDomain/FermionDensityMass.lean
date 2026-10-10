import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.ParticleDensity

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombLT
open CoulombPauli CoulombPackets CoulombAtom
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma fermionDensity_mass {N : ℕ} (ψ : fermionL2 (V := V) (N+1)) :
    (∫⁻ x, fermionDensity ψ x) = ENNReal.ofReal ((N+1:ℝ)*‖ψ‖^2) := by
  have he := density_weighted_lintegral ψ (fun _ => 1) measurable_const
  simp only [ENNReal.ofReal_one,one_mul] at he
  rw [he]
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.memLp ψ).aestronglyMeasurable).1 (Lp.memLp ψ)
  have hn : (∫⁻ q, ENNReal.ofReal (‖ψ q‖^2) ∂configMeasure (N+1) (spinSpaceMeasure (V := V))) =
      ENNReal.ofReal (‖ψ‖^2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
      ← CoulombPauli.l2_norm_sq]
  simp only [hn,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ N+1)]
  rw [ENNReal.ofReal_add (Nat.cast_nonneg N) zero_le_one]
  simp only [ENNReal.ofReal_natCast,ENNReal.ofReal_one,Nat.cast_add,Nat.cast_one]

lemma fermionDensity_finite_ae {N : ℕ} (ψ : fermionL2 (V := V) (N+1)) :
    ∀ᵐ x ∂(volume : Measure V), fermionDensity ψ x < ⊤ := by
  exact ae_lt_top' (fermionDensity_aemeasurable ψ) (by rw [fermionDensity_mass]; exact ENNReal.ofReal_ne_top)

lemma fermionDensity_real_integrable {N : ℕ} (ψ : fermionL2 (V := V) (N+1)) :
    Integrable (fun x => (fermionDensity ψ x).toReal) :=
  integrable_toReal_of_lintegral_ne_top (fermionDensity_aemeasurable ψ)
    (by rw [fermionDensity_mass]; exact ENNReal.ofReal_ne_top)

lemma fermionDensity_real_mass {N : ℕ} (ψ : fermionL2 (V := V) (N+1)) :
    (∫ x, (fermionDensity ψ x).toReal) = (N+1:ℝ)*‖ψ‖^2 := by
  rw [integral_toReal (fermionDensity_aemeasurable ψ) (fermionDensity_finite_ae ψ),
    fermionDensity_mass,ENNReal.toReal_ofReal (by positivity)]
end CoulombLT

end

end OAI
