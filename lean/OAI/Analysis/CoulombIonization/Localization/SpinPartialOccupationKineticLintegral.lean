import Mathlib
import OAI.Analysis.CoulombIonization.Localization.FermionL2
import OAI.Analysis.CoulombIonization.Localization.PacketFourier

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
namespace CoulombPackets
open CoulombPauli CoulombSobolev
open scoped LineDeriv
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {B : Type*} [MeasurableSpace B] {ν : Measure B} [SigmaFinite ν]
variable [SeparableSpace (Lp ℂ 2 ν)]
lemma spinPartialOccupation_kinetic_lintegral {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V)
    (ψ : Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν))
    (u : ι → Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν))
    (hw : ∀ i, HasWeakSpinPartialDerivative ψ (u i) (b i))
    (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1) :
    (∫⁻ p : V × V, ENNReal.ofReal ((2*Real.pi)^2 * ‖p.2‖^2 *
      ∑ s : Fin 2, spinPartialOccupation g ψ s p) ∂((volume : Measure V).prod volume)) =
    ENNReal.ofReal ((∑ i, ‖u i‖^2) + (∑ i, ∫ x : V, (∂_{b i} g x)^2) * ‖ψ‖^2) := by
  classical
  obtain ⟨κ,a,-⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 ν)
  obtain ⟨η,c,-⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 (spinSpaceMeasure (V := V)))
  let : Countable κ := hilbertBasis_countable a
  let f (s : Fin 2) (j : κ) := spinMarginal ψ s (a j)
  let v (i : ι) (s : Fin 2) (j : κ) := spinMarginal (u i) s (a j)
  let C : ℝ := ∑ i, ∫ x : V, (∂_{b i} g x)^2
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => integral_nonneg fun _ => sq_nonneg _)
  have hscalar (s : Fin 2) (j : κ) := packet_kinetic b (f s j) (fun i => v i s j)
    (fun i => spinMarginal_weak_derivative (hw i) s (a j)) g hg
  have hexp (s : Fin 2) (p : V × V) :
      ENNReal.ofReal ((2*Real.pi)^2 * ‖p.2‖^2 * spinPartialOccupation g ψ s p) =
      ∑' j : κ, ENNReal.ofReal
        ((2*Real.pi)^2 * ‖p.2‖^2 * ‖inner ℂ (packet g p) (f s j)‖^2) := by
    rw [ENNReal.ofReal_mul (by positivity), spinPartialOccupation_expansion g ψ a,
      ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro j
    rw [spinPacket_coefficient]
    simp only [f, spinMarginal, spinBasis_apply]
    exact (ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _))).symm
  have hj (s : Fin 2) (j : κ) : (∫⁻ p : V × V, ENNReal.ofReal
      ((2*Real.pi)^2 * ‖p.2‖^2 * ‖inner ℂ (packet g p) (f s j)‖^2)
      ∂((volume : Measure V).prod volume)) =
      ENNReal.ofReal ((∑ i, ‖v i s j‖^2) + C * ‖f s j‖^2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hscalar s j).1
      (Filter.Eventually.of_forall fun _ => by positivity), (hscalar s j).2]
  have hsum (j : κ) : (∑ s : Fin 2, ((∑ i, ‖v i s j‖^2) + C * ‖f s j‖^2)) =
      (∑ i, ‖(tensorRight (a j)).adjoint (u i)‖^2) + C * ‖(tensorRight (a j)).adjoint ψ‖^2 := by
    rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum]
    simp only [v, f, spinMarginal_sum_norm]
  have hall : HasSum (fun j : κ => (∑ i, ‖(tensorRight (a j)).adjoint (u i)‖^2) +
      C * ‖(tensorRight (a j)).adjoint ψ‖^2) ((∑ i, ‖u i‖^2) + C * ‖ψ‖^2) :=
    (hasSum_sum (fun i _ => tensorRight_hasSum_general c a (u i))).add
      ((tensorRight_hasSum_general c a ψ).mul_left C)
  have hnon (p : V × V) (s : Fin 2) :
      0 ≤ (2*Real.pi)^2 * ‖p.2‖^2 * spinPartialOccupation g ψ s p :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  have hexpall (p : V × V) :
      ENNReal.ofReal ((2*Real.pi)^2 * ‖p.2‖^2 * ∑ s : Fin 2, spinPartialOccupation g ψ s p) =
      ∑' s : Fin 2, ∑' j : κ, ENNReal.ofReal
        ((2*Real.pi)^2 * ‖p.2‖^2 * ‖inner ℂ (packet g p) (f s j)‖^2) := by
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun s _ => hnon p s), tsum_fintype]
    simp only [hexp]
  calc
    _ = ∑' s : Fin 2, ∫⁻ p : V × V, ∑' j : κ, ENNReal.ofReal
        ((2*Real.pi)^2 * ‖p.2‖^2 * ‖inner ℂ (packet g p) (f s j)‖^2)
        ∂((volume : Measure V).prod volume) := by
      simp only [hexpall]
      apply lintegral_tsum
      intro s
      exact AEMeasurable.tsum (fun j =>
        (hscalar s j).1.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    _ = ∑' j : κ, ∑' s : Fin 2, ENNReal.ofReal ((∑ i, ‖v i s j‖^2) + C * ‖f s j‖^2) := by
      simp_rw [lintegral_tsum (fun j =>
        (hscalar _ j).1.aestronglyMeasurable.aemeasurable.ennreal_ofReal), hj]
      exact ENNReal.tsum_comm
    _ = ∑' j : κ, ENNReal.ofReal ((∑ i, ‖(tensorRight (a j)).adjoint (u i)‖^2) +
        C * ‖(tensorRight (a j)).adjoint ψ‖^2) := by
      apply tsum_congr
      intro j
      rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), hsum]
    _ = _ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hall.summable, hall.tsum_eq]
lemma spinPartialOccupation_kinetic {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V)
    (ψ : Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν))
    (u : ι → Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν))
    (hw : ∀ i, HasWeakSpinPartialDerivative ψ (u i) (b i))
    (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1) :
    Integrable (fun p : V × V => (2*Real.pi)^2 * ‖p.2‖^2 *
      ∑ s : Fin 2, spinPartialOccupation g ψ s p) ((volume : Measure V).prod volume) ∧
    (∫ p : V × V, (2*Real.pi)^2 * ‖p.2‖^2 * ∑ s : Fin 2, spinPartialOccupation g ψ s p
      ∂((volume : Measure V).prod volume)) =
    (∑ i, ‖u i‖^2) + (∑ i, ∫ x : V, (∂_{b i} g x)^2) * ‖ψ‖^2 := by
  have hp (p : V × V) : 0 ≤ (2*Real.pi)^2 * ‖p.2‖^2 *
      ∑ s : Fin 2, spinPartialOccupation g ψ s p := by
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hm : AEStronglyMeasurable
      (fun p : V × V => (2*Real.pi)^2 * ‖p.2‖^2 * ∑ s : Fin 2, spinPartialOccupation g ψ s p)
      ((volume : Measure V).prod volume) :=
    (by fun_prop : Continuous (fun p : V × V => (2*Real.pi)^2 * ‖p.2‖^2)).aestronglyMeasurable.mul
      (integrable_finsetSum Finset.univ
        (fun s _ => spinPartialOccupation_integrable g hg ψ s)).aestronglyMeasurable
  have he := spinPartialOccupation_kinetic_lintegral b ψ u hw g hg
  have hi : Integrable (fun p : V × V => (2*Real.pi)^2 * ‖p.2‖^2 *
      ∑ s : Fin 2, spinPartialOccupation g ψ s p) ((volume : Measure V).prod volume) := by
    refine ⟨hm, ?_⟩
    rw [HasFiniteIntegral]
    simp only [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hp _)]
    rw [he]
    exact ENNReal.ofReal_lt_top
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hp)] at he
  apply (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hp) (by positivity)).1 he
end CoulombPackets

end

end OAI
