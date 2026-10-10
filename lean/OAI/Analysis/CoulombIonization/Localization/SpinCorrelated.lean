import Mathlib
import OAI.Analysis.CoulombIonization.Localization.Trace

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
variable {B : Type*} [MeasurableSpace B] {ν : Measure B} [SigmaFinite ν]
  [SeparableSpace (Lp ℂ 2 ν)]

def spinPartialOccupation (g : 𝓢(V, ℝ))
    (ψ : Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν)) (s : Fin 2) (p : V × V) : ℝ :=
  ‖(tensorLeft (ν := ν) (spinPacket g s p)).adjoint ψ‖^2

omit [SeparableSpace (Lp ℂ 2 ν)] in
lemma spinPartialOccupation_expansion (g : 𝓢(V, ℝ))
    (ψ : Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν))
    {κ : Type*} (b : HilbertBasis κ ℂ (Lp ℂ 2 ν)) (s : Fin 2) (p : V × V) :
    ENNReal.ofReal (spinPartialOccupation g ψ s p) =
      ∑' j, ENNReal.ofReal (‖inner ℂ (spinPacket g s p) ((tensorRight (b j)).adjoint ψ)‖^2) := by
  have h := basis_parseval b ((tensorLeft (ν := ν) (spinPacket g s p)).adjoint ψ)
  rw [spinPartialOccupation, ← h.tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) h.summable]
  simp_rw [tensor_adjoint_exchange]

lemma spinPartialOccupation_measurable (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1)
    (ψ : Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν)) (s : Fin 2) :
    AEMeasurable (fun p => ENNReal.ofReal (spinPartialOccupation g ψ s p))
      ((volume : Measure V).prod volume) := by
  obtain ⟨w,b,-⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 ν)
  let : Countable w := hilbertBasis_countable b
  simp_rw [spinPartialOccupation_expansion g ψ b, spinPacket_coefficient]
  exact AEMeasurable.tsum (fun _ => packet_coefficient_measurable g hg _)

lemma spinPartialOccupation_mass (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1)
    (ψ : Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν)) :
    (∑ s : Fin 2, ∫⁻ p, ENNReal.ofReal (spinPartialOccupation g ψ s p)
      ∂((volume : Measure V).prod volume)) = ENNReal.ofReal (‖ψ‖^2) := by
  obtain ⟨w,b,-⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 ν)
  obtain ⟨v,a,-⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 (spinSpaceMeasure (V := V)))
  let : Countable w := hilbertBasis_countable b
  simp_rw [spinPartialOccupation_expansion g ψ b]
  suffices hs : (∑' s : Fin 2, ∫⁻ p, ∑' j : w, ENNReal.ofReal
      (‖inner ℂ (spinPacket g s p) ((tensorRight (b j)).adjoint ψ)‖^2)
      ∂((volume : Measure V).prod volume)) = ENNReal.ofReal (‖ψ‖^2) by
    simpa only [tsum_fintype] using hs
  calc
    _ = ∑' s : Fin 2, ∑' j : w, ∫⁻ p, ENNReal.ofReal
        (‖inner ℂ (spinPacket g s p) ((tensorRight (b j)).adjoint ψ)‖^2)
        ∂((volume : Measure V).prod volume) := by
      congr 1; funext s
      apply lintegral_tsum
      intro j
      simp_rw [spinPacket_coefficient]
      exact packet_coefficient_measurable g hg _
    _ = ∑' j : w, ENNReal.ofReal (‖(tensorRight (b j)).adjoint ψ‖^2) := by
      rw [ENNReal.tsum_comm]
      congr 1; funext j
      rw [tsum_fintype, spinPacket_plancherel g hg]
    _ = _ := tensorRight_parseval a b ψ

end CoulombPackets

end

end OAI
