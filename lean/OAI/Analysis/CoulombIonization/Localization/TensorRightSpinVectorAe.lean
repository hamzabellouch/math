import Mathlib
import OAI.Analysis.CoulombIonization.Localization.PacketFourier
import OAI.Analysis.CoulombIonization.ThomasFermi.ContractFunction

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
namespace CoulombPackets
open CoulombPauli
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma tensorRight_spinVector_ae
    (ψ : Lp ℂ 2 (spinSpaceMeasure (V := V))) (s : Fin 2) :
    (fun x => ((tensorRight (spinVector s)).adjoint ψ) x) =ᵐ[volume]
      (fun x => ψ (x,s)) := by
  rw [tensorRight_adjoint_eq_contract]
  filter_upwards [contractL2_ae (spinVector s) ψ, memLp_slice_ae ψ] with x hx hm
  rw [hx,contractFunction_slice (spinVector s) ψ x hm, spinVector_inner]
  exact (Measure.ae_count_iff.mp hm.coeFn_toLp) s

variable {B : Type*} [MeasurableSpace B] {ν : Measure B} [SigmaFinite ν]
lemma spinMarginal_slice_parseval {κ : Type*} [Countable κ]
    (b : HilbertBasis κ ℂ (Lp ℂ 2 ν))
    (ψ : Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν)) :
    ∀ᵐ x ∂(volume : Measure V), ∀ s : Fin 2,
      (∑' j, ENNReal.ofReal (‖spinMarginal ψ s (b j) x‖^2)) =
        ∫⁻ y, ENNReal.ofReal (‖ψ ((x,s),y)‖^2) ∂ν := by
  have h1 (s : Fin 2) (j : κ) :
      (fun x => spinMarginal ψ s (b j) x) =ᵐ[volume]
        (fun x => ((tensorRight (b j)).adjoint ψ) (x,s)) :=
    tensorRight_spinVector_ae ((tensorRight (b j)).adjoint ψ) s
  have h2 := Measure.ae_ae_of_ae_prod (tensorRight_slice_parseval b ψ)
  filter_upwards [ae_all_iff.mpr (fun s => ae_all_iff.mpr (h1 s)), h2] with x hx hy
  intro s
  rw [← Measure.ae_count_iff.mp hy s]
  apply tsum_congr
  intro j
  rw [hx s j]

lemma spinMarginal_parseval_norm {κ : Type*}
    (b : HilbertBasis κ ℂ (Lp ℂ 2 ν))
    (ψ : Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν)) :
    (∑' p : Fin 2 × κ, ENNReal.ofReal (‖spinMarginal ψ p.1 (b p.2)‖^2)) =
      ENNReal.ofReal (‖ψ‖^2) := by
  obtain ⟨ι,a,-⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 (spinSpaceMeasure (V := V)))
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  simp_rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
    spinMarginal_sum_norm]
  exact tensorRight_parseval a b ψ
end CoulombPackets

end

end OAI
