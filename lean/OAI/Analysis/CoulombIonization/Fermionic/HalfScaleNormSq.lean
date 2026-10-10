import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.FourierMomentGradient
import OAI.Analysis.CoulombIonization.Localization.TensorRightSpinVectorAe

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
open CoulombPauli CoulombPackets
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {N : ℕ} {κ : Type*}

lemma half_scale_norm_sq {H : Type*} [SeminormedAddCommGroup H] [NormedSpace ℂ H]
    (u : H) : ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • u‖^2 = (1/2:ℝ)*‖u‖^2 := by
  have hc : ((Real.sqrt 2)⁻¹)^2 = (1/2:ℝ) := by
    rw [inv_pow,Real.sq_sqrt (by norm_num)]; norm_num
  simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,hc]

lemma marginal_family_trace
    (b : HilbertBasis κ ℂ (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := V)))))
    (ψ : Fin (N+1) → fermionL2 (V := V) (N+1)) :
    (∑' p : Fin (N+1) × Fin 2 × κ,
      ENNReal.ofReal (‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
        spinMarginal (splitFermion p.1 (ψ p.1)) p.2.1 (b p.2.2)‖^2)) =
      ENNReal.ofReal ((1/2:ℝ) * ∑ i, ‖ψ i‖^2) := by
  simp_rw [half_scale_norm_sq,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
  rw [ENNReal.tsum_mul_left,ENNReal.tsum_prod']
  simp_rw [spinMarginal_parseval_norm b,splitFermion_norm,tsum_fintype,
    ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]

lemma fermionFamily_trace
    (b : HilbertBasis κ ℂ (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := V)))))
    (ψ : fermionL2 (V := V) (N+1)) :
    (∑' p, ENNReal.ofReal (‖fermionFamily b ψ p‖^2)) =
      ENNReal.ofReal ((N+1:ℝ)/2 * ‖ψ‖^2) := by
  have h := marginal_family_trace b (fun _ => ψ)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_add,Nat.cast_one] at h
  unfold fermionFamily
  rw [h]
  congr 1
  ring

end CoulombLT

end

end OAI
