import OAI.Analysis.OperatorAlgebra.ContinuousLpFieldNorm
import OAI.Analysis.ModularTheory.OriginalRightAction

namespace OAI

/-! Evaluation at time zero transfers the modular product norm bound to the
original left/right representation. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma modularLp_product_ae (S : StandardModularData H)
    (a b : H →L[ℂ] H) (f : Lp H 2 (volume : Measure ℝ)) :
    (modularLpRepresentation volume S.D a * pointwiseLpRepresentation volume b) f
      =ᵐ[volume] fun t => (S.D.unitary (-t) * a * S.D.unitary t * b) (f t) := by
  filter_upwards [modularLpRepresentation_ae volume S.D a (b.compLpL 2 volume f),
    b.coeFn_compLpL f] with t ha hb
  change modularLpRepresentation volume S.D a (b.compLpL 2 volume f) t = _
  rw [ha, hb]
  rfl

lemma modularLp_product_sum_ae (S : StandardModularData H)
    {I : Type*} [Fintype I] (a b : I → H →L[ℂ] H)
    (f : Lp H 2 (volume : Measure ℝ)) :
    (∑ i, modularLpRepresentation volume S.D (a i) *
        pointwiseLpRepresentation volume (b i)) f =ᵐ[volume]
      fun t => (∑ i, S.D.unitary (-t) * a i * S.D.unitary t * b i) (f t) := by
  classical
  have hs := Lp.coeFn_finsetSum Finset.univ
    (fun i => (modularLpRepresentation volume S.D (a i) *
      pointwiseLpRepresentation volume (b i)) f)
  have ht : ∀ᵐ t ∂volume, ∀ i,
      (modularLpRepresentation volume S.D (a i) *
          pointwiseLpRepresentation volume (b i)) f t =
        (S.D.unitary (-t) * a i * S.D.unitary t * b i) (f t) :=
    ae_all_iff.mpr (fun i => modularLp_product_ae S (a i) (b i) f)
  filter_upwards [hs, ht] with t hsum hterm
  simp only [Finset.sum_apply] at hsum
  simpa only [sum_apply] using hsum.trans (Finset.sum_congr rfl (fun i _ => hterm i))

lemma modularLp_product_sum_norm_ge (S : StandardModularData H)
    {I : Type*} [Fintype I] (a b : I → H →L[ℂ] H) :
    ‖∑ i, a i * b i‖ ≤
      ‖∑ i, modularLpRepresentation volume S.D (a i) *
        pointwiseLpRepresentation volume (b i)‖ := by
  have hc (x : H) : Continuous (fun t : ℝ =>
      (∑ i, S.D.unitary (-t) * a i * S.D.unitary t * b i) x) := by
    simp only [sum_apply, mul_apply_eq_comp]
    apply continuous_finsetSum
    intro i _
    exact S.D.continuous_unitary_action.comp
      (continuous_neg.prodMk ((a i).continuous.comp
        (S.D.continuous_unitary_apply (b i x))))
  have h := continuousLpField_norm_le
    (∑ i, modularLpRepresentation volume S.D (a i) * pointwiseLpRepresentation volume (b i))
    (fun t => ∑ i, S.D.unitary (-t) * a i * S.D.unitary t * b i)
    (modularLp_product_sum_ae S a b) 0 (fun x => (hc x).continuousAt)
  simpa only [neg_zero, S.D.unitary_zero, one_mul, mul_one] using h

lemma modularRight_product_sum_norm_ge (S : StandardModularData H)
    {I : Type*} [Fintype I] (a b : I → H →L[ℂ] H) :
    ‖∑ i, a i * antiunitaryConjugate S.J (star (b i))‖ ≤
      ‖∑ i, modularLpRepresentation volume S.D (a i) *
        modularTracialRightAction S (modularLpRepresentation volume S.D (b i))‖ := by
  simp only [modularTracialRightAction_coefficient]
  exact modularLp_product_sum_norm_ge S a (fun i => antiunitaryConjugate S.J (star (b i)))

end WeakPureInfiniteness

end

end OAI
