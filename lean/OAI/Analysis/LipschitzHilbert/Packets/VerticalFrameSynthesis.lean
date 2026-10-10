import OAI.Analysis.LipschitzHilbert.Fourier.VerticalSelfAdjoint

namespace OAI

/-! Finite vertical-band synthesis follows from the same square bound
as analysis, using self-adjointness and Hilbert-space duality. -/
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation
variable {ι : Type*}

theorem verticalFrame_synthesis (I : Finset ι) (p : ι → SchwartzMap ℝ ℂ) (w : ι → ℝ)
    (hw : ∀ i, 0<w i) (hp : ∀ i s, conj (p i s)=p i s)
    (M : ℝ) (hM : 0≤M) (hsymbol : ∀ eta, (∑ i∈I, ‖p i (w i*eta)‖^2)≤M)
    (f : ι → Lp ℂ 2 planeMeasure) :
    ‖∑ i∈I, verticalL2Projection (p i) (w i) (f i)‖≤
      Real.sqrt M*Real.sqrt (∑ i∈I, ‖f i‖^2) := by
  let y := ∑ i∈I, verticalL2Projection (p i) (w i) (f i)
  let E := ∑ i∈I, ‖f i‖^2
  have hE : 0≤E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hid : inner ℂ y y=∑ i∈I, inner ℂ (f i) (verticalL2Projection (p i) (w i) y) := by
    change inner ℂ (∑ i∈I, verticalL2Projection (p i) (w i) (f i)) y=_
    simp only [sum_inner]
    exact Finset.sum_congr rfl (fun i _ => verticalL2Projection_inner (p i) (hp i) (w i) (hw i) (f i) y)
  have hsq : ‖y‖^2≤Real.sqrt E*Real.sqrt (M*‖y‖^2) := by
    calc
      _ = ‖inner ℂ y y‖ := by
        simp only [inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg y)]
      _ = ‖∑ i∈I, inner ℂ (f i) (verticalL2Projection (p i) (w i) y)‖ := congrArg norm hid
      _ ≤ ∑ i∈I, ‖inner ℂ (f i) (verticalL2Projection (p i) (w i) y)‖ := norm_sum_le _ _
      _ ≤ ∑ i∈I, ‖f i‖*‖verticalL2Projection (p i) (w i) y‖ :=
        Finset.sum_le_sum (fun _ _ => norm_inner_le_norm _ _)
      _ ≤ Real.sqrt E*Real.sqrt (∑ i∈I, ‖verticalL2Projection (p i) (w i) y‖^2) :=
        Real.sum_mul_le_sqrt_mul_sqrt I _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (verticalFrame_L2 I p w hw M hsymbol y)) (Real.sqrt_nonneg E)
  rw [Real.sqrt_mul hM,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg y)] at hsq
  by_cases hy : ‖y‖=0
  · change ‖y‖≤_
    rw [hy]
    positivity
  · have hypos : 0<‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy)
    apply (mul_le_mul_iff_right₀ hypos).mp
    change ‖y‖*‖y‖≤‖y‖*(Real.sqrt M*Real.sqrt E)
    nlinarith only [hsq]

end LipschitzHilbert.PacketRepresentation

end

end OAI
