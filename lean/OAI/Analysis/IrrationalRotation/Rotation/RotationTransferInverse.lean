import OAI.Analysis.IrrationalRotation.Rotation.RotationTransfer

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
namespace Invariant233.Rotation

theorem exponentialTransfer_neg_eq (θ : ℝ) (b : Circle → ℝ) :
    exponentialTransfer θ (fun x => -b x) =
      WeightedShift.fieldUnboundedMultiplier circleMeasure
        (fun x k => ((Real.exp (b (action θ k x)) : ℂ))⁻¹) := by
  simp only [exponentialTransfer, Real.exp_neg, Complex.ofReal_inv]

theorem exponentialTransfer_range (θ : ℝ) (b : Circle → ℝ) :
    LinearMap.range (exponentialTransfer θ b).toFun =
      (exponentialTransfer θ (fun x => -b x)).domain := by
  rw [exponentialTransfer_neg_eq]
  exact WeightedShift.fieldMultiplier_range _
    (Eventually.of_forall fun x k => Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))

theorem exponentialTransfer_denseRange (θ : ℝ) {b : Circle → ℝ}
    (hb : Measurable b) : DenseRange (exponentialTransfer θ b) := by
  change Dense (LinearMap.range (exponentialTransfer θ b).toFun : Set Hilbert)
  rw [exponentialTransfer_range]
  exact dense_exponentialTransfer_domain θ hb.neg

theorem exponentialTransfer_mem_neg_domain (θ : ℝ) (b : Circle → ℝ)
    (ξ : (exponentialTransfer θ b).domain) :
    exponentialTransfer θ b ξ ∈ (exponentialTransfer θ (fun x => -b x)).domain := by
  rw [← exponentialTransfer_range]
  exact ⟨ξ, rfl⟩

theorem exponentialTransfer_neg_mul (θ : ℝ) (b : Circle → ℝ)
    (ξ : (exponentialTransfer θ b).domain) :
    exponentialTransfer θ (fun x => -b x)
      ⟨exponentialTransfer θ b ξ, exponentialTransfer_mem_neg_domain θ b ξ⟩ = ξ.val := by
  apply WeightedShift.fieldUnboundedMultiplier_eq_of_ae
  filter_upwards [exponentialTransfer_apply_ae θ b ξ] with x hξ
  intro k
  rw [hξ]
  simp only [Real.exp_neg, Complex.ofReal_inv]
  rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
    one_mul]

theorem exponentialTransfer_neg_mem_domain (θ : ℝ) (b : Circle → ℝ)
    (η : (exponentialTransfer θ (fun x => -b x)).domain) :
    exponentialTransfer θ (fun x => -b x) η ∈ (exponentialTransfer θ b).domain := by
  simpa only [neg_neg] using
    exponentialTransfer_mem_neg_domain θ (fun x => -b x) η

theorem exponentialTransfer_mul_neg (θ : ℝ) (b : Circle → ℝ)
    (η : (exponentialTransfer θ (fun x => -b x)).domain) :
    exponentialTransfer θ b
      ⟨exponentialTransfer θ (fun x => -b x) η,
        exponentialTransfer_neg_mem_domain θ b η⟩ = η.val := by
  apply WeightedShift.fieldUnboundedMultiplier_eq_of_ae
  filter_upwards [exponentialTransfer_apply_ae θ (fun x => -b x) η] with x hη
  intro k
  rw [hη]
  simp only [Real.exp_neg, Complex.ofReal_inv]
  rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
    one_mul]

theorem exponentialTransfer_inverse_eq (θ : ℝ) (b : Circle → ℝ) :
    (exponentialTransfer θ b).inverse = exponentialTransfer θ (fun x => -b x) := by
  apply LinearPMap.ext
  · rw [LinearPMap.inverse_domain, exponentialTransfer_range]
  · intro x hx hy
    have hker : (exponentialTransfer θ b).ker = ⊥ :=
      LinearPMap.ker_eq_bot.mpr (exponentialTransfer_injective θ b)
    exact LinearPMap.inverse_apply_eq hker (y := ⟨x, hx⟩)
      (x := ⟨exponentialTransfer θ (fun x => -b x) ⟨x, hy⟩,
        exponentialTransfer_neg_mem_domain θ b ⟨x, hy⟩⟩)
      (exponentialTransfer_mul_neg θ b ⟨x, hy⟩)

theorem exponentialTransfer_inverse_inner (θ : ℝ) (b : Circle → ℝ)
    (η : (exponentialTransfer θ (fun x => -b x)).domain)
    (ζ : (exponentialTransfer θ b).domain) :
    inner ℂ (exponentialTransfer θ (fun x => -b x) η)
      (exponentialTransfer θ b ζ) = inner ℂ η.val ζ.val := by
  have hf : (exponentialTransfer θ b).IsFormalAdjoint (exponentialTransfer θ b) := by
    have hstar : (fun x k => star (Real.exp (b (action θ k x)) : ℂ)) =
        (fun x k => (Real.exp (b (action θ k x)) : ℂ)) := by
      funext x k
      exact Complex.conj_ofReal _
    have hh := WeightedShift.fieldUnboundedMultiplier_formalAdjoint (μ := circleMeasure)
      (fun x k => (Real.exp (b (action θ k x)) : ℂ))
    rw [hstar] at hh
    exact hh
  have heq := hf
    ⟨exponentialTransfer θ (fun x => -b x) η,
      exponentialTransfer_neg_mem_domain θ b η⟩ ζ
  rw [exponentialTransfer_mul_neg] at heq
  exact heq.symm

end Invariant233.Rotation

end

end OAI
