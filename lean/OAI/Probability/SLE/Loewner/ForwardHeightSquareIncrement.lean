import OAI.Probability.SLE.Loewner.CapacityPointwiseLoewner
import OAI.Probability.SLE.Geometry.EndpointMonotonicity

namespace OAI

/-! The squared height can decrease by at most twice elapsed capacity.
The proof uses pointwise right derivatives and includes both endpoints. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

lemma height_kernel_square_bound (z : ℂ) (u : ℝ) :
    2*z.im^2/Complex.normSq (z-(u:ℂ))-2≤0 := by
  have hsq : z.im^2≤Complex.normSq (z-(u:ℂ)) := by
    simp only [Complex.normSq_apply,sub_im,ofReal_im,sub_zero]
    nlinarith [sq_nonneg (z-(u:ℂ)).re]
  by_cases hn : Complex.normSq (z-(u:ℂ))=0
  · simp only [hn,div_zero,zero_sub]
    norm_num
  · have hpos := lt_of_le_of_ne (Complex.normSq_nonneg (z-(u:ℂ))) (Ne.symm hn)
    have hb : 2*z.im^2/Complex.normSq (z-(u:ℂ))≤2 :=
      (div_le_iff₀ hpos).mpr (by nlinarith)
    linarith

theorem height_square_increment {f : ℝ → ℂ} {u : ℝ → ℝ} {a b : ℝ}
    (hab : a≤b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ c∈Ico a b, HasDerivWithinAt f (1/(f c-(u c:ℂ))) (Ici c) c) :
    (f a).im^2≤(f b).im^2+2*(b-a) := by
  let g (c : ℝ) := -(f c).im^2-2*c
  let v (c : ℝ) := 2*(f c).im^2/Complex.normSq (f c-(u c:ℂ))-2
  have hg : ContinuousOn g (Icc a b) :=
    ((Complex.continuous_im.comp_continuousOn hf).pow 2).neg.sub
      (continuousOn_const.mul continuousOn_id)
  have hgd (c : ℝ) (hc : c∈Ico a b) : HasDerivWithinAt g (v c) (Ici c) c := by
    have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt c (hd c hc)
    change HasDerivWithinAt (fun x => (f x).im) (1/(f c-(u c:ℂ))).im (Ici c) c at hi
    have hh := (hi.pow 2).neg.sub ((hasDerivWithinAt_id c (Ici c)).const_mul 2)
    convert! hh using 1
    dsimp only [v]
    simp only [Complex.div_im,one_im,one_re,zero_mul,one_mul,sub_im,ofReal_im,sub_zero]
    ring
  have hb := image_le_of_deriv_right_le_deriv_boundary hg hgd
    (B := fun _ => g a) (B' := fun _ => 0) le_rfl continuousOn_const
    (fun c _ => hasDerivWithinAt_const c (Ici c) (g a))
    (fun c _ => height_kernel_square_bound (f c) (u c)) (show b∈Icc a b from ⟨hab,le_rfl⟩)
  dsimp only [g] at hb
  linarith

end SLEExactGauge

end

end OAI
