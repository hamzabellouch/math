import OAI.Analysis.LipschitzHilbert.Fourier.LineHighLowSpectrum

namespace OAI

/-! The exact differentiated commutator identity and its low-output
energy estimate, before the comparable-frequency summation. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem schwartzDerivative_one_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzDerivative 1 f x=deriv f x := rfl

theorem schwartzDerivative_product (f g : SchwartzMap ℝ ℂ) :
    schwartzDerivative 1 (lineSchwartzProduct f g)=
      lineSchwartzProduct (schwartzDerivative 1 f) g+
        lineSchwartzProduct f (schwartzDerivative 1 g) := by
  ext x
  simp only [schwartzDerivative_one_apply,lineSchwartzProduct_apply,add_apply]
  change deriv (fun x => f x*g x) x=deriv f x*g x+f x*deriv g x
  exact deriv_mul f.differentiable.differentiableAt g.differentiable.differentiableAt

theorem lineSchwartzCommutator_derivative_identity (m b h : SchwartzMap ℝ ℂ) :
    lineSchwartzCommutator m b (schwartzDerivative 1 h)=
      schwartzDerivative 1 (lineSchwartzCommutator m b h)-
        lineSchwartzProduct (schwartzDerivative 1 b) (lineSchwartzProjection m 1 (by norm_num) h)+
        lineSchwartzProjection m 1 (by norm_num) (lineSchwartzProduct (schwartzDerivative 1 b) h) := by
  have hlin (f g : SchwartzMap ℝ ℂ) : schwartzDerivative 1 (f-g)=
      schwartzDerivative 1 f-schwartzDerivative 1 g :=
    map_sub (SchwartzMap.derivCLM ℂ ℂ) f g
  have hproj (f g : SchwartzMap ℝ ℂ) : lineSchwartzProjection m 1 (by norm_num) (f+g)=
      lineSchwartzProjection m 1 (by norm_num) f+lineSchwartzProjection m 1 (by norm_num) g :=
    map_add (lineSchwartzProjectionLM m 1 (by norm_num)) f g
  simp only [lineSchwartzCommutator,hlin,schwartzDerivative_product,
    lineSchwartzProjection_derivative,hproj]
  abel

theorem lineSchwartzCommutator_ball (m b h : SchwartzMap ℝ ℂ) (B H : ℝ)
    (hb : ∀ eta, (𝓕 b : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤B)
    (hh : ∀ eta, (𝓕 h : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤H) :
    ∀ eta, (𝓕 (lineSchwartzCommutator m b h) : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤B+H := by
  intro eta heta
  have ht : ∀ eta, (𝓕 (lineSchwartzProjection m 1 (by norm_num) h) : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤H := by
    intro eta he
    exact hh eta (lineSchwartzProjection_frequency_of_nonzero m h 1 (by norm_num) eta he)
  have hu := lineSchwartzProduct_band b (lineSchwartzProjection m 1 (by norm_num) h) B H hb ht
  have hv := lineSchwartzProduct_band b h B H hb hh
  by_contra hn
  have hzero1 : (𝓕 (lineSchwartzProduct b (lineSchwartzProjection m 1 (by norm_num) h)) : SchwartzMap ℝ ℂ) eta=0 :=
    not_ne_iff.mp (fun hx => hn (hu eta hx))
  have hzero2 : (𝓕 (lineSchwartzProduct b h) : SchwartzMap ℝ ℂ) eta=0 :=
    not_ne_iff.mp (fun hx => hn (hv eta hx))
  apply heta
  change (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ)
    (lineSchwartzProduct b (lineSchwartzProjection m 1 (by norm_num) h)-
      lineSchwartzProjection m 1 (by norm_num) (lineSchwartzProduct b h))) eta=0
  rw [map_sub,sub_apply,FourierTransform.fourierCLM_apply,FourierTransform.fourierCLM_apply,
    lineSchwartzProjection_fourier,hzero1,hzero2,mul_zero,sub_zero]

theorem projectedCommutator_derivative_energy (m b h : SchwartzMap ℝ ℂ)
    (W V A L : ℝ) (hW : 0<W) (hV : 0<V) (hm : ∀ eta, ‖m eta‖≤A)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    let B := lineSchwartzProjection dyadicDifference W hW.ne' b
    (∫ x, ‖lineSchwartzProjection dyadicDifference V hV.ne'
      (schwartzDerivative 1 (lineSchwartzCommutator m B h)) x‖^2)≤
      (A*L*(∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖)*
        (52*Real.pi/3)*(W/V))^2*(∫ x, ‖h x‖^2) := by
  intro B
  let M := ∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖
  let F := lineSchwartzCommutator m B h
  have hb (x : ℝ) : ‖B x‖≤L*W*M := by
    dsimp [B]
    rw [lineSchwartzProjection_eq_convolution]
    exact dyadicProjection_lipschitz_bound W hW b b.continuous.measurable
      (SchwartzMap.seminorm ℝ 0 0 b) (fun z => b.norm_le_seminorm ℝ z) L hLip x
  have hc := lineSchwartzCommutator_bounded_energy m B h A (L*W*M) hm hb
  have hp := lineSchwartzProjection_energy dyadicDifference V hV.ne' 2 dyadicDifference_norm F
  have hd := line_bernstein_energy (lineSchwartzProjection dyadicDifference V hV.ne' F) ((13/6)/V)
    (fun eta heta => (dyadicProjection_frequency V hV F eta heta).2)
  rw [←lineSchwartzProjection_derivative]
  calc
    _ ≤ (2*Real.pi*((13/6)/V))^2*(∫ x, ‖lineSchwartzProjection dyadicDifference V hV.ne' F x‖^2) := hd
    _ ≤ (2*Real.pi*((13/6)/V))^2*(2^2*(∫ x, ‖F x‖^2)) :=
      mul_le_mul_of_nonneg_left hp (sq_nonneg _)
    _ ≤ (2*Real.pi*((13/6)/V))^2*(2^2*(4*A^2*(L*W*M)^2*(∫ x, ‖h x‖^2))) := by
      gcongr
    _ = _ := by dsimp [M]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
