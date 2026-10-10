import OAI.Analysis.LipschitzHilbert.Fourier.LineLocalizedMultiplier
import OAI.Analysis.LipschitzHilbert.Fourier.LineProjectionLipschitz

namespace OAI

/-! The actual low/high contribution of the multiplier commutator.
Both localization identities follow from the proved Fourier bands. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def lineSchwartzCommutator (m b h : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  lineSchwartzProduct b (lineSchwartzProjection m 1 (by norm_num) h)-
    lineSchwartzProjection m 1 (by norm_num) (lineSchwartzProduct b h)

theorem lineSchwartzCommutator_localized (m b h : SchwartzMap ℝ ℂ) (V : ℝ) (hV : 0<V)
    (hcutH : ∀ eta, dyadicCommutatorCutoff (V*eta)*(𝓕 h) eta=(𝓕 h) eta)
    (hcutBH : ∀ eta, dyadicCommutatorCutoff (V*eta)*(𝓕 (lineSchwartzProduct b h)) eta=
      (𝓕 (lineSchwartzProduct b h)) eta) :
    (lineSchwartzCommutator m b h : ℝ → ℂ)=
      lineMultiplicationCommutator (lineProjectionKernel (localizedLineSymbol m V hV) V hV.ne') b h := by
  funext x
  simp only [lineSchwartzCommutator,sub_apply,lineSchwartzProduct_apply,lineMultiplicationCommutator]
  rw [←localizedLineProjection_eq m h V hV hcutH,
    ←localizedLineProjection_eq m (lineSchwartzProduct b h) V hV hcutBH,
    lineSchwartzProjection_eq_convolution,lineSchwartzProjection_eq_convolution]
  rfl

theorem lowHighCommutator_localized (m b h : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) :
    let B := lineSchwartzProjection reassemblyLow (16*W) (by positivity) b
    let H := lineSchwartzProjection dyadicDifference W hW.ne' h
    (lineSchwartzCommutator m B (schwartzDerivative 1 H) : ℝ → ℂ)=
      lineMultiplicationCommutator
        (lineProjectionKernel (localizedLineSymbol m ((2/3)*W) (by positivity)) ((2/3)*W) (by positivity))
        B (schwartzDerivative 1 H) := by
  intro B H
  have hD : schwartzDerivative 1 H=lineSchwartzProjection dyadicDifference W hW.ne' (schwartzDerivative 1 h) :=
    lineSchwartzProjection_derivative dyadicDifference W hW.ne' h
  have hband : ∀ eta, (𝓕 (schwartzDerivative 1 H)) eta≠0 →
      (11/12)/W≤|eta| ∧ |eta|≤(9/4)/W := by
    intro eta heta
    rw [hD] at heta
    have hh := dyadicProjection_frequency W hW (schwartzDerivative 1 h) eta heta
    exact ⟨(div_le_div_of_nonneg_right (by norm_num : (11/12:ℝ)≤1) hW.le).trans hh.1,
      hh.2.trans (div_le_div_of_nonneg_right (by norm_num : (13/6:ℝ)≤9/4) hW.le)⟩
  have hbandB : ∀ eta, (𝓕 (lineSchwartzProduct B (schwartzDerivative 1 H))) eta≠0 →
      (11/12)/W≤|eta| ∧ |eta|≤(9/4)/W := by
    rw [hD]
    exact lowHighProduct_frequency W hW b (schwartzDerivative 1 h)
  have hcut (f : SchwartzMap ℝ ℂ)
      (hf : ∀ eta, (𝓕 f) eta≠0 → (11/12)/W≤|eta| ∧ |eta|≤(9/4)/W) (eta : ℝ) :
      dyadicCommutatorCutoff (((2/3)*W)*eta)*(𝓕 f) eta=(𝓕 f) eta := by
    have he := congrArg (fun g : SchwartzMap ℝ ℂ => (𝓕 g) eta)
      (dyadicCommutatorCutoff_absorb W hW f hf)
    simpa only [lineSchwartzProjection_fourier] using he
  exact lineSchwartzCommutator_localized m B (schwartzDerivative 1 H) ((2/3)*W) (by positivity)
    (hcut _ hband) (hcut _ hbandB)

theorem lowHighCommutator_energy (m b h : SchwartzMap ℝ ℂ) (W A L : ℝ)
    (hW : 0<W) (hA : 0≤A)
    (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    let B := lineSchwartzProjection reassemblyLow (16*W) (by positivity) b
    let H := lineSchwartzProjection dyadicDifference W hW.ne' h
    (∫ x, ‖lineSchwartzCommutator m B (schwartzDerivative 1 H) x‖^2)≤
      (L*(∫ t, ‖(𝓕⁻ reassemblyLow : SchwartzMap ℝ ℂ) t‖)*A*
        localizedKernelFirstMomentConstant dyadicCommutatorCutoff*(26*Real.pi/9))^2*
      (∫ x, ‖H x‖^2) := by
  intro B H
  let Lb := L*(∫ t, ‖(𝓕⁻ reassemblyLow : SchwartzMap ℝ ℂ) t‖)
  have hBLip (x y : ℝ) : ‖B x-B y‖≤Lb*|x-y| := by
    dsimp [B]
    rw [lineSchwartzProjection_eq_convolution,lineSchwartzProjection_eq_convolution]
    exact lineProjection_lipschitz reassemblyLow (16*W) (by positivity) b b.continuous.measurable
      (SchwartzMap.seminorm ℝ 0 0 b) (fun z => b.norm_le_seminorm ℝ z) L hLip x y
  have hR (eta : ℝ) (heta : (𝓕 H) eta≠0) : |eta|≤(13/6)/W :=
    (dyadicProjection_frequency W hW h eta heta).2
  have he := lowHighCommutator_localized m b h W hW
  have hc := localizedLineCommutator_derivative_energy m H ((2/3)*W) A (by positivity) hA hm
    B B.continuous.measurable (SchwartzMap.seminorm ℝ 0 0 B) (apply_nonneg _ _)
    (fun z => B.norm_le_seminorm ℝ z) Lb ((13/6)/W) hBLip hR
  change (∫ x, ‖lineSchwartzCommutator m B (schwartzDerivative 1 H) x‖^2)≤_
  rw [show (fun x => ‖lineSchwartzCommutator m B (schwartzDerivative 1 H) x‖^2)=
    (fun x => ‖lineMultiplicationCommutator
      (lineProjectionKernel (localizedLineSymbol m ((2/3)*W) (by positivity)) ((2/3)*W) (by positivity))
      B (schwartzDerivative 1 H) x‖^2) from by rw [he]]
  apply hc.2.trans_eq
  congr 2
  dsimp [Lb]
  field_simp [hW.ne']
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
