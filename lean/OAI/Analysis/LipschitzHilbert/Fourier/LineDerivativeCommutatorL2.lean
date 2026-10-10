import OAI.Analysis.LipschitzHilbert.Fourier.LineSchwartzCommutatorEstimate

namespace OAI

/-! The differentiated Lipschitz commutator has its actual bounded L2
extension, with the uniform constant proved by dyadic decomposition. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def lineCommutatorNormConstant : ℝ := Real.sqrt lineCommutatorEnergyConstant

theorem lineCommutatorNormConstant_nonneg : 0≤lineCommutatorNormConstant := Real.sqrt_nonneg _

theorem lineCommutatorNormConstant_sq : lineCommutatorNormConstant^2=lineCommutatorEnergyConstant :=
  Real.sq_sqrt lineCommutatorEnergyConstant_nonneg

def lineDerivativeCommutatorToL2 (m b : SchwartzMap ℝ ℂ) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (lineCommutatorToL2 m b).comp (SchwartzMap.derivCLM ℂ ℂ).toLinearMap

theorem lineDerivativeCommutatorToL2_apply (m b h : SchwartzMap ℝ ℂ) :
    lineDerivativeCommutatorToL2 m b h=(lineSchwartzCommutator m b (schwartzDerivative 1 h)).toLp 2 volume := by
  change (lineCommutatorLM m b (schwartzDerivative 1 h)).toLp 2 volume=_
  rw [lineCommutatorLM_apply]

theorem lineDerivativeCommutatorToL2_bound (m b h : SchwartzMap ℝ ℂ)
    (A L : ℝ) (hA : 0≤A)
    (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    ‖lineDerivativeCommutatorToL2 m b h‖≤lineCommutatorNormConstant*A*L*‖h.toLp 2 volume‖ := by
  have hL := (schwartzDerivative_lipschitz_bound b L hLip).1
  have hc := lineSchwartz_lipschitz_commutator_energy m b h A L hA hm hLip
  have hn (f : SchwartzMap ℝ ℂ) : ‖f.toLp 2 volume‖^2=∫ x, ‖f x‖^2 :=
    memLp_toL2_norm_sq volume f (f.memLp 2 volume)
  rw [lineDerivativeCommutatorToL2_apply]
  apply (sq_le_sq₀ (norm_nonneg _) (by have := lineCommutatorNormConstant_nonneg; positivity)).mp
  rw [mul_pow,mul_pow,mul_pow,lineCommutatorNormConstant_sq,hn,hn]
  exact hc

def lineDerivativeCommutatorL2 (m b : SchwartzMap ℝ ℂ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (lineDerivativeCommutatorToL2 m b).extendOfNorm (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap

theorem lineDerivativeCommutatorL2_onSchwartz (m b h : SchwartzMap ℝ ℂ)
    (A L : ℝ) (hA : 0≤A)
    (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    lineDerivativeCommutatorL2 m b (h.toLp 2 volume)=
      (lineSchwartzCommutator m b (schwartzDerivative 1 h)).toLp 2 volume := by
  rw [←lineDerivativeCommutatorToL2_apply]
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · exact ⟨lineCommutatorNormConstant*A*L,fun g =>
      lineDerivativeCommutatorToL2_bound m b g A L hA hm hLip⟩

theorem lineDerivativeCommutatorL2_bound (m b : SchwartzMap ℝ ℂ)
    (A L : ℝ) (hA : 0≤A)
    (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    ‖lineDerivativeCommutatorL2 m b‖≤lineCommutatorNormConstant*A*L := by
  have hL := (schwartzDerivative_lipschitz_bound b L hLip).1
  apply LinearMap.opNorm_extendOfNorm_le
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · have := lineCommutatorNormConstant_nonneg
    positivity
  · exact fun h => lineDerivativeCommutatorToL2_bound m b h A L hA hm hLip

end LipschitzHilbert.PacketRepresentation

end

end OAI
