import Mathlib
import OAI.Analysis.Conductivity.Variational.PhysicalRealTrace

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal
local instance physicalTraceMeanMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalTraceMeanIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma physicalRealTrace_mean (i : Fin 3) (u : H1) :
    (∫ θ,physicalRealTraceCLM i u θ)=(physicalOuterTraceCLM i u 0).re := by
  have he : (mFourierBasis (d:=Fin 2)).repr (physicalComplexTraceCLM i u)=physicalOuterTraceCLM i u :=
    (mFourierBasis (d:=Fin 2)).repr.apply_symm_apply _
  rw [←he,mFourierBasis_repr]
  simp only [mFourierCoeff,neg_zero,mFourier_zero,ContinuousMap.one_apply,one_smul]
  have hi : Integrable (physicalComplexTraceCLM i u) :=
    (Lp.memLp (physicalComplexTraceCLM i u)).integrable (by norm_num)
  calc
    _ = ∫ θ,Complex.reCLM (physicalComplexTraceCLM i u θ) := integral_congr_ae
      (Complex.reCLM.coeFn_compLpL (p:=2) (μ:=volume) (physicalComplexTraceCLM i u))
    _ = _ := Complex.reCLM.integral_comp_comm hi

lemma constantTerminalFlux_realTrace (κ : Fin 3 → ℝ) (u : H1) :
    constantTerminalFluxCLM κ u=angularArea*∑ i : Fin 3,κ i*(∫ θ,physicalRealTraceCLM i u θ) := by
  simp only [constantTerminalFluxCLM,smul_apply,sum_apply,
    ContinuousLinearMap.comp_apply,smul_eq_mul,physicalRealTrace_mean]
  rfl

lemma constantTerminalFlux_zero_of_realTrace (κ : Fin 3 → ℝ) (u : H1)
    (hu : ∀ i : Fin 3,physicalRealTraceCLM i u=0) : constantTerminalFluxCLM κ u=0 := by
  rw [constantTerminalFlux_realTrace]
  have hz (i : Fin 3) : (∫ θ,physicalRealTraceCLM i u θ)=0 := by
    rw [hu i]
    exact (integral_congr_ae (Lp.coeFn_zero ℝ 2 (volume : Measure (UnitAddTorus (Fin 2))))).trans (integral_zero _ _)
  simp [hz]

lemma physicalRealTrace_transition_zero (u : H1) {M : ℝ} (hM : 0≤M)
    (ht : ∀ i : Fin 3,∀ᵐ θ,physicalRealTraceCLM i u θ≤M) :
    ∀ i : Fin 3,physicalRealTraceCLM i ((upperTransition M hM).onH1 u)=0 := by
  intro i
  rw [physicalRealTrace_chain]
  apply Lp.ext
  filter_upwards [(upperTransition M hM).lipschitz.coeFn_compLp (upperTransition M hM).at_zero
    (physicalRealTraceCLM i u),ht i,Lp.coeFn_zero ℝ 2 (volume : Measure (UnitAddTorus (Fin 2)))]
    with θ hx ht hz
  rw [hx,hz]
  exact (upperTransition_zero_iff M hM _).mpr ht

end ScalarConductivity

end
end

end OAI
