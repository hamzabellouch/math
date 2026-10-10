import Mathlib
import OAI.Analysis.Conductivity.Variational.FieldMean

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped ENNReal Matrix.Norms.Elementwise

lemma voltageGradient_sum
    {I : Type*} [Fintype I] (u : I → Coord3 → Fin 2 → ℝ)
    (hu : ∀ i, Differentiable ℝ (u i)) (x : Coord3) :
    voltageGradient (fun y => ∑ i, u i y) x = ∑ i, voltageGradient (u i) x := by
  classical
  unfold voltageGradient
  rw [fderiv_fun_sum (fun i _ => hu i x),map_sum]

lemma CompactGlobalUpdate.gradient_mean_zero_restrict
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) :
    (∫ x, voltageGradient R.du x ∂μ.restrict U) = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact voltageGradient_mean_zero μ R.smooth_du R.compact_du
  · intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun hs => hx (R.support_du (tsupport_voltageGradient hs)))

lemma CompactGlobalUpdate.flux_mean_zero_restrict
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) :
    (∫ x, fieldVector (R.dF x) ∂μ.restrict U) = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact R.flux_mean_zero μ
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hs => hx (R.support_dF hs))]
    exact map_zero fieldVectorCLM

lemma CompactGlobalUpdate.memLp_gradient_correction
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) :
    MemLp (voltageGradient R.du) 2 (μ.restrict U) :=
  (memLp_voltageGradient_smooth_compact μ R.smooth_du R.compact_du).restrict U

lemma CompactGlobalUpdate.memLp_flux_correction
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) :
    MemLp (fun x => fieldVector (R.dF x)) 2 (μ.restrict U) :=
  ((R.smooth_dF.continuous.memLp_of_hasCompactSupport R.compact_dF).continuousLinearMap_comp fieldVectorCLM).restrict U

lemma CompactGlobalUpdate.gradient_toLp_eq
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} (hUm : MeasurableSet U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) (hreg : μ (U \ regularRegion u A U) = 0)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hE' : MemLp (voltageGradient (fun x => u x+R.du x)) 2 (μ.restrict U)) :
    hE'.toLp _ = hE.toLp _ + (R.memLp_gradient_correction μ).toLp _ := by
  rw [← MemLp.toLp_add]
  exact hE'.toLp_congr _ (R.gradient_add_ae μ hUm hreg)

lemma CompactGlobalUpdate.flux_toLp_eq
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A)
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (hF' : MemLp (voltageFlux (fun x => u x+R.du x) R.tensor) 2 (μ.restrict U)) :
    hF'.toLp _ = hF.toLp _ + (R.memLp_flux_correction μ).toLp _ := by
  rw [← MemLp.toLp_add]
  apply hF'.toLp_congr
  exact Eventually.of_forall fun x => by
    simp only [voltageFlux,R.constitutive x,fieldVector_add,Pi.add_apply]

lemma norm_correction_bound_of_add
    {V : Type*} [NormedAddCommGroup V] (E E₀ dE : V) (M : ℝ)
    (he : E = E₀ + dE) (hbound : ‖E‖ ≤ M) : ‖dE‖ ≤ M + ‖E₀‖ := by
  have hd : dE = E - E₀ := by rw [he, add_sub_cancel_left]
  rw [hd]
  exact (norm_sub_le _ _).trans (add_le_add hbound le_rfl)

lemma CompactGlobalUpdate.correction_energy_bound
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} (hUm : MeasurableSet U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) (hreg : μ (U \ regularRegion u A U) = 0)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → R.tensor x ∈ matrixFiniteLaminate a b) :
    ‖(R.memLp_gradient_correction μ).toLp _‖ ≤ (b/a+1)*‖hE.toLp _‖ ∧
      ‖(R.memLp_flux_correction μ).toLp _‖ ≤ (b^2/a)*‖hE.toLp _‖+‖hF.toLp _‖ := by
  obtain ⟨hE',hF'⟩ := R.fields_memLp μ hUm hreg hE hF
  obtain ⟨hEB,hFB⟩ := R.Lp_energy_bound μ hUm hreg hE hE' hF' hint hdiv ha hab hgraph
  have he := R.gradient_toLp_eq μ hUm hreg hE hE'
  have hf := R.flux_toLp_eq μ hF hF'
  constructor
  · have h := norm_correction_bound_of_add _ _ _ _ he hEB
    simpa only [add_mul, one_mul] using h
  · exact norm_correction_bound_of_add _ _ _ _ hf hFB

end ScalarConductivity

end
end

end OAI
