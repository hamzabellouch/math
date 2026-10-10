import Mathlib
import OAI.Analysis.Conductivity.Scalarization.ScalarizationAffineLimit

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology TopologicalSpace Matrix
open scoped ENNReal Matrix.Norms.Elementwise

def smoothVoltageJets (μ : Measure Coord3) (U : Set Coord3) : Set (VoltageJetSpace μ U) :=
  {z | ∃ (v : Coord3 → Fin 2 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) v ∧
    ∃ (hm : MemLp v 2 (μ.restrict U)) (hg : MemLp (voltageGradient v) 2 (μ.restrict U)),
      z = (hm.toLp _,hg.toLp _)}

def voltageH1Jets (μ : Measure Coord3) (U : Set Coord3) :
    Submodule ℝ (VoltageJetSpace μ U) :=
  (Submodule.span ℝ (smoothVoltageJets μ U)).topologicalClosure

lemma zeroVoltageJets_le_H1 (μ : Measure Coord3) (U : Set Coord3) :
    zeroVoltageJets μ U ≤ voltageH1Jets μ U := by
  apply Submodule.topologicalClosure_minimal
  · rintro _ ⟨v,hv,hvc,hvs,hvm,hvg,rfl⟩
    apply (Submodule.span ℝ (smoothVoltageJets μ U)).le_topologicalClosure
    exact Submodule.subset_span ⟨v,hv,hvm,hvg,rfl⟩
  · exact Submodule.isClosed_topologicalClosure _

lemma voltageH1_gradient_mem (μ : Measure Coord3) (U : Set Coord3)
    {z : VoltageJetSpace μ U} (hz : z ∈ voltageH1Jets μ U) :
    z.2 ∈ allVoltageGradients μ U := by
  have hs : voltageH1Jets μ U ≤
      (allVoltageGradients μ U).comap (ContinuousLinearMap.snd ℝ _ _).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨v,hv,hvm,hvg,rfl⟩
      apply (Submodule.span ℝ (smoothVoltageGradients μ U)).le_topologicalClosure
      exact Submodule.subset_span ⟨v,hv,hvg,rfl⟩
    · exact (Submodule.isClosed_topologicalClosure _).preimage continuous_snd
  exact hs hz

lemma divergence_pairing_compact_voltage
    (μ : Measure Coord3) {U : Set Coord3}
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    {z : VoltageJetSpace μ U} (hz : z ∈ compactVoltageJets μ U) :
    inner ℝ z.2 (hF.toLp _) = 0 := by
  obtain ⟨v,hv,hvc,hvs,hvm,hvg,rfl⟩ := hz
  rw [L2.inner_def]
  have he : (∫ x, inner ℝ ((hvg.toLp _) x) ((hF.toLp _) x) ∂μ.restrict U) =
      ∫ x, inner ℝ (voltageGradient v x) (voltageFlux u A x) ∂μ.restrict U := by
    apply integral_congr_ae
    filter_upwards [hvg.coeFn_toLp,hF.coeFn_toLp] with x hx hy
    rw [hx,hy]
  rw [he,setIntegral_eq_integral_of_forall_compl_eq_zero]
  · have hvc' (j) : HasCompactSupport (fun x => v x j) :=
      hvc.comp_left (g := fun v : Fin 2 → ℝ => v j) rfl
    have hvs' (j) : tsupport (fun x => v x j) ⊆ U :=
      (tsupport_comp_subset (g := fun v : Fin 2 → ℝ => v j) rfl v).trans hvs
    have hv' (j) : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => v x j) :=
      (contDiff_apply ℝ ℝ j).comp hv
    simp_rw [voltageFlux,voltageGradient_pairing v (hv.differentiable (by simp))]
    rw [integral_finsetSum _ (fun j _ => hint j _ (hv' j) (hvc' j) (hvs' j))]
    simp only [hdiv _ _ (hv' _) (hvc' _) (hvs' _),Finset.sum_const_zero]
  · intro x hx
    have hg : voltageGradient v x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hs => hx (hvs (tsupport_voltageGradient hs)))
    rw [hg,inner_zero_left]

lemma divergence_pairing_zeroVoltageJets
    (μ : Measure Coord3) {U : Set Coord3}
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    {z : VoltageJetSpace μ U} (hz : z ∈ zeroVoltageJets μ U) :
    inner ℝ z.2 (hF.toLp _) = 0 := by
  apply closure_minimal (s := compactVoltageJets μ U) ?_ ?_ hz
  · exact fun z hz => divergence_pairing_compact_voltage μ hF hint hdiv hz
  · exact isClosed_eq (continuous_snd.inner continuous_const) continuous_const

theorem exact_scalarization_H1
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {U : Set Coord3} (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U)
    [IsFiniteMeasure (μ.restrict U)] [(μ.restrict U).WeaklyRegular]
    [SeparableSpace (Lp FieldVector 2 (μ.restrict U))]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hAm : Measurable A)
    (hu : MemLp u 2 (μ.restrict U))
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (huH1 : (hu.toLp _,hE.toLp _) ∈ voltageH1Jets μ U)
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hreg : μ (U \ regularRegion u A U) = 0)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → A x ∈ matrixFiniteLaminate a b) :
    ∃ (z : voltageH1Jets μ U) (F : Lp FieldVector 2 (μ.restrict U)) (s : Coord3 → ℝ),
      Measurable s ∧ MemLp s ∞ (μ.restrict U) ∧
      z.val-(hu.toLp _,hE.toLp _) ∈ zeroVoltageJets μ U ∧
      (∀ᵐ x ∂μ.restrict U, s x ∈ Icc a b ∧ F x = s x • (z.val.2 x)) ∧
      (∀ W : voltageH1Jets μ U, inner ℝ W.val.2 F = inner ℝ W.val.2 (hF.toLp _)) ∧
      (∀ W : zeroVoltageJets μ U, inner ℝ W.val.2 F = 0) := by
  obtain ⟨v,F,s,hsm,hs,hC⟩ := exact_scalarization_Cauchy_flux μ ha hab hUb hUm u A hAm
    hE hF hint hdiv hreg hgraph
  let z : voltageH1Jets μ U := ⟨(hu.toLp _,hE.toLp _) + v.val,
    (voltageH1Jets μ U).add_mem huH1 (zeroVoltageJets_le_H1 μ U v.property)⟩
  refine ⟨z,F,s,hsm,?_,?_,hs,?_,?_⟩
  · apply memLp_top_of_bound hsm.aestronglyMeasurable b
    filter_upwards [hs] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (ha.le.trans hx.1.1)]
    exact hx.1.2
  · change (hu.toLp _,hE.toLp _) + v.val - (hu.toLp _,hE.toLp _) ∈ _
    rw [add_sub_cancel_left]
    exact v.property
  · intro W
    exact hC _ (voltageH1_gradient_mem μ U W.property)
  · intro W
    rw [hC _ (voltageH1_gradient_mem μ U (zeroVoltageJets_le_H1 μ U W.property))]
    exact divergence_pairing_zeroVoltageJets μ hF hint hdiv W.property

end ScalarConductivity

end
end

end OAI
