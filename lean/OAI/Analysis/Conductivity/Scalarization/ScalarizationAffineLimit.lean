import Mathlib
import OAI.Analysis.Conductivity.Scalarization.DenseClosureApprox
import OAI.Analysis.Conductivity.Sobolev.VoltageJetCompletion
import OAI.Analysis.Conductivity.Variational.AffineWeakConstraints
import OAI.Analysis.Conductivity.Flux.VoltageFluxConstraints

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal

lemma CompactGlobalUpdate.gradientCorrection_mem_range
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) :
    (R.memLp_gradient_correction μ).toLp _ ∈ (zeroVoltageGradientMap μ U).range := by
  let hv : MemLp R.du 2 (μ.restrict U) :=
    (R.smooth_du.continuous.memLp_of_hasCompactSupport R.compact_du).restrict U
  let z : VoltageJetSpace μ U := (hv.toLp _,(R.memLp_gradient_correction μ).toLp _)
  have hz : z ∈ compactVoltageJetModule μ U :=
    ⟨R.du,R.smooth_du,R.compact_du,R.support_du,hv,R.memLp_gradient_correction μ,rfl⟩
  exact ⟨⟨z,(compactVoltageJetModule μ U).le_topologicalClosure hz⟩,rfl⟩

lemma finiteUpdateClosure_affine_constraints
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} (hUb : Bornology.IsBounded U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U)) {a b : ℝ}
    {Z : Lp FieldVector 2 (μ.restrict U) × Lp FieldVector 2 (μ.restrict U)}
    (hZ : toWeakSpace ℝ _ Z ∈ closure (toWeakSpace ℝ _ '' finiteUpdatePairs μ U u A hE hF a b)) :
    (∃ v : zeroVoltageJets μ U, Z.1 = hE.toLp _ + v.val.2) ∧
      Z.2-hF.toLp _ ∈ (allVoltageGradients μ U)ᗮ := by
  constructor
  · have hg := submodule_constraint_of_mem_weak_closure
      (zeroVoltageGradientMap μ U).range (zeroVoltageGradientMap_closed_range μ hUb)
      (ContinuousLinearMap.fst ℝ _ _) (hE.toLp _)
      (S := finiteUpdatePairs μ U u A hE hF a b) (z := Z) ?_ hZ
    · obtain ⟨v,hv⟩ := hg
      refine ⟨v,?_⟩
      change v.val.2 = Z.1 - hE.toLp _ at hv
      rw [hv,add_sub_cancel]
    · rintro _ ⟨R,hreg,hgraph,rfl⟩
      change hE.toLp _ + (R.memLp_gradient_correction μ).toLp _ - hE.toLp _ ∈ _
      rw [add_sub_cancel_left]
      exact R.gradientCorrection_mem_range μ
  · apply submodule_constraint_of_mem_weak_closure
      ((allVoltageGradients μ U)ᗮ) (Submodule.isClosed_orthogonal _)
      (ContinuousLinearMap.snd ℝ _ _) (hF.toLp _) (S := finiteUpdatePairs μ U u A hE hF a b) ?_ hZ
    rintro _ ⟨R,hreg,hgraph,rfl⟩
    change hF.toLp _ + (R.memLp_flux_correction μ).toLp _ - hF.toLp _ ∈ _
    rw [add_sub_cancel_left]
    exact R.fluxCorrection_mem_orthogonal μ

theorem exact_scalarization_Cauchy_flux
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {U : Set Coord3} (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U)
    [IsFiniteMeasure (μ.restrict U)] [(μ.restrict U).WeaklyRegular]
    [SeparableSpace (Lp FieldVector 2 (μ.restrict U))]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hAm : Measurable A)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hreg : μ (U \ regularRegion u A U) = 0)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → A x ∈ matrixFiniteLaminate a b) :
    ∃ (v : zeroVoltageJets μ U) (F : Lp FieldVector 2 (μ.restrict U)) (s : Coord3 → ℝ),
      Measurable s ∧
      (∀ᵐ x ∂μ.restrict U, s x ∈ Icc a b ∧ F x = s x • ((hE.toLp _ + v.val.2) x)) ∧
      (∀ W ∈ allVoltageGradients μ U, inner ℝ W F = inner ℝ W (hF.toLp _)) := by
  obtain ⟨Z,s,hZ,hsm,hs⟩ := exact_scalar_in_finiteUpdateClosure μ ha hab hUb hUm u A hAm
    hE hF hint hdiv hreg hgraph
  obtain ⟨⟨v,hv⟩,hFv⟩ := finiteUpdateClosure_affine_constraints μ hUb hE hF hZ
  refine ⟨v,Z.2,s,hsm,?_,?_⟩
  · simpa only [hv] using hs
  · intro W hW
    have he := (Submodule.mem_orthogonal _ _).mp hFv W hW
    rw [inner_sub_right] at he
    exact sub_eq_zero.mp he

end ScalarConductivity

end
end

end OAI
