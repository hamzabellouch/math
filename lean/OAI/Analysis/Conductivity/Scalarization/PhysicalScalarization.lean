import Mathlib
import OAI.Analysis.Conductivity.Scalarization.OriginalScalarizationCauchy
import OAI.Analysis.Conductivity.Variational.PhysicalOpenVoltage

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

theorem scalar_pair_green_exists
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2) :
    ∃ (σ : Coord3 → ℝ) (c C : ℝ) (w q : Fin 2 → H1),
      Measurable σ ∧ MemLp σ ∞ (volume.restrict physicalOpenBlock) ∧
      0<c ∧ c<C ∧ (∀ᵐ y∂volume.restrict physicalOpenBlock,σ y∈Icc c C) ∧
      (∀ j,q j∈H10) ∧
      (∀ j,H1JetOn (w j) centralPhysical (centralFullJetCLM s (z.p j).val)) ∧
      (∀ j i,H1JetOn (w j) (physicalEndRegion i) (z.correctedEndJet j i)) ∧
      (∃ Z : VoltageJetSpace volume physicalOpenBlock,
        Z-originalPairVoltageJet physicalOpenBlock w∈zeroVoltageJets volume physicalOpenBlock ∧
        ∀ j,(q j-w j).val=voltageOriginalJetCLM physicalOpenBlock_open.measurableSet j
          (Z-originalPairVoltageJet physicalOpenBlock w)) ∧
      ∀ j (h : H1),(∫ y in physicalOpenBlock,σ y*(originalPiGradient (q j) y ⬝ᵥ
        originalPiGradient h y))=constantTerminalFluxCLM (centralBasisSlopes j) h := by
  let : IsFiniteMeasure (volume.restrict physicalOpenBlock) :=
    isFiniteMeasure_restrict.mpr physicalOpenBlock_bounded.measure_lt_top.ne
  let : Fact ((2:ℝ≥0∞)≠∞) := ⟨by norm_num⟩
  obtain ⟨w,hw,hc,he,hgreen⟩ := z.corrected_pair_green_exists hs
  obtain ⟨v,hv,hd,hr⟩ := z.corrected_pair_representative hs w hc he
  have hv' : ∀ᵐ y : Coord3,y∈physicalOpenBlock → v y=fun j => weakValue (w j) (WithLp.toLp 2 y) := by
    filter_upwards [hv] with y hy hyU
    exact hy (physicalOpenBlock_subset hyU)
  have hd' : ∀ᵐ y : Coord3,y∈physicalOpenBlock → ∀ i : Fin 3,∀ j : Fin 2,
      fderiv ℝ (fun x => v x j) y (Pi.single i 1)=weakGradient (w j) (WithLp.toLp 2 y) i := by
    filter_upwards [hd] with y hy hyU
    exact hy (physicalOpenBlock_subset hyU)
  have hr' := regularRegion_conull_open_restrict physicalOpenBlock_open physicalOpenBlock_subset hr
  obtain ⟨hu,hE,hjet,hH1⟩ := original_pair_voltageH1 physicalOpenBlock_open.measurableSet
    (fun _ => physicalOpenBlock_subset_ball) physicalOpenBlock_bounded w v (z.cartesianTensor hs) hv' hd' hr'
  have hg := voltageGradient_original_ae physicalOpenBlock_open.measurableSet hd' hr'
  have hF := voltageFlux_memLp v (z.cartesianTensor hs) hE
    (z.cartesianTensor_entry_memLp hs physicalOpenBlock)
  obtain ⟨l,L,hl,hlL,hb⟩ := z.cartesianTensor_dot_elliptic hs
  obtain ⟨Z,F,σ,hσm,hσL,hzero,hσ,hcau,_⟩ := finite_field_scalarization volume hl hlL.le
    physicalOpenBlock_bounded physicalOpenBlock_open.measurableSet v (z.cartesianTensor hs)
    (z.cartesianTensor_measurable hs) hu hE hF hH1 (smoothFluxIntegrable_of_L2 v _ hF)
    (fun j ψ hψ _ hψs => z.corrected_voltage_divergence hs w hc he v hg j hψ hψs)
    hr' (Filter.Eventually.of_forall (fun y _ => hb y))
  rw [hjet] at hzero
  obtain ⟨q,hq,hqjet,hqv,hqg⟩ := original_pair_zeroVoltage_extension physicalOpenBlock_open.measurableSet
    (fun _ => physicalOpenBlock_subset_ball) w hw Z.val hzero
  refine ⟨σ,laminateLower l L,laminateUpper L,w,q,hσm,hσL,
    (uniform_laminate_coverage hl hlL.le).1,(uniform_laminate_coverage hl hlL.le).2.1,
    hσ.mono (fun _ h => h.1),hq,hc,he,⟨Z.val,hzero,hqjet⟩,?_⟩
  intro j h
  have hcc := scalarization_original_weak_gradient_cauchy physicalOpenBlock_open.measurableSet
    (fun _ => physicalOpenBlock_subset_ball) physicalOpenBlock_bounded hcau h j
  have hlhs : (∫ y,∑ i,weakGradient h (WithLp.toLp 2 y) i*F y (i,j) ∂volume.restrict physicalOpenBlock)=
      ∫ y in physicalOpenBlock,σ y*(originalPiGradient (q j) y ⬝ᵥ originalPiGradient h y) := by
    apply integral_congr_ae
    filter_upwards [hσ,hqg] with y hσ hqg
    rw [hσ.2]
    simp only [PiLp.smul_apply,smul_eq_mul,hqg,dotProduct,Finset.mul_sum,originalPiGradient]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hrhs : (∫ y,∑ i,weakGradient h (WithLp.toLp 2 y) i*(hF.toLp _) y (i,j) ∂volume.restrict physicalOpenBlock)=
      ∫ y in physicalOpenBlock,originalPiGradient (w j) y ⬝ᵥ
        (variableBlockTensor z.flatTensor z.compression y*ᵥoriginalPiGradient h y) := by
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp,hg] with y hF hg
    rw [hF]
    simp_rw [voltageFlux_component,hg]
    change originalPiGradient h y ⬝ᵥ((z.cartesianTensor hs y).val*ᵥoriginalPiGradient (w j) y)=_
    have hsym : (z.cartesianTensor hs y).valᵀ=(z.cartesianTensor hs y).val := (z.cartesianTensor hs y).property
    have hh := Matrix.dotProduct_transpose_mulVec (z.cartesianTensor hs y).val
      (originalPiGradient h y) (originalPiGradient (w j) y)
    rw [hsym] at hh
    exact hh
  rw [hlhs,hrhs] at hcc
  exact hcc.trans (by simpa only [physicalOpenBlock,physicalBlockRegion_openBlock_restrict] using hgreen j h)

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

end OAI
