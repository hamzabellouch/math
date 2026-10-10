import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalAttachedWeakPDE
import OAI.Analysis.Conductivity.Branching.PhysicalBlockRepresentative
import OAI.Analysis.Conductivity.Flux.PhysicalSplicedGreen
import OAI.Analysis.Conductivity.Sobolev.OriginalPairVoltage
import OAI.Analysis.Conductivity.Flux.PhysicalVoltageFlux

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

def physicalOpenBlock : Set Coord3 := (WithLp.toLp 2) ⁻¹' sourceOpenBlock

lemma physicalOpenBlock_open : IsOpen physicalOpenBlock :=
  sourceOpenBlock_isOpen.preimage
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous

lemma physicalOpenBlock_subset : physicalOpenBlock⊆physicalBlockRegion := by
  rw [physicalBlockRegion_eq_closure_openBlock]
  exact subset_closure

lemma physicalOpenBlock_bounded : Bornology.IsBounded physicalOpenBlock :=
  physicalBlockRegion_compact.isBounded.subset physicalOpenBlock_subset

lemma physicalOpenBlock_subset_ball {y : Coord3} (hy : y∈physicalOpenBlock) :
    WithLp.toLp 2 y∈ball := physicalBlockRegion_subset_ball (physicalOpenBlock_subset hy)

lemma regularRegion_open_restrict {v : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {U V : Set Coord3} (hV : IsOpen V) (_hVU : V⊆U) {y : Coord3}
    (hy : y∈V) (hr : y∈regularRegion v A U) : y∈regularRegion v A V := by
  obtain ⟨O,hOU,hO,hyO⟩ := mem_regularRegion_iff.mp hr
  exact mem_regularRegion_iff.mpr ⟨O∩V,inter_subset_right,hO.mono (hO.1.inter hV)
    inter_subset_left,⟨hyO,hy⟩⟩

lemma regularRegion_conull_open_restrict {v : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {U V : Set Coord3} (hV : IsOpen V) (hVU : V⊆U) (hr : volume (U \ regularRegion v A U)=0) :
    volume (V \ regularRegion v A V)=0 := by
  apply measure_mono_null (t:=U \ regularRegion v A U) ?_ hr
  intro y hy
  exact ⟨hVU hy.1,fun hh => hy.2 (regularRegion_open_restrict hV hVU hy.1 hh)⟩

lemma voltageGradient_original_ae {U : Set Coord3} (hU : MeasurableSet U)
    {w : Fin 2 → H1} {v : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (hd : ∀ᵐ y : Coord3,y∈U → ∀ i : Fin 3,∀ j : Fin 2,
      fderiv ℝ (fun x => v x j) y (Pi.single i 1)=weakGradient (w j) (WithLp.toLp 2 y) i)
    (hr : volume (U \ regularRegion v A U)=0) :
    ∀ᵐ y∂volume.restrict U,∀ i : Fin 3,∀ j : Fin 2,
      voltageGradient v y (i,j)=originalPiGradient (w j) y i := by
  filter_upwards [ae_restrict_of_ae hd,ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hr),
    ae_restrict_mem hU] with y hd hr hy i j
  have hyR : y∈regularRegion v A U := by simpa only [Set.mem_sdiff,hy,true_and,not_not] using hr
  rw [voltageGradient_component (regularRegion_differentiable hyR),hd hy i j]
  rfl

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

lemma cartesianTensor_dot_elliptic
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2) :
    ∃ c C : ℝ,0<c ∧ c<C ∧ ∀ y v,
      c*(v ⬝ᵥ v)≤v ⬝ᵥ((z.cartesianTensor hs y).val*ᵥv) ∧
        v ⬝ᵥ((z.cartesianTensor hs y).val*ᵥv)≤C*(v ⬝ᵥ v) := by
  obtain ⟨c,C,hc,hcC,hb⟩ := (variableBlockTensor_properties z.flatTensor z.compression
    (z.flatTensor_properties hs) z.compression_ne).2.2.2.1
  exact norm_elliptic_to_dot hc hcC hb

lemma cartesianTensor_entry_memLp
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2) (U : Set Coord3) (i j : Fin 3) :
    MemLp (fun y => (z.cartesianTensor hs y).val i j) ∞ (volume.restrict U) :=
  (variableBlockTensor_entry_memLp z.flatTensor z.compression (z.flatTensor_properties hs)
    z.compression_ne i j).restrict U

lemma corrected_voltage_divergence
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (w : Fin 2 → H1)
    (hc : ∀ j,H1JetOn (w j) centralPhysical (centralFullJetCLM s (z.p j).val))
    (he : ∀ j i,H1JetOn (w j) (physicalEndRegion i) (z.correctedEndJet j i))
    (v : Coord3 → Fin 2 → ℝ)
    (hd : ∀ᵐ y∂volume.restrict physicalOpenBlock,∀ i : Fin 3,∀ j : Fin 2,
      voltageGradient v y (i,j)=originalPiGradient (w j) y i)
    (j : Fin 2) {ψ : Coord3 → ℝ} (hψ : ContDiff ℝ (↑(⊤:ℕ∞)) ψ)
    (hψs : tsupport ψ⊆physicalOpenBlock) :
    (∫ y,fderiv ℝ ψ y ((conductivityFlux v (z.cartesianTensor hs) y).col j))=0 := by
  have hzero : ∀ y∉physicalOpenBlock,fderiv ℝ ψ y ((conductivityFlux v (z.cartesianTensor hs) y).col j)=0 := by
    intro y hy
    rw [fderiv_of_notMem_tsupport ℝ (fun hh => hy (hψs hh))]
    rfl
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hg := z.corrected_block_smooth_green hs j (w j) (hc j) (he j) hψ
  rw [constantTerminalFlux_smooth s,show (∑ i : Fin 3,centralBasisSlopes j i*
    spectralGraphMean (torusRate s) (physicalSmoothOuterTrace s hψ i))=0 from by
      simp only [physicalSmoothOuterTrace_compact_zero s hψ hψs,spectralGraphMean,map_zero,mul_zero,
        Finset.sum_const_zero],mul_zero] at hg
  rw [physicalBlockRegion_openBlock_restrict] at hg
  refine (integral_congr_ae ?_).trans hg
  filter_upwards [hd,ae_restrict_of_ae (piSmoothH1_gradient hψ
    (fun _ => physicalOpenBlock_subset_ball)),ae_restrict_mem physicalOpenBlock_open.measurableSet]
    with y hd hp hy
  rw [hp hy,fderiv_flux_eq_sum]
  change (∑ i : Fin 3,fderiv ℝ ψ y (Pi.single i 1)*voltageFlux v (z.cartesianTensor hs) y (i,j))=_
  simp_rw [voltageFlux_component,hd]
  change physicalTestCovector ψ y ⬝ᵥ
    ((z.cartesianTensor hs y).val*ᵥoriginalPiGradient (w j) y)=_
  have hsym : (z.cartesianTensor hs y).valᵀ=(z.cartesianTensor hs y).val :=
    (z.cartesianTensor hs y).property
  have hh := Matrix.dotProduct_transpose_mulVec (z.cartesianTensor hs y).val
    (physicalTestCovector ψ y) (originalPiGradient (w j) y)
  rw [hsym] at hh
  exact hh

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma ae_original_to_cartesian {P : R3 → Prop} (hP : ∀ᵐ x∂ballMeasure,P x) :
    ∀ᵐ y : Coord3,WithLp.toLp 2 y∈ball → P (WithLp.toLp 2 y) :=
  (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' (show MeasurableSet ball from Metric.isOpen_ball.measurableSet)).mp hP)

theorem original_pair_zeroVoltage_extension {U : Set Coord3} (hU : MeasurableSet U)
    (hb : ∀ y∈U,WithLp.toLp 2 y∈ball) (w : Fin 2 → H1) (hw : ∀ j,w j∈H10)
    (Z : VoltageJetSpace volume U)
    (hz : Z-originalPairVoltageJet U w∈zeroVoltageJets volume U) :
    ∃ q : Fin 2 → H1,(∀ j,q j∈H10) ∧
      (∀ j,(q j-w j).val=voltageOriginalJetCLM hU j (Z-originalPairVoltageJet U w)) ∧
      (∀ᵐ y∂volume.restrict U,Z.1 y=fun j => weakValue (q j) (WithLp.toLp 2 y)) ∧
      (∀ᵐ y∂volume.restrict U,∀ i : Fin 3,∀ j : Fin 2,
        Z.2 y (i,j)=originalPiGradient (q j) y i) := by
  have hd (j : Fin 2) := voltage_original_H10_extension hU hb j hz
  choose d hd hdv hdae using hd
  refine ⟨fun j => w j+d j,fun j => H10.add_mem (hw j) (hd j),fun j => ?_,?_,?_⟩
  · rw [add_sub_cancel_left]
    exact hdv j
  · have he := originalPairVoltageJet_ae hU hb w
    filter_upwards [he.1,ae_restrict_of_ae (ae_original_to_cartesian (ae_all_iff.mpr hdae)),
      ae_restrict_of_ae (ae_original_to_cartesian (ae_all_iff.mpr (fun j => weakValue_add (w j) (d j)))),
      Lp.coeFn_sub Z.1 (originalPairVoltageJet U w).1,ae_restrict_mem hU] with y he hd ha hz hy
    ext j
    rw [ha (hb y hy) j]
    change _=weakValue (w j) (WithLp.toLp 2 y)+weakValue (d j) (WithLp.toLp 2 y)
    have hv := (hd (hb y hy) j).1
    simp only [ite_eq_left hy] at hv
    rw [hv]
    change _=weakValue (w j) (WithLp.toLp 2 y)+
      ((Z.1-(originalPairVoltageJet U w).1) y) j
    rw [hz,Pi.sub_apply,he]
    simp
  · have he := originalPairVoltageJet_ae hU hb w
    filter_upwards [he.2,ae_restrict_of_ae (ae_original_to_cartesian (ae_all_iff.mpr hdae)),
      ae_restrict_of_ae (ae_original_to_cartesian (ae_all_iff.mpr (fun j => weakGradient_add (w j) (d j)))),
      Lp.coeFn_sub Z.2 (originalPairVoltageJet U w).2,ae_restrict_mem hU] with y he hd ha hz hy i j
    change _=weakGradient (w j+d j) (WithLp.toLp 2 y) i
    rw [ha (hb y hy) j]
    change _=weakGradient (w j) (WithLp.toLp 2 y) i+weakGradient (d j) (WithLp.toLp 2 y) i
    have hv := (hd (hb y hy) j).2 i
    simp only [ite_eq_left hy] at hv
    rw [hv]
    change _=weakGradient (w j) (WithLp.toLp 2 y) i+
      ((Z.2-(originalPairVoltageJet U w).2) y) (i,j)
    rw [hz,Pi.sub_apply,he]
    change _=originalPiGradient (w j) y i+(Z.2 y (i,j)-originalPiGradient (w j) y i)
    ring

end ScalarConductivity

end
end

end OAI
