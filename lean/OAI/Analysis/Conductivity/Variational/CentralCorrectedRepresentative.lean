import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalFiniteEndingData
import OAI.Analysis.Conductivity.Variational.CentralHarmonicOpen
import OAI.Analysis.Conductivity.Flux.VariableBlockTensor
import OAI.Analysis.Conductivity.Fourier.SpectralAffineCovector
import OAI.Analysis.Conductivity.Sobolev.WeylPairGluing

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma H1JetOn.value_cartesian {w : H1} {D : Set Coord3} {f : R3 → JetFiber}
    (hw : H1JetOn w D f) (hDb : ∀ y∈D,WithLp.toLp 2 y∈ball) :
    ∀ᵐ y : Coord3,y∈D → weakValue w (WithLp.toLp 2 y)=f (WithLp.toLp 2 y) 0 := by
  have hh := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' (show MeasurableSet ball from Metric.isOpen_ball.measurableSet)).mp hw)
  filter_upwards [hh] with y hy hyD
  exact congrArg (fun z : JetFiber => z 0) (hy (hDb y hyD) hyD)

lemma centralFullJet_value_ae (s : Fin 3 → ℝ) (p : CentralAmbient s) :
    ∀ᵐ y : Coord3,y∈centralPhysical → centralFullJetCLM s p (WithLp.toLp 2 y) 0=
      centralWholeL2 (centralAmbientComponent s 0 p) (WithLp.toLp 2 y) := by
  have hh := physicalFourJetCLM_ae (fun i => centralPhysicalWholeCLM (centralAmbientComponent s i p))
  have hh' := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' (show MeasurableSet ball from Metric.isOpen_ball.measurableSet)).mp hh)
  have hr := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae
    (centralWholeL2_ae (centralAmbientComponent s 0 p))
  filter_upwards [hh',hr,centralPhysicalWholeCLM_ae (centralAmbientComponent s 0 p)] with y hy hr hc hyC
  change physicalFourJetCLM (fun i => centralPhysicalWholeCLM (centralAmbientComponent s i p))
    (WithLp.toLp 2 y) 0=_
  rw [hy (centralPhysical_subset_ball hyC),hr]
  change centralPhysicalWholeCLM (centralAmbientComponent s 0 p) y=_
  rw [hc]
  change centralPhysical.indicator (fun y => centralAmbientComponent s 0 p (sourcePairCoordinates y)) y=
    centralClosed.indicator (centralAmbientComponent s 0 p) (centralEuclideanCLE (WithLp.toLp 2 y))
  rw [indicator_of_mem hyC,indicator_of_mem (show centralEuclideanCLE (WithLp.toLp 2 y)∈centralClosed from hyC)]
  rfl

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

lemma central_representative {w : Fin 2 → H1}
    (hw : ∀ j,H1JetOn (w j) centralPhysical (centralFullJetCLM s (z.p j).val)) :
    ∃ u : Coord3 → Fin 2 → ℝ,
      ContDiffOn ℝ (↑(⊤:ℕ∞)) u centralStrict ∧
      (∀ᵐ y : Coord3,y∈centralStrict → u y=fun j => weakValue (w j) (WithLp.toLp 2 y)) ∧
      ∀ᵐ y : Coord3,y∈centralStrict → y∈regularRegion u
        (fun _ => ⟨1,Matrix.transpose_one⟩) centralStrict := by
  let U : Set R3 := (WithLp.ofLp : R3 → Coord3) ⁻¹' centralStrict
  have hU : IsOpen U := centralStrict_open.preimage
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).continuous
  obtain ⟨u,hs,he,hr⟩ := weakWeyl_pair_cartesian_representative
    (fun j => centralWholeL2 (centralAmbientComponent s 0 (z.p j).val)) hU
    (fun j => (z.harmonic j).mono centralStrict_harmonic)
  refine ⟨u,hs,?_,hr⟩
  have hj (j : Fin 2) : ∀ᵐ y : Coord3,y∈centralPhysical →
      weakValue (w j) (WithLp.toLp 2 y)=centralWholeL2 (centralAmbientComponent s 0 (z.p j).val) (WithLp.toLp 2 y) := by
    filter_upwards [(hw j).value_cartesian (fun _ => centralPhysical_subset_ball),
      centralFullJet_value_ae s (z.p j).val] with y hw hv hy
    exact (hw hy).trans (hv hy)
  filter_upwards [he,ae_all_iff.mpr hj] with y he hw hy
  rw [he hy]
  funext j
  exact (hw j (centralStrict_subset hy)).symm

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma correctedEndValue_face {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : Fin 2 → spectralTraceGraph (torusRate s)) (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i (fun j => torusSpectralSynthesis s (f j))))
    (j : Fin 2) (a b : ℝ) (m n : Fin 4) {x : Coord3}
    (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) :
    fullAttachedEndValue s (f j) a b (centralBasisSlopes j i) (sourceCollarPiece m n x)+
      attachedPeriodicField (branchCorrection i z j) a b (sourceCollarPiece m n x)=
      variableCollarField (fun y j => branchSplicedField i z j y) a b (sourceCollarPiece m n x) j := by
  rw [variableCollarField_open _ a b m n hx]
  change (attachedEndPoissonField s (f j) a b 0 (sourceCollarPiece m n x)).re+
    (centralBasisSlopes j i)*(a*(sourceCollarTime (sourceCollarPiece m n x)-b))+
    physicalPeriodicField (fun y => branchCorrection i z j (flatEndCoordinates a b y)) (sourceCollarPiece m n x)=_
  rw [attachedEndPoissonField_piece _ _ _ _ _ _ (sourceCollarOpenBox_subset hx),
    physicalPeriodicField_piece ((branchCorrection_periodic i z j).flatEnd a b) m n
      (sourceCollarOpenBox_subset hx),sourceCollarPiece_time_open hx]
  unfold branchSplicedField torusAffineField
  rw [(torusRealContinuation_spectral_eventually hs (f j)
    (show 0<(flatEndCoordinates a b (sourceFaceAngles m n x)) 0 from ht)).eq_of_nhds]
  change _+_+_= (centralBasisSlopes j i)*(a*(x 0-b))+
    (endFlatPoisson s (f j) (endAxialAffine a b (sourceFaceAngles m n x))).re+_
  ring

lemma correctedEndValue_band {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : Fin 2 → spectralTraceGraph (torusRate s)) (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i (fun j => torusSpectralSynthesis s (f j))))
    (j : Fin 2) (a b : ℝ) {l r : ℝ} (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Ioo l r,0<a*(t-b)) :
    ∀ᵐ y∂volume.restrict (sourceClosedCollarBand l r),
      fullAttachedEndValue s (f j) a b (centralBasisSlopes j i) y+
        attachedPeriodicField (branchCorrection i z j) a b y=
        variableCollarField (fun y j => branchSplicedField i z j y) a b y j := by
  apply sourceClosedCollarBand_ae_faces hl hr
  intro m n
  filter_upwards [sourceExtendedBox_open_ae hl hr,sourceExtendedBox_axial_strict_ae l r]
    with x hxo hxt
  exact correctedEndValue_face hs f i z j a b m n hxo (hT _ hxt)

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

def endRepresentative (i : Fin 3) : Coord3 → Fin 2 → ℝ :=
  Fin.cases (variableCollarField (fun y j => branchSplicedField 0 (z.ending 0) j y)
    (z.compression 0) centralThickness)
    (fun k => fun y => variableCollarField (fun y j => branchSplicedField k.succ (z.ending k.succ) j y)
      (z.compression k.succ) (-centralThickness) ((sourceChildHomeomorph (actualChildSign k)).symm y)) i

lemma parent_open_time {t : ℝ} (ht : t∈Ioo 0 centralThickness) :
    0<z.compression 0*(t-centralThickness) := mul_pos_of_neg_of_neg z.compression_parent (sub_neg.mpr ht.2)
lemma child_open_time (k : Fin 2) {t : ℝ} (ht : t∈Ioo (-centralThickness) 0) :
    0<z.compression k.succ*(t-(-centralThickness)) := mul_pos (z.compression_child k) (sub_pos.mpr ht.1)

lemma endRepresentative_value
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2) (i : Fin 3) (j : Fin 2) :
    ∀ᵐ y : Coord3,y∈physicalEndRegion i → z.correctedEndJet j i (WithLp.toLp 2 y) 0=z.endRepresentative i y j := by
  refine Fin.cases ?_ (fun k => ?_) i
  · have hh := correctedEndValue_band hs (fun j => centralT s 0 (z.p j)) 0 (z.ending 0) j
      (z.compression 0) centralThickness (by norm_num : -(1:ℝ)/100≤0)
      (by norm_num [centralThickness] : centralThickness≤(1:ℝ)/100) (fun t => z.parent_open_time)
    exact (ae_restrict_iff' (physicalEndRegion_compact 0).measurableSet).mp hh
  · have hh := correctedEndValue_band hs (fun j => centralT s k.succ (z.p j)) k.succ (z.ending k.succ) j
      (z.compression k.succ) (-centralThickness) (by norm_num [centralThickness] : -(1:ℝ)/100≤-centralThickness)
      (by norm_num : (0:ℝ)≤1/100) (fun t => z.child_open_time k)
    exact (sourceChildInverse_quasi (actualChildSign k)).ae
      ((ae_restrict_iff' childEndBand_measurable).mp hh)

lemma endRepresentative_regular
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (hS : ∀ i y,(variableEndTensor (fun i => branchSplicedTensor i (z.ending i)) z.compression i y).IsSymm)
    (i : Fin 3) : ∀ᵐ y : Coord3,y∈physicalEndRegion i →
      y∈regularRegion (z.endRepresentative i)
        (fun y => ⟨variableEndTensor (fun i => branchSplicedTensor i (z.ending i)) z.compression i y,hS i y⟩) univ := by
  refine Fin.cases ?_ (fun k => ?_) i
  · exact (ae_restrict_iff' (physicalEndRegion_compact 0).measurableSet).mp
      (branchCollar_regular_ae hs 0 (z.ending 0) (z.compression_ne 0)
        (by norm_num : -(1:ℝ)/100≤0) (by norm_num [centralThickness] : centralThickness≤(1:ℝ)/100)
        (fun t => z.parent_open_time))
  · have hh := branchCollar_regular_ae hs k.succ (z.ending k.succ) (z.compression_ne k.succ)
      (by norm_num [centralThickness] : -(1:ℝ)/100≤-centralThickness) (by norm_num : (0:ℝ)≤1/100)
      (fun t => z.child_open_time k)
    have hh' := (sourceChildInverse_quasi (actualChildSign k)).ae
      ((ae_restrict_iff' childEndBand_measurable).mp hh)
    filter_upwards [hh'] with y hy hyE
    have hr := sourceChild_regular_at k
      (variableCollarTensor_symm (branchSplicedTensor_symm k.succ (z.ending k.succ))
        (z.compression k.succ) (-centralThickness)) (hy hyE)
    simpa only [preimage_univ, endRepresentative, variableEndTensor, Fin.cases_succ] using hr

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

end OAI
