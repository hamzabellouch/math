import Mathlib
import OAI.Analysis.Conductivity.Variational.CentralHarmonicOpen
import OAI.Analysis.Conductivity.Flux.VariableBlockTensor

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

def physicalEndOpen (i : Fin 3) : Set Coord3 :=
  Fin.cases {y | sourceCollarTime y∈Ioo 0 centralThickness}
    (fun k => {y | sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)∈Ioo (-centralThickness) 0}) i

lemma physicalEndOpen_open (i : Fin 3) : IsOpen (physicalEndOpen i) := by
  refine Fin.cases ?_ (fun k => ?_) i
  · exact isOpen_Ioo.preimage locallyLipschitz_sourceCollarTime.continuous
  · exact isOpen_Ioo.preimage (locallyLipschitz_sourceCollarTime.continuous.comp
      (sourceChildHomeomorph (actualChildSign k)).symm.continuous)

lemma physicalEndOpen_subset (i : Fin 3) : physicalEndOpen i⊆physicalEndRegion i := by
  refine Fin.cases ?_ (fun k => ?_) i <;> exact fun y hy => ⟨hy.1.le,hy.2.le⟩

lemma physicalEndOpen_conull (i : Fin 3) :
    ∀ᵐ y : Coord3,y∈physicalEndRegion i → y∈physicalEndOpen i := by
  have hn (t : ℝ) (ht : t∈Icc (-(1:ℝ)/100) (1/100)) := sourceColevel_ae_ne ht
  refine Fin.cases ?_ (fun k => ?_) i
  · filter_upwards [hn 0 (by norm_num),hn centralThickness (by norm_num [centralThickness])]
      with y h0 hct hy
    exact ⟨lt_of_le_of_ne hy.1 h0.symm,lt_of_le_of_ne hy.2 hct⟩
  · have hh := (sourceChildInverse_quasi (actualChildSign k))
    filter_upwards [hh.ae (hn 0 (by norm_num)),
      hh.ae (hn (-centralThickness) (by norm_num [centralThickness]))] with y h0 hct hy
    exact ⟨lt_of_le_of_ne hy.1 hct.symm,lt_of_le_of_ne hy.2 h0⟩

lemma centralStrict_no_end {y : Coord3} (hy : y∈centralStrict) (i : Fin 3) :
    y∉physicalEndRegion i := by
  refine Fin.cases ?_ (fun k => ?_) i
  · exact fun he => (not_le.mpr hy.1) he.2
  · exact fun he => (not_le.mpr (hy.2 k)) he.1

lemma variableBlockTensor_centralStrict (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ)
    {y : Coord3} (hy : y∈centralStrict) : variableBlockTensor K a y=1 :=
  variableBlockTensorList_outside K a _ (fun i _ => centralStrict_no_end hy i)

end ScalarConductivity

end
end

end OAI
