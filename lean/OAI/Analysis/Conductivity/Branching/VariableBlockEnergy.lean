import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalBlockEnergySum
import OAI.Analysis.Conductivity.Variational.PhysicalEnergyContinuous
import OAI.Analysis.Conductivity.Flux.VariableBlockTensor

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal
local instance variableBlockEnergyMeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance variableBlockEnergyBorelSpace : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

lemma variableBlockTensor_central_ae (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ) :
    ∀ᵐ y∂(volume : Measure (Fin 3 → ℝ)),y∈centralPhysical → variableBlockTensor K a y=1 := by
  have hparent := sourceColevel_ae_ne
    (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
  have hchild (k : Fin 2) := (sourceChildInverse_quasi (actualChildSign k)).ae
    (sourceColevel_ae_ne
      (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness]))
  filter_upwards [hparent,hchild 0,hchild 1] with y hp hc₀ hc₁ hy
  apply variableBlockTensorList_outside
  intro i _ hi
  have ht := (centralPhysical_time_iff y).mp hy
  have hn (k : Fin 2) : sourceCollarTime
      ((sourceChildHomeomorph (actualChildSign k)).symm y)≠-centralThickness := by
    fin_cases k
    · exact hc₀
    · exact hc₁
  fin_cases i
  · change sourceCollarTime y∈Icc 0 centralThickness at hi
    exact hp (le_antisymm hi.2 ht.1)
  · change sourceCollarTime ((sourceChildHomeomorph (actualChildSign 0)).symm y)
      ∈Icc (-centralThickness) 0 at hi
    exact hn 0 (le_antisymm (ht.2 0) hi.1)
  · change sourceCollarTime ((sourceChildHomeomorph (actualChildSign 1)).symm y)
      ∈Icc (-centralThickness) 0 at hi
    exact hn 1 (le_antisymm (ht.2 1) hi.1)

lemma variableBlockTensor_entry_memLp (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ)
    (hK : ∀ i,Measurable (K i) ∧ (∀ x,(K i x).IsSymm) ∧
      ∃ c C : ℝ,0<c ∧ c≤C ∧ ∀ x v,c*(v ⬝ᵥ v)≤v ⬝ᵥ(K i x*ᵥv) ∧ v ⬝ᵥ(K i x*ᵥv)≤C*(v ⬝ᵥ v))
    (ha : ∀ i,a i≠0) (i j : Fin 3) :
    MemLp (fun y => variableBlockTensor K a y i j) ∞
      (volume : Measure (Fin 3 → ℝ)) := by
  have h := variableBlockTensor_properties K a hK ha
  let heval : (Matrix (Fin 3) (Fin 3) ℝ) →L[ℝ] ℝ :=
    ((ContinuousLinearMap.proj j) : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
      ((ContinuousLinearMap.proj i) : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] (Fin 3 → ℝ))
  exact heval.comp_memLp' h.2.1

theorem variableBlockTensor_weak_integrable (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ)
    (hK : ∀ i,Measurable (K i) ∧ (∀ x,(K i x).IsSymm) ∧
      ∃ c C : ℝ,0<c ∧ c≤C ∧ ∀ x v,c*(v ⬝ᵥ v)≤v ⬝ᵥ(K i x*ᵥv) ∧ v ⬝ᵥ(K i x*ᵥv)≤C*(v ⬝ᵥ v))
    (ha : ∀ i,a i≠0) {D : Set (Fin 3 → ℝ)} (hD : MeasurableSet D)
    (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) (u v : H1) :
    Integrable (fun y => originalPiGradient u y ⬝ᵥ
      (variableBlockTensor K a y*ᵥoriginalPiGradient v y)) (volume.restrict D) := by
  have hrow (i : Fin 3) : MemLp (fun y => ∑ j : Fin 3,
      variableBlockTensor K a y i j*originalPiGradient v y j) 2 (volume.restrict D) := by
    apply memLp_finsetSum
    intro j _
    exact ((variableBlockTensor_entry_memLp K a hK ha i j).restrict D).mul (r := 2)
      (originalPiGradient_memLp_on_ball hD hb v j)
  change Integrable (fun y => ∑ i : Fin 3,originalPiGradient u y i*
    ∑ j : Fin 3,variableBlockTensor K a y i j*originalPiGradient v y j) _
  apply integrable_finsetSum
  intro i _
  exact (originalPiGradient_memLp_on_ball hD hb u i).integrable_mul (hrow i)

lemma variableBlockTensor_end_energy (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ) (i : Fin 3)
    {D : Set (Fin 3 → ℝ)} (hD : MeasurableSet D) (hsub : D⊆physicalEndRegion i)
    (u v : H1) :
    (∫ y in D,originalPiGradient u y ⬝ᵥ
      (variableBlockTensor K a y*ᵥoriginalPiGradient v y))=
    ∫ y in D,originalPiGradient u y ⬝ᵥ
      (variableEndTensor K a i y*ᵥoriginalPiGradient v y) := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hD] with y hy
  rw [variableBlockTensor_local K a i (hsub hy)]

lemma variableBlockTensor_central_energy (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ) (u v : H1) :
    (∫ y in centralPhysical,originalPiGradient u y ⬝ᵥ
      (variableBlockTensor K a y*ᵥoriginalPiGradient v y))=
    ∫ y in centralPhysical,originalPiGradient u y ⬝ᵥ originalPiGradient v y := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (variableBlockTensor_central_ae K a),
    ae_restrict_mem centralPhysical_compact.measurableSet] with y he hy
  rw [he hy,Matrix.one_mulVec]

theorem variableBlockTensor_energy_sum (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ)
    (hK : ∀ i,Measurable (K i) ∧ (∀ x,(K i x).IsSymm) ∧
      ∃ c C : ℝ,0<c ∧ c≤C ∧ ∀ x v,c*(v ⬝ᵥ v)≤v ⬝ᵥ(K i x*ᵥv) ∧ v ⬝ᵥ(K i x*ᵥv)≤C*(v ⬝ᵥ v))
    (ha : ∀ i,a i≠0) (u v : H1) :
    Integrable (fun y => originalPiGradient u y ⬝ᵥ
      (variableBlockTensor K a y*ᵥoriginalPiGradient v y)) (volume.restrict physicalBlockRegion) ∧
    (∫ y in physicalBlockRegion,originalPiGradient u y ⬝ᵥ
      (variableBlockTensor K a y*ᵥoriginalPiGradient v y))=
      (∫ y in centralPhysical,originalPiGradient u y ⬝ᵥ originalPiGradient v y)+
      ∑ i : Fin 3,∫ y in physicalEndRegion i,originalPiGradient u y ⬝ᵥ
        (variableEndTensor K a i y*ᵥoriginalPiGradient v y) := by
  refine ⟨variableBlockTensor_weak_integrable K a hK ha
    physicalBlockRegion_compact.measurableSet (fun _ => physicalBlockRegion_subset_ball) u v,?_⟩
  rw [physicalBlockRegion_integral _
    (variableBlockTensor_weak_integrable K a hK ha centralPhysical_compact.measurableSet
      (fun _ => centralPhysical_subset_ball) u v)
    (fun i => variableBlockTensor_weak_integrable K a hK ha
      (physicalEndRegion_compact i).measurableSet
        (fun _ => physicalEndRegion_subset_ball i) u v),
    variableBlockTensor_central_energy]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact variableBlockTensor_end_energy K a i (physicalEndRegion_compact i).measurableSet
    Subset.rfl u v

lemma variableBlockEnergy_continuous (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ)
    (hK : ∀ i,Measurable (K i) ∧ (∀ x,(K i x).IsSymm) ∧
      ∃ c C : ℝ,0<c ∧ c≤C ∧ ∀ x v,c*(v ⬝ᵥ v)≤v ⬝ᵥ(K i x*ᵥv) ∧ v ⬝ᵥ(K i x*ᵥv)≤C*(v ⬝ᵥ v))
    (ha : ∀ i,a i≠0) (u : H1) :
    Continuous (fun v : H1 => ∫ y in physicalBlockRegion,originalPiGradient u y ⬝ᵥ
      (variableBlockTensor K a y*ᵥoriginalPiGradient v y)) := by
  have h := variableBlockTensorList_properties K a hK ha (Finset.univ : Finset (Fin 3)).toList
  obtain ⟨B,hB,hbound⟩ := h.2.2.2
  apply literal_matrix_energy_continuous _ (fun i j =>
    (measurable_pi_apply j |>.comp ((measurable_pi_apply i).comp h.1)).aestronglyMeasurable)
    B hB.le (fun y i j => ?_) physicalBlockRegion_compact.measurableSet
      (fun _ => physicalBlockRegion_subset_ball) u
  exact (norm_le_pi_norm ((variableBlockTensor K a y) i) j).trans
    ((norm_le_pi_norm (variableBlockTensor K a y) i).trans (hbound y))

end ScalarConductivity

end
end

end OAI
