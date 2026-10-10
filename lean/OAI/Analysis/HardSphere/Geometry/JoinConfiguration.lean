import Mathlib
import OAI.Analysis.HardSphere.Geometry.ConfigurationPath

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace
namespace HardSphere
open MeasureTheory Wiener Set Filter
noncomputable section

def joinConfiguration (m n : ℕ) (L : Length)
    (p : Configuration m L × Configuration n L) : Configuration (m+n) L :=
  Fin.addCases p.1 p.2

def splitConfiguration (m n : ℕ) (L : Length) (X : Configuration (m+n) L) :
    Configuration m L × Configuration n L :=
  (fun i ↦ X (Fin.castAdd n i),fun i ↦ X (Fin.natAdd m i))

lemma joinConfiguration_continuous (m n : ℕ) (L : Length) :
    Continuous (joinConfiguration m n L) := by
  apply continuous_pi
  intro i
  induction i using Fin.addCases with
  | left i => simpa only [joinConfiguration,Fin.addCases_left,Function.comp_def] using
      ((continuous_apply i).comp continuous_fst)
  | right i => simpa only [joinConfiguration,Fin.addCases_right,Function.comp_def] using
      ((continuous_apply i).comp continuous_snd)

lemma splitConfiguration_continuous (m n : ℕ) (L : Length) :
    Continuous (splitConfiguration m n L) := by unfold splitConfiguration; fun_prop

@[simp] lemma split_joinConfiguration (m n : ℕ) (L : Length)
    (p : Configuration m L × Configuration n L) :
    splitConfiguration m n L (joinConfiguration m n L p)=p := by
  ext <;> simp [splitConfiguration,joinConfiguration]

@[simp] lemma join_splitConfiguration (m n : ℕ) (L : Length) (X : Configuration (m+n) L) :
    joinConfiguration m n L (splitConfiguration m n L X)=X := by
  ext i j
  induction i using Fin.addCases <;> simp [splitConfiguration,joinConfiguration]

lemma joinConfiguration_preserving (m n : ℕ) (L : Length) :
    MeasurePreserving (joinConfiguration m n L)
      ((volume : Measure (Configuration m L)).prod volume) volume := by
  have h := (volume_measurePreserving_piCongrLeft (fun _ : Fin (m+n) ↦ Torus L)
    (finSumFinEquiv (m:=m) (n:=n))).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ Fin n ↦ Torus L))
  convert h using 1
  try rfl
  funext p i
  induction i using Fin.addCases <;> simp [joinConfiguration,MeasurableEquiv.coe_piCongrLeft,
    MeasurableEquiv.coe_sumPiEquivProdPi_symm,Equiv.piCongrLeft_apply,Equiv.sumPiEquivProdPi_symm_apply]

lemma splitConfiguration_preserving (m n : ℕ) (L : Length) :
    MeasurePreserving (splitConfiguration m n L) volume
      ((volume : Measure (Configuration m L)).prod volume) := by
  refine ⟨(splitConfiguration_continuous m n L).measurable,?_⟩
  rw [← (joinConfiguration_preserving m n L).map_eq,
    Measure.map_map (splitConfiguration_continuous m n L).measurable
      (joinConfiguration_continuous m n L).measurable]
  simp only [Function.comp_def,split_joinConfiguration,Measure.map_id']

def joinConfigurationPath (m n : ℕ) (L : Length)
    (p : ConfigurationPath m L × ConfigurationPath n L) : ConfigurationPath (m+n) L :=
  ⟨fun t ↦ joinConfiguration m n L (p.1 t,p.2 t),
    (joinConfiguration_continuous m n L).comp (p.1.continuous.prodMk p.2.continuous)⟩

def splitConfigurationPath (m n : ℕ) (L : Length) (ω : ConfigurationPath (m+n) L) :
    ConfigurationPath m L × ConfigurationPath n L :=
  (⟨fun t i ↦ ω t (Fin.castAdd n i),by fun_prop⟩,
   ⟨fun t i ↦ ω t (Fin.natAdd m i),by fun_prop⟩)

lemma joinConfigurationPath_continuous (m n : ℕ) (L : Length) :
    Continuous (joinConfigurationPath m n L) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (joinConfiguration_continuous m n L).comp
    ((continuous_fst.fst.eval continuous_snd).prodMk
      (continuous_fst.snd.eval continuous_snd))

lemma splitConfigurationPath_continuous (m n : ℕ) (L : Length) :
    Continuous (splitConfigurationPath m n L) := by
  apply Continuous.prodMk
  all_goals
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply continuous_pi
    intro i
    change Continuous (fun p : ConfigurationPath (m+n) L × Time ↦ p.1 p.2 _)
    exact (continuous_apply _).comp (continuous_fst.eval continuous_snd)

@[simp] lemma split_joinConfigurationPath (m n : ℕ) (L : Length)
    (p : ConfigurationPath m L × ConfigurationPath n L) :
    splitConfigurationPath m n L (joinConfigurationPath m n L p)=p := by
  ext <;> simp [splitConfigurationPath,joinConfigurationPath,joinConfiguration]

@[simp] lemma join_splitConfigurationPath (m n : ℕ) (L : Length)
    (ω : ConfigurationPath (m+n) L) :
    joinConfigurationPath m n L (splitConfigurationPath m n L ω)=ω := by
  apply ContinuousMap.ext
  intro t
  exact join_splitConfiguration m n L (ω t)

lemma measurePreserving_shuffle {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] (μ : Measure A) (ν : Measure B)
    (ξ : Measure C) (ζ : Measure D) [SFinite μ] [SFinite ν] [SFinite ξ] [SFinite ζ] :
    MeasurePreserving (fun p : (A×B)×(C×D) ↦ ((p.1.1,p.2.1),(p.1.2,p.2.2)))
      ((μ.prod ν).prod (ξ.prod ζ)) ((μ.prod ξ).prod (ν.prod ζ)) := by
  have h1 := measurePreserving_prodAssoc μ ν (ξ.prod ζ)
  have h2 := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc ν ξ ζ).symm
  have h3 := (MeasurePreserving.id μ).prod
    ((Measure.measurePreserving_swap (μ:=ν) (ν:=ξ)).prod (MeasurePreserving.id ζ))
  have h4 := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc ξ ν ζ)
  have h5 := (measurePreserving_prodAssoc μ ξ (ν.prod ζ)).symm
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

def directionSumEquiv (m n : ℕ) : Direction m ⊕ Direction n ≃ Direction (m+n) :=
  (Equiv.sumProdDistrib (Fin m) (Fin n) (Fin 3)).symm.trans
    ((finSumFinEquiv (m:=m) (n:=n)).prodCongr (Equiv.refl (Fin 3)))

def joinCoordinatePaths (m n : ℕ) (p : CoordinatePaths m × CoordinatePaths n) : CoordinatePaths (m+n) :=
  fun d ↦ Sum.elim p.1 p.2 ((directionSumEquiv m n).symm d)

lemma joinCoordinatePaths_preserving (m n : ℕ) :
    MeasurePreserving (joinCoordinatePaths m n)
      ((coordinateWiener m).prod (coordinateWiener n)) (coordinateWiener (m+n)) := by
  convert (measurePreserving_piCongrLeft (fun _ : Direction (m+n) ↦ wiener)
    (directionSumEquiv m n)).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Direction m ⊕ Direction n ↦ wiener)) using 1 <;> try rfl
  funext p d
  simp [joinCoordinatePaths,MeasurableEquiv.coe_piCongrLeft,
    MeasurableEquiv.coe_sumPiEquivProdPi_symm,Equiv.piCongrLeft_apply,Equiv.sumPiEquivProdPi_symm_apply]
  cases (directionSumEquiv m n).symm d <;> rfl

lemma freeTrajectory_join (m n : ℕ) (L : Length) (t : ℝ)
    (w : CoordinatePaths m × CoordinatePaths n) (X : Configuration m L × Configuration n L) :
    freeTrajectory (m+n) L t (joinCoordinatePaths m n w) (joinConfiguration m n L X)=
      joinConfigurationPath m n L (freeTrajectory m L t w.1 X.1,freeTrajectory n L t w.2 X.2) := by
  ext s i j
  induction i using Fin.addCases <;>
    simp [freeTrajectory,joinConfigurationPath,joinConfiguration,joinCoordinatePaths,directionSumEquiv]

lemma joinConfigurationPath_preserving (m n : ℕ) (L : Length) (t : ℝ) :
    MeasurePreserving (joinConfigurationPath m n L)
      ((freePathLaw m L t).prod (freePathLaw n L t)) (freePathLaw (m+n) L t) := by
  refine ⟨(joinConfigurationPath_continuous m n L).measurable,?_⟩
  have hj := ((joinCoordinatePaths_preserving m n).prod (joinConfiguration_preserving m n L)).comp
    (measurePreserving_shuffle (coordinateWiener m) (volume : Measure (Configuration m L))
      (coordinateWiener n) (volume : Measure (Configuration n L)))
  simp only [freePathLaw,Measure.map_prod_map _ _ (freeTrajectory_continuous m L t).measurable
    (freeTrajectory_continuous n L t).measurable]
  rw [Measure.map_map (joinConfigurationPath_continuous m n L).measurable
    ((freeTrajectory_continuous m L t).measurable.prodMap (freeTrajectory_continuous n L t).measurable)]
  rw [← hj.map_eq,Measure.map_map (freeTrajectory_continuous (m+n) L t).measurable hj.measurable]
  congr 1
  funext p
  exact (freeTrajectory_join m n L t (p.1.1,p.2.1) (p.1.2,p.2.2)).symm

lemma splitConfigurationPath_preserving (m n : ℕ) (L : Length) (t : ℝ) :
    MeasurePreserving (splitConfigurationPath m n L) (freePathLaw (m+n) L t)
      ((freePathLaw m L t).prod (freePathLaw n L t)) := by
  refine ⟨(splitConfigurationPath_continuous m n L).measurable,?_⟩
  rw [← (joinConfigurationPath_preserving m n L t).map_eq,
    Measure.map_map (splitConfigurationPath_continuous m n L).measurable
      (joinConfigurationPath_continuous m n L).measurable]
  simp only [Function.comp_def,split_joinConfigurationPath,Measure.map_id']

lemma staysAllowed_join_subset_bath (m n : ℕ) (L : Length) (a : ℝ) :
    joinConfigurationPath m n L ⁻¹' staysAllowed (m+n) L a ⊆
      Prod.snd ⁻¹' staysAllowed n L a := by
  rintro ⟨ω,η⟩ h x ⟨s,rfl⟩ i j hij
  have hh := h ⟨s,rfl⟩ (Fin.natAdd m i) (Fin.natAdd m j) (by simpa using hij)
  simpa [joinConfigurationPath,joinConfiguration] using hh
end
end HardSphere

end
end
end

end OAI
