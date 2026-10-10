import Mathlib
import OAI.Computability.VertexCover.Analysis.StarEnergyBudget
import OAI.Computability.VertexCover.Reduction.AverageCommute

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Restriction
open MeasureTheory
open scoped BigOperators

def plug {ι X : Type*} [DecidableEq ι] (J : Finset ι) (s t : ι → X) : ι → X :=
  fun i => if i ∈ J then t i else s i

@[simp] theorem plug_empty {ι X : Type*} [DecidableEq ι] (s t : ι → X) :
    plug ∅ s t = s := by funext i; simp [plug]

@[simp] theorem plug_univ {ι X : Type*} [Fintype ι] [DecidableEq ι] (s t : ι → X) :
    plug Finset.univ s t = t := by funext i; simp [plug]

theorem plug_insert_update {ι X : Type*} [DecidableEq ι] (J : Finset ι) (i : ι)
    (hi : i ∉ J) (s t : ι → X) (x : X) :
    plug J (Function.update s i x) t = plug (insert i J) s (Function.update t i x) := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [plug, hi]
  · simp [plug, hk]

theorem continuous_plug_right {ι X : Type*} [DecidableEq ι] [TopologicalSpace X]
    (J : Finset ι) (s : ι → X) : Continuous (plug J s) := by
  apply continuous_pi
  intro i
  by_cases hi : i ∈ J
  · simpa only [plug, ite_eq_left hi] using continuous_apply i
  · simpa only [plug, ite_eq_right hi] using (continuous_const : Continuous (fun _ : ι → X => s i))

namespace EnergyForm.Projection
section Averaging
variable {ι X : Type*} [Fintype ι] [DecidableEq ι]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem product_average_apply (is : List ι) (his : is.Nodup)
    (f : C(ι → X, ℝ)) (s : ι → X) :
    productMap (average μ) is f s =
      ∫ t, f (plug is.toFinset s t) ∂Measure.pi (fun _ : ι => μ) := by
  induction is generalizing s with
  | nil => simp
  | cons i is ih =>
    rcases List.nodup_cons.mp his with ⟨hnot, hn⟩
    have hni : i ∉ is.toFinset := by simpa using hnot
    simp only [productMap_cons, average_apply]
    simp_rw [ih hn]
    simp only [List.toFinset_cons]
    simp_rw [plug_insert_update is.toFinset i hni]
    exact VertexCover.Product.integral_update μ i
      ((f.continuous.comp (continuous_plug_right (insert i is.toFinset) s)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))

noncomputable def averageSet (J : Finset ι) :
    (EnergyForm.integral (Measure.pi (fun _ : ι => μ))).Projection :=
  product (average μ) (average_commute μ) J.toList

@[simp] theorem averageSet_apply (J : Finset ι) (f : C(ι → X, ℝ)) (s : ι → X) :
    averageSet μ J f s = ∫ t, f (plug J s t) ∂Measure.pi (fun _ : ι => μ) := by
  simpa only [averageSet, product_apply, Finset.toList_toFinset] using
    product_average_apply μ J.toList J.nodup_toList f s

@[simp] theorem averageSet_univ (f : C(ι → X, ℝ)) (s : ι → X) :
    averageSet μ Finset.univ f s = ∫ t, f t ∂Measure.pi (fun _ : ι => μ) := by
  simp

end Averaging
end EnergyForm.Projection

theorem restrict_preserving {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (J : Finset ι) :
    MeasurePreserving (fun s : ι → X => fun i : J => s i)
      (Measure.pi (fun _ : ι => μ)) (Measure.pi (fun _ : J => μ)) := by
  classical
  have hp : MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) (fun i => i ∈ J))
      (Measure.pi (fun _ : ι => μ))
      ((Measure.pi (fun _ : J => μ)).prod (Measure.pi (fun _ : {i : ι // i ∉ J} => μ))) := by
    convert measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) (fun i => i ∈ J) using 1
    congr 2
    exact Subsingleton.elim _ _
  exact (measurePreserving_fst (μ := Measure.pi (fun _ : J => μ))
    (ν := Measure.pi (fun _ : {i : ι // i ∉ J} => μ))).comp hp

theorem integral_restrict {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (J : Finset ι)
    {g : (J → X) → ℝ} (hg : AEStronglyMeasurable g (Measure.pi (fun _ : J => μ))) :
    (∫ s, g (fun i : J => s i) ∂Measure.pi (fun _ : ι => μ)) =
      ∫ t, g t ∂Measure.pi (fun _ : J => μ) := by
  have hp := restrict_preserving μ J
  rw [← hp.map_eq] at hg ⊢
  exact (integral_map hp.measurable.aemeasurable hg).symm

def splice {ι X : Type*} [DecidableEq ι] (J : Finset ι) (s : ι → X) (t : J → X) : ι → X :=
  fun i => if h : i ∈ J then t ⟨i,h⟩ else s i

theorem continuous_splice_right {ι X : Type*} [DecidableEq ι] [TopologicalSpace X]
    (J : Finset ι) (s : ι → X) : Continuous (splice J s) := by
  apply continuous_pi
  intro i
  by_cases hi : i ∈ J
  · simpa only [splice, dite_eq_left hi] using continuous_apply (⟨i,hi⟩ : J)
  · simpa only [splice, dite_eq_right hi] using (continuous_const : Continuous (fun _ : J → X => s i))

theorem plug_erase_eq_splice_update {ι X : Type*} [DecidableEq ι]
    (J : Finset ι) (j : J) (s t : ι → X) :
    plug (J.erase j) s t = splice J s (Function.update (fun i : J => t i) j (s j)) := by
  funext i
  by_cases hi : i ∈ J
  · by_cases hij : i = j
    · subst i
      simp [plug, splice]
    · have hij' : (⟨i,hi⟩ : J) ≠ j := fun h => hij (congrArg Subtype.val h)
      simp [plug, splice, hi, hij, hij']
  · simp [plug, splice, hi]

theorem integral_plug_erase {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (J : Finset ι) (j : J)
    (f : C(ι → X, ℝ)) (s : ι → X) :
    (∫ t, f (plug (J.erase j) s t) ∂Measure.pi (fun _ : ι => μ)) =
      ∫ t, f (splice J s (Function.update t j (s j))) ∂Measure.pi (fun _ : J => μ) := by
  simp_rw [plug_erase_eq_splice_update J j s]
  apply integral_restrict μ J (g := fun t => f (splice J s (Function.update t j (s j))))
  exact (f.continuous.comp ((continuous_splice_right J s).comp
    (continuous_id.update j continuous_const))).measurable.aestronglyMeasurable

namespace CompactCube

abbrev Interval := Set.Icc (-1 : ℝ) 1

noncomputable def intervalLaw : Measure Interval :=
  VertexCover.Cube.intervalLaw.comap Subtype.val

theorem ae_interval_mem : ∀ᵐ x ∂VertexCover.Cube.intervalLaw, x ∈ Set.Icc (-1 : ℝ) 1 := by
  filter_upwards [VertexCover.Cube.ae_interval] with x hx
  exact (abs_le.mp hx)

instance : IsProbabilityMeasure intervalLaw :=
  (MeasurableEmbedding.subtype_coe measurableSet_Icc).isProbabilityMeasure_comap
    (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using ae_interval_mem)

theorem interval_preserving : MeasurePreserving (Subtype.val : Interval → ℝ)
    intervalLaw VertexCover.Cube.intervalLaw := by
  refine ⟨measurable_subtype_coe, ?_⟩
  rw [intervalLaw, (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_comap]
  simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using
    Measure.restrict_eq_self_of_ae_mem ae_interval_mem

noncomputable def law (ι : Type*) [Fintype ι] : Measure (ι → Interval) :=
  Measure.pi (fun _ : ι => intervalLaw)

instance {ι : Type*} [Fintype ι] : IsProbabilityMeasure (law ι) := by
  unfold law
  infer_instance

def realWeights {ι κ : Type*} (s : ι → κ → Interval) : ι → κ → ℝ :=
  fun i k => (s i k).1

theorem continuous_realWeights {ι κ : Type*} :
    Continuous (realWeights (ι := ι) (κ := κ)) :=
  continuous_pi (fun i => continuous_pi (fun k =>
    continuous_subtype_val.comp ((continuous_apply k).comp (continuous_apply i))))

theorem law_preserving {ι : Type*} [Fintype ι] :
    MeasurePreserving (fun s : ι → Interval => fun i => (s i).1)
      (law ι) (VertexCover.Cube.law ι) :=
  measurePreserving_pi _ _ (fun _ => interval_preserving)

noncomputable def blockLaw (ι κ : Type*) [Fintype ι] [Fintype κ] :
    Measure (ι → κ → Interval) := Measure.pi (fun _ : ι => law κ)

instance {ι κ : Type*} [Fintype ι] [Fintype κ] : IsProbabilityMeasure (blockLaw ι κ) := by
  unfold blockLaw
  infer_instance

theorem blockLaw_preserving {ι κ : Type*} [Fintype ι] [Fintype κ] :
    MeasurePreserving (realWeights (ι := ι) (κ := κ))
      (blockLaw ι κ) (VertexCover.Cube.blockLaw ι κ) :=
  measurePreserving_pi _ _ (fun _ => law_preserving)

theorem integral_realWeights {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : (ι → κ → ℝ) → ℝ} (hf : AEStronglyMeasurable f (VertexCover.Cube.blockLaw ι κ)) :
    (∫ s, f (realWeights s) ∂blockLaw ι κ) =
      ∫ s, f s ∂VertexCover.Cube.blockLaw ι κ := by
  have hp := blockLaw_preserving (ι := ι) (κ := κ)
  rw [← hp.map_eq] at hf ⊢
  exact (integral_map hp.measurable.aemeasurable hf).symm

theorem integral_coe {ι : Type*} [Fintype ι]
    {f : (ι → ℝ) → ℝ} (hf : AEStronglyMeasurable f (VertexCover.Cube.law ι)) :
    (∫ s, f (fun i => (s i).1) ∂law ι) = ∫ s, f s ∂VertexCover.Cube.law ι := by
  have hp := law_preserving (ι := ι)
  rw [← hp.map_eq] at hf ⊢
  exact (integral_map hp.measurable.aemeasurable hf).symm

end CompactCube
end VertexCover.Restriction


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
