import OAI.Probability.PosteriorReplicas.Information.ConditionalPiKL
import OAI.Probability.PosteriorReplicas.Information.FiniteKL
import OAI.Probability.PosteriorReplicas.Information.GraphKL

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

def mutualInformation {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (q : Measure (X × Y)) : ℝ≥0∞ := klDiv q (q.fst.prod q.snd)

def totalCorrelation {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (q : Measure (Fin n → Y)) : ℝ≥0∞ := klDiv q (marginalProduct q)

lemma snd_compProd_map {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) [SFinite μ] (κ : Kernel X Y) [IsSFiniteKernel κ]
    {g : Y → Z} (hg : Measurable g) :
    (μ ⊗ₘ κ.map g).snd = (μ ⊗ₘ κ).snd.map g := by
  rw [Measure.compProd_map hg, Measure.snd, Measure.map_map measurable_snd (by fun_prop),
    Measure.snd, Measure.map_map hg measurable_snd]
  rfl

lemma mutualInformation_swap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (q : Measure (X × Y)) [IsProbabilityMeasure q] :
    mutualInformation (q.map Prod.swap) = mutualInformation q := by
  unfold mutualInformation
  rw [Measure.fst_map_swap, Measure.snd_map_swap, ← Measure.prod_swap, klDiv_swap]

section Coordinates
variable {W Y : Type*} [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y] {n : ℕ}
  (μ : Measure W) [IsProbabilityMeasure μ] (κ : Kernel W (Fin n → Y)) [IsMarkovKernel κ]

def coordinateJoint (i : Fin n) : Measure (Y × W) :=
  (μ ⊗ₘ coordKernel κ i).map Prod.swap

instance coordinateJoint_probability (i : Fin n) : IsProbabilityMeasure (coordinateJoint μ κ i) := by
  unfold coordinateJoint
  infer_instance

omit [StandardBorelSpace W] [Nonempty W] [StandardBorelSpace Y] [Nonempty Y] in
lemma coordinateJoint_fst (i : Fin n) :
    (coordinateJoint μ κ i).fst = coordinateMarginal (μ ⊗ₘ κ).snd i := by
  rw [coordinateJoint, Measure.fst_map_swap, coordKernel, snd_compProd_map _ _ (measurable_pi_apply i)]
  rfl

omit [StandardBorelSpace W] [Nonempty W] [StandardBorelSpace Y] [Nonempty Y] in
lemma coordinateJoint_snd (i : Fin n) : (coordinateJoint μ κ i).snd = μ := by
  rw [coordinateJoint, Measure.snd_map_swap, Measure.fst_compProd]

omit [StandardBorelSpace W] [Nonempty W] [StandardBorelSpace Y] [Nonempty Y] in
lemma coordinateJoint_information (i : Fin n) :
    mutualInformation (coordinateJoint μ κ i) =
      klDiv (μ ⊗ₘ coordKernel κ i) (μ.prod (coordinateMarginal (μ ⊗ₘ κ).snd i)) := by
  rw [coordinateJoint, mutualInformation_swap, mutualInformation, Measure.fst_compProd,
    coordKernel, snd_compProd_map _ _ (measurable_pi_apply i)]
  rfl

lemma tuple_information_decomposition :
    conditionalTotalCorrelation μ κ + ∑ i, mutualInformation (coordinateJoint μ κ i) =
      totalCorrelation (μ ⊗ₘ κ).snd + mutualInformation (μ ⊗ₘ κ) := by
  simp_rw [coordinateJoint_information]
  simpa only [totalCorrelation, mutualInformation, Measure.fst_compProd] using
    conditionalTotalCorrelation_identity μ κ

end Coordinates

section Projection
variable {W Y Z : Type*} [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z] {n : ℕ}
  (μ : Measure W) [IsProbabilityMeasure μ] (κ : Kernel W (Fin n → Y)) [IsMarkovKernel κ]
  {g : Y → Z} (hg : Measurable g)
include hg

omit [StandardBorelSpace W] [Nonempty W] [StandardBorelSpace Y] [Nonempty Y]
  [StandardBorelSpace Z] [Nonempty Z] in
lemma coordinateJoint_projection (i : Fin n) :
    coordinateJoint μ (κ.map (fun u j => g (u j))) i =
      (coordinateJoint μ κ i).map (fun z => (g z.1,z.2)) := by
  unfold coordinateJoint coordKernel
  rw [Measure.compProd_map (measurable_pi_apply i),
    Measure.compProd_map (show Measurable (fun u : Fin n → Y => fun j => g (u j)) by fun_prop),
    Measure.compProd_map (measurable_pi_apply i)]
  repeat rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

omit [StandardBorelSpace Z] [Nonempty Z] in
lemma coordinate_information_chain (i : Fin n) :
    mutualInformation (coordinateJoint μ κ i) =
      cmi (attachSide g (coordinateJoint μ κ i)) +
      mutualInformation (coordinateJoint μ (κ.map (fun u j => g (u j))) i) := by
  have h := mutualInformation_attachSide_chain hg (coordinateJoint μ κ i)
  dsimp only at h
  rw [coordinateJoint_projection μ κ hg]
  unfold mutualInformation
  have hfst : ((coordinateJoint μ κ i).map (fun z => (g z.1,z.2))).fst =
      (coordinateJoint μ κ i).fst.map g := by
    rw [Measure.fst, Measure.map_map measurable_fst (by fun_prop),
      Measure.fst, Measure.map_map hg measurable_fst]
    rfl
  have hsnd : ((coordinateJoint μ κ i).map (fun z => (g z.1,z.2))).snd =
      (coordinateJoint μ κ i).snd := by
    rw [Measure.snd, Measure.map_map measurable_snd (by fun_prop)]
    rfl
  rwa [hfst, hsnd]

lemma replica_information_inequality :
    (∑ i, cmi (attachSide g (coordinateJoint μ κ i))) +
      totalCorrelation ((μ ⊗ₘ κ).snd.map (fun u i => g (u i))) ≤
      totalCorrelation (μ ⊗ₘ κ).snd + mutualInformation (μ ⊗ₘ κ) := by
  let κ' := κ.map (fun u i => g (u i))
  have : IsMarkovKernel κ' := Kernel.IsMarkovKernel.map _ (by fun_prop)
  have hc := conditionalTotalCorrelation_map_le μ κ hg
  have h := tuple_information_decomposition μ κ
  have h' := tuple_information_decomposition μ κ'
  have hm : (μ ⊗ₘ κ').snd = (μ ⊗ₘ κ).snd.map (fun u i => g (u i)) :=
    snd_compProd_map _ _ (by fun_prop)
  rw [← hm, ← h]
  have hs : (∑ i, mutualInformation (coordinateJoint μ κ i)) =
      (∑ i, cmi (attachSide g (coordinateJoint μ κ i))) +
      ∑ i, mutualInformation (coordinateJoint μ κ' i) := by
    simp_rw [coordinate_information_chain μ κ hg, Finset.sum_add_distrib]
    rfl
  rw [hs]
  calc
    _ ≤ (∑ i, cmi (attachSide g (coordinateJoint μ κ i))) +
        (totalCorrelation (μ ⊗ₘ κ').snd + mutualInformation (μ ⊗ₘ κ')) :=
      add_le_add le_rfl le_self_add
    _ = (∑ i, cmi (attachSide g (coordinateJoint μ κ i))) +
        (conditionalTotalCorrelation μ κ' + ∑ i, mutualInformation (coordinateJoint μ κ' i)) := by
      rw [h']
    _ ≤ (∑ i, cmi (attachSide g (coordinateJoint μ κ i))) +
        (conditionalTotalCorrelation μ κ + ∑ i, mutualInformation (coordinateJoint μ κ' i)) :=
      add_le_add le_rfl (add_le_add hc le_rfl)
    _ = _ := by ac_rfl

lemma replica_information_le_entropy [Fintype W] [MeasurableSingletonClass W] :
    (∑ i, cmi (attachSide g (coordinateJoint μ κ i))) +
      totalCorrelation ((μ ⊗ₘ κ).snd.map (fun u i => g (u i))) ≤
      totalCorrelation (μ ⊗ₘ κ).snd + ENNReal.ofReal (finiteEntropy μ) := by
  apply (replica_information_inequality μ κ hg).trans
  refine add_le_add le_rfl ?_
  have : IsProbabilityMeasure ((μ ⊗ₘ κ).map Prod.swap) := inferInstance
  have h := mutualInformation_le_finiteEntropy ((μ ⊗ₘ κ).map Prod.swap)
  change mutualInformation ((μ ⊗ₘ κ).map Prod.swap) ≤ _ at h
  simpa only [mutualInformation_swap, Measure.snd_map_swap, Measure.fst_compProd] using h

end Projection
end PosteriorReplicas
end

end OAI
