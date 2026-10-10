import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Fourier.LawRoot

namespace OAI

/-! Graph energies and pair estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical Topology ENNReal NNReal
variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin (n+1))
namespace AssemblyClassFamily
variable {ι : Type*} {μ : Measure (EuclideanSpace ℝ (Fin (n+1)))} {N B : ℕ} {chi sig : ℝ}
    (F : AssemblyClassFamily ι μ N B chi sig)
lemma law_probability [IsFiniteMeasure μ] (i : ι) :
    IsProbabilityMeasure (assemblyClassLaw μ (F.domain i)) := by
  constructor
  rw [assemblyClassLaw,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply MeasurableSet.univ,
    univ_inter]
  exact ENNReal.inv_mul_cancel (F.positive i) (measure_ne_top _ _)
end AssemblyClassFamily

section Mixture
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {μ ν : Measure (EuclideanSpace ℝ (Fin (n+1)))} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
variable {N B : ℕ} {chi sig : ℝ}
variable (F : AssemblyClassFamily ι μ N B chi sig) (G : AssemblyClassFamily κ ν N B chi sig)
variable (kap Ctest beta : ℝ)

noncomputable def assemblyPairCoefficient (a : ι×κ) : ℝ≥0 := F.coefficient a.1 * G.coefficient a.2

omit [Fintype ι] [Fintype κ] in
lemma assemblyPairCoefficient_prod (a : ι×κ) :
    assemblyPairCoefficient F G a • ((F.env kap Ctest a.1).ρ.prod (G.env kap Ctest a.2).ρ) =
      (μ.prod ν).restrict (F.domain a.1 ×ˢ G.domain a.2) := by
  let := F.law_probability a.1
  let := G.law_probability a.2
  change _ • (assemblyClassLaw μ (F.domain a.1)).prod (assemblyClassLaw ν (G.domain a.2)) = _
  rw [← Measure.prod_restrict,← F.coefficient_law a.1,← G.coefficient_law a.2,
    Measure.prod_smul_left,Measure.prod_smul_right,smul_smul]
  rfl

omit [Fintype ι] [Fintype κ] in
lemma assemblyPairCoefficient_component (a : ι×κ) (X Y : Set V)
    (hX : MeasurableSet X) (hY : MeasurableSet Y) :
    assemblyPairCoefficient F G a • assemblyComponentMeasure (F.env kap Ctest a.1)
      (G.env kap Ctest a.2) (assemblyPairEntry F G kap Ctest beta a.1 a.2) X Y =
      ((μ.prod ν).withDensity ((F.domain a.1 ×ˢ G.domain a.2).indicator
        ((X ×ˢ Y).indicator (fun z => ENNReal.ofReal (assemblySpatialWeight
          (F.env kap Ctest a.1) (G.env kap Ctest a.2)
            (assemblyPairEntry F G kap Ctest beta a.1 a.2) z))))).map
              (fun z => dist z.1 z.2) := by
  let : IsProbabilityMeasure (F.env kap Ctest a.1).ρ := F.law_probability a.1
  let : IsProbabilityMeasure (G.env kap Ctest a.2).ρ := G.law_probability a.2
  rw [assemblyComponentMeasure,← Measure.map_smul _ (by fun_prop)]
  congr 1
  rw [Measure.prod_restrict,ENNReal.smul_def,← withDensity_smul_measure,
    ← Measure.restrict_smul,← ENNReal.smul_def,assemblyPairCoefficient_prod]
  rw [← withDensity_indicator (hX.prod hY),
    ← withDensity_indicator ((F.measurable a.1).prod (G.measurable a.2))]

omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
lemma assembly_density_eq (I : Finset ℕ) (X Y : ℕ → Set V)
    (hdis : Set.Pairwise (↑I : Set ℕ) (fun l m => Disjoint (X l ×ˢ Y l) (X m ×ˢ Y m)))
    (z : V×V) :
    ENNReal.ofReal ((dist z.1 z.2)^(-(n:ℝ)/2) *
      (assemblyGamma I X Y).indicator (assemblyTheta F G kap Ctest beta) z) =
    ∑ a : ι×κ, ∑ l∈I, (F.domain a.1 ×ˢ G.domain a.2).indicator
      ((X l ×ˢ Y l).indicator (fun z => ENNReal.ofReal (assemblySpatialWeight
        (F.env kap Ctest a.1) (G.env kap Ctest a.2)
          (assemblyPairEntry F G kap Ctest beta a.1 a.2) z))) z := by
  have hlocal (S : Set (V×V)) :
      (dist z.1 z.2)^(-(n:ℝ)/2) * S.indicator (assemblyTheta F G kap Ctest beta) z =
      ∑ a : ι×κ, (F.domain a.1 ×ˢ G.domain a.2).indicator
        (S.indicator (assemblySpatialWeight (F.env kap Ctest a.1) (G.env kap Ctest a.2)
          (assemblyPairEntry F G kap Ctest beta a.1 a.2))) z := by
    by_cases hs : z∈S
    · rw [indicator_of_mem hs]
      change (dist z.1 z.2)^(-(n:ℝ)/2) * (∑ i, ∑ j, _) = _
      rw [Finset.mul_sum,Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hd : z∈F.domain i ×ˢ G.domain j
      · simp only [indicator_of_mem hd,indicator_of_mem hs,assemblySpatialWeight]
      · simp only [indicator_of_notMem hd,mul_zero]
    · rw [indicator_of_notMem hs,mul_zero]
      symm
      apply Finset.sum_eq_zero
      intro a ha
      by_cases hd : z∈F.domain a.1 ×ˢ G.domain a.2
      · simp only [indicator_of_mem hd,indicator_of_notMem hs]
      · simp only [indicator_of_notMem hd]
  have hreal : (dist z.1 z.2)^(-(n:ℝ)/2) *
      (assemblyGamma I X Y).indicator (assemblyTheta F G kap Ctest beta) z =
      ∑ a : ι×κ, ∑ l∈I, (F.domain a.1 ×ˢ G.domain a.2).indicator
        ((X l ×ˢ Y l).indicator (assemblySpatialWeight
          (F.env kap Ctest a.1) (G.env kap Ctest a.2)
            (assemblyPairEntry F G kap Ctest beta a.1 a.2))) z := by
    rw [assemblyGamma,Finset.indicator_biUnion_apply I (fun l => X l ×ˢ Y l) hdis,Finset.mul_sum]
    simp_rw [hlocal]
    exact Finset.sum_comm
  rw [hreal,ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro l hl
      by_cases hd : z∈F.domain a.1 ×ˢ G.domain a.2 <;>
        by_cases hx : z∈X l ×ˢ Y l <;> simp [hd,hx]
    · intro l hl
      exact indicator_nonneg (fun z _ => indicator_nonneg (fun z _ => assemblySpatialWeight_nonneg _ _ _ z) z) z
  · intro a ha
    exact Finset.sum_nonneg (fun l hl =>
      indicator_nonneg (fun z _ => indicator_nonneg (fun z _ => assemblySpatialWeight_nonneg _ _ _ z) z) z)

lemma assemblyTau_eq_sum (I : Finset ℕ) (X Y : ℕ → Set V)
    (hXY : ∀ l∈I, MeasurableSet (X l) ∧ MeasurableSet (Y l))
    (hdis : Set.Pairwise (↑I : Set ℕ) (fun l m => Disjoint (X l ×ˢ Y l) (X m ×ˢ Y m))) :
    assemblyTau F G kap Ctest beta I X Y =
      ∑ a : ι×κ, assemblyPairCoefficient F G a •
        (∑ l : I, assemblyComponentMeasure (F.env kap Ctest a.1) (G.env kap Ctest a.2)
          (assemblyPairEntry F G kap Ctest beta a.1 a.2) (X l) (Y l)) := by
  simp only [Finset.smul_sum]
  have hsum (a : ι×κ) :
      (∑ l:I, assemblyPairCoefficient F G a • assemblyComponentMeasure
        (F.env kap Ctest a.1) (G.env kap Ctest a.2)
          (assemblyPairEntry F G kap Ctest beta a.1 a.2) (X l) (Y l)) =
      ∑ l∈I, assemblyPairCoefficient F G a • assemblyComponentMeasure
        (F.env kap Ctest a.1) (G.env kap Ctest a.2)
          (assemblyPairEntry F G kap Ctest beta a.1 a.2) (X l) (Y l) :=
    Finset.sum_coe_sort I (fun l => assemblyPairCoefficient F G a • assemblyComponentMeasure
        (F.env kap Ctest a.1) (G.env kap Ctest a.2)
          (assemblyPairEntry F G kap Ctest beta a.1 a.2) (X l) (Y l))
  simp_rw [hsum]
  have hm (a : ι×κ) (l : ℕ) (hl : l∈I) :=
    assemblyPairCoefficient_component F G kap Ctest beta a (X l) (Y l) (hXY l hl).1 (hXY l hl).2
  have he : (∑ a : ι×κ, ∑ l∈I, assemblyPairCoefficient F G a •
      assemblyComponentMeasure (F.env kap Ctest a.1) (G.env kap Ctest a.2)
      (assemblyPairEntry F G kap Ctest beta a.1 a.2) (X l) (Y l)) =
      ∑ a : ι×κ, ∑ l∈I, ((μ.prod ν).withDensity ((F.domain a.1 ×ˢ G.domain a.2).indicator
        ((X l ×ˢ Y l).indicator (fun z => ENNReal.ofReal (assemblySpatialWeight
          (F.env kap Ctest a.1) (G.env kap Ctest a.2)
            (assemblyPairEntry F G kap Ctest beta a.1 a.2) z))))).map
              (fun z => dist z.1 z.2) := by
    apply Finset.sum_congr rfl
    intro a ha
    exact Finset.sum_congr rfl (fun l hl => hm a l hl)
  rw [he,assemblyTau]
  simp_rw [← Measure.map_finset_sum ((by fun_prop : Measurable (fun z : V×V => dist z.1 z.2)).aemeasurable)]
  congr 1
  ext S hS
  simp only [withDensity_apply _ hS,Measure.finsetSum_apply]
  simp_rw [assembly_density_eq F G kap Ctest beta I X Y hdis]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    exact lintegral_finsetSum I (fun l hl =>
      ((assemblySpatialWeight_measurable _ _ _).ennreal_ofReal.indicator
        ((hXY l hl).1.prod (hXY l hl).2)).indicator ((F.measurable a.1).prod (G.measurable a.2)))
  · intro a ha
    exact Finset.measurable_sum I (fun l hl =>
      ((assemblySpatialWeight_measurable _ _ _).ennreal_ofReal.indicator
        ((hXY l hl).1.prod (hXY l hl).2)).indicator ((F.measurable a.1).prod (G.measurable a.2)))
end Mixture
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
