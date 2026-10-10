import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Graphs.LawProbability
import OAI.MeasureTheory.FalconerCompletion.Measures.AssemblyPositiveEnergy

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
section Mixture
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {μ ν : Measure (EuclideanSpace ℝ (Fin (n+1)))} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
variable {N B : ℕ} {chi sig : ℝ}
variable (F : AssemblyClassFamily ι μ N B chi sig) (G : AssemblyClassFamily κ ν N B chi sig)
variable (kap Ctest beta : ℝ)
lemma assemblyPairCoefficient_sum : (∑ a:ι×κ,(assemblyPairCoefficient F G a:ℝ)) ≤ 1 := by
  simp only [assemblyPairCoefficient,NNReal.coe_mul,Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  exact (mul_le_mul F.coefficient_sum G.coefficient_sum
    (Finset.sum_nonneg (fun _ _ => NNReal.coe_nonneg _)) zero_le_one).trans_eq (mul_one 1)

lemma assemblyTau_positive_energy (I : Finset ℕ) (X Y : ℕ → Set V)
    (hXY : ∀ l∈I, MeasurableSet (X l) ∧ MeasurableSet (Y l))
    (hdis : Set.Pairwise (↑I : Set ℕ) (fun l m => Disjoint (X l ×ˢ Y l) (X m ×ˢ Y m)))
    {δ : ℝ} (hδ : 0<δ) (hsep : ∀ l∈I,∀ x∈X l,∀ y∈Y l,δ≤dist x y)
    (R C : ℝ) (hC : 0≤C)
    (hcomp : ∀ (i : ι) (j : κ) (l : ℕ), l∈I →
      assemblyPositiveEnergy (assemblyComponentMeasure (F.env kap Ctest i) (G.env kap Ctest j)
        (assemblyPairEntry F G kap Ctest beta i j) (X l) (Y l)) R ≤ C) :
    IsFiniteMeasure (assemblyTau F G kap Ctest beta I X Y) ∧
    assemblyPositiveEnergy (assemblyTau F G kap Ctest beta I X Y) R ≤ (I.card:ℝ)^2*C := by
  let τ (a : ι×κ) (l : I) := assemblyComponentMeasure (F.env kap Ctest a.1)
    (G.env kap Ctest a.2) (assemblyPairEntry F G kap Ctest beta a.1 a.2) (X l) (Y l)
  have hf (a : ι×κ) (l : I) : IsFiniteMeasure (τ a l) := by
    let : IsProbabilityMeasure (F.env kap Ctest a.1).ρ := (F.profile a.1).probability
    let : IsProbabilityMeasure (G.env kap Ctest a.2).ρ := (G.profile a.2).probability
    exact assemblyComponentMeasure_finite _ _ _ _ _ (hXY l l.2).1 (hXY l l.2).2 hδ
      (hsep l l.2)
  let := hf
  have hsum (a : ι×κ) : assemblyPositiveEnergy (∑ l:I,τ a l) R ≤ (I.card:ℝ)^2*C := by
    have hh := assemblyPositiveEnergy_sum (τ a) R C (fun l => hcomp a.1 a.2 l l.2)
    simpa only [Fintype.card_coe] using hh
  rw [assemblyTau_eq_sum F G kap Ctest beta I X Y hXY hdis]
  constructor
  · change IsFiniteMeasure (∑ a:ι×κ,assemblyPairCoefficient F G a • (∑ l:I,τ a l))
    infer_instance
  · exact assemblyPositiveEnergy_weighted_sum Finset.univ (assemblyPairCoefficient F G)
      (fun a => ∑ l:I,τ a l) R (assemblyPairCoefficient_sum F G)
      (mul_nonneg (sq_nonneg _) hC) (fun a _ => hsum a)
end Mixture
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
