import Mathlib
import OAI.MeasureTheory.Falconer.Estimates.ActualOuterMasks
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Recursion.AssemblyDescriptorList
import OAI.MeasureTheory.FalconerCompletion.Recursion.RecursiveProfileWithOverhead

namespace OAI

/-! Measures and the conditional distance-set completion. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical ENNReal NNReal
variable {n : ℕ}

noncomputable def assemblyClassLaw (μ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (C : Set (EuclideanSpace ℝ (Fin (n+1)))) : Measure (EuclideanSpace ℝ (Fin (n+1))) :=
  (μ C)⁻¹ • μ.restrict C

structure AssemblyClassFamily (ι : Type*) (μ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (N B : ℕ) (chi sig : ℝ) where
  domain : ι → Set (EuclideanSpace ℝ (Fin (n+1)))
  measurable : ∀ i, MeasurableSet (domain i)
  disjoint : Pairwise (fun i j => Disjoint (domain i) (domain j))
  positive : ∀ i, μ (domain i) ≠ 0
  root : ∀ i, domain i ⊆ treeCell []
  mass : ι → ℝ → ℝ
  profile : ∀ i, RegularizedProfileData (assemblyClassLaw μ (domain i)) N B
    ((n+1:ℝ)/2+chi) sig (mass i)

namespace AssemblyClassFamily
variable {ι : Type*} {μ : Measure (EuclideanSpace ℝ (Fin (n+1)))} {N B : ℕ} {chi sig : ℝ}
noncomputable def env (F : AssemblyClassFamily ι μ N B chi sig)
    (kap Ctest : ℝ) (i : ι) : RecursiveEnvironmentND n :=
  ⟨assemblyClassLaw μ (F.domain i),F.mass i,N,sourcePolicyBlock N kap,
    sourceSmoothingLevels sig kap,sig,Ctest⟩
noncomputable def coefficient (F : AssemblyClassFamily ι μ N B chi sig) (i : ι) : ℝ≥0 :=
  (μ (F.domain i)).toNNReal
end AssemblyClassFamily

noncomputable def assemblyPairEntry {ι κ : Type*} {μ ν : Measure (EuclideanSpace ℝ (Fin (n+1)))} {N B : ℕ} {chi sig : ℝ}
    (F : AssemblyClassFamily ι μ N B chi sig) (G : AssemblyClassFamily κ ν N B chi sig)
    (kap Ctest beta : ℝ) (i : ι) (j : κ) : ℕ :=
  GraphLiteralSupport.CurrentFalconer.entryDepthND
    (fun l : Fin 2 => if l=0 then (F.env kap Ctest i).profile else (G.env kap Ctest j).profile) N beta

noncomputable def assemblyPairMask (e₁ e₂ : RecursiveEnvironmentND n) (c : ℕ) (z : (EuclideanSpace ℝ (Fin (n+1))) × (EuclideanSpace ℝ (Fin (n+1)))) : ℝ :=
  (∏ b ∈ assemblyDescriptorList e₁.profile e₁.N e₁.q c,
    actualEndpointMask e₁.ρ e₁.mass e₁.N e₁.sig e₁.C e₁.J 0 b z.1 (radialVector z.1 z.2)) *
  (∏ b ∈ assemblyDescriptorList e₂.profile e₂.N e₂.q c,
    actualEndpointMask e₂.ρ e₂.mass e₂.N e₂.sig e₂.C e₂.J 0 b z.2 (radialVector z.1 z.2))

noncomputable def assemblyTheta {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ ν : Measure (EuclideanSpace ℝ (Fin (n+1)))} {N B : ℕ} {chi sig : ℝ}
    (F : AssemblyClassFamily ι μ N B chi sig) (G : AssemblyClassFamily κ ν N B chi sig)
    (kap Ctest beta : ℝ) (z : (EuclideanSpace ℝ (Fin (n+1))) × (EuclideanSpace ℝ (Fin (n+1)))) : ℝ :=
  ∑ i, ∑ j, (F.domain i ×ˢ G.domain j).indicator
    (assemblyPairMask (F.env kap Ctest i) (G.env kap Ctest j)
      (assemblyPairEntry F G kap Ctest beta i j)) z

noncomputable def assemblyGamma (I : Finset ℕ) (X Y : ℕ → Set (EuclideanSpace ℝ (Fin (n+1)))) : Set ((EuclideanSpace ℝ (Fin (n+1))) × (EuclideanSpace ℝ (Fin (n+1)))) :=
  ⋃ l ∈ I, X l ×ˢ Y l

noncomputable def assemblyTau {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ ν : Measure (EuclideanSpace ℝ (Fin (n+1)))} {N B : ℕ} {chi sig : ℝ}
    (F : AssemblyClassFamily ι μ N B chi sig) (G : AssemblyClassFamily κ ν N B chi sig)
    (kap Ctest beta : ℝ) (I : Finset ℕ) (X Y : ℕ → Set (EuclideanSpace ℝ (Fin (n+1)))) : Measure ℝ :=
  ((μ.prod ν).withDensity (fun z => ENNReal.ofReal
    ((dist z.1 z.2)^(-(n:ℝ)/2) *
      (assemblyGamma I X Y).indicator (assemblyTheta F G kap Ctest beta) z))).map
        (fun z => dist z.1 z.2)
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
