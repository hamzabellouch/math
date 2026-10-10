import OAI.Probability.CubeShuffle.FourierBound

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace CubeShuffle.WeightedSweep
open Specht UnitaryFinite

def dimension (μ : YoungDiagram) : ℝ := Module.finrank ℂ (space μ)

def sweepLaw (d : ℕ) : Equiv.Perm (Card d) → ℝ := sampleLaw (run d d)

lemma sweepLaw_nonneg (d : ℕ) (g : Equiv.Perm (Card d)) : 0 ≤ sweepLaw d g :=
  sampleLaw_nonneg _ _

lemma sweepLaw_sum (d : ℕ) : ∑ g, sweepLaw d g = 1 := sampleLaw_sum _

def fourierSweep (d : ℕ) (μ : Shapes (2^d)) :
    hilbertSpace μ.1 →L[ℂ] hilbertSpace μ.1 :=
  sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (run d d)

lemma fourierSweep_eq_group_sum (d : ℕ) (μ : Shapes (2 ^ d)) :
    fourierSweep d μ = ∑ g : Equiv.Perm (Card d), (sweepLaw d g : ℂ) •
      continuousRepresentation (V := hilbertSpace μ.1) (cardRepresentation d μ) g := by
  let : NormedAddCommGroup (hilbertSpace μ.1) := inferInstance
  let : InnerProductSpace ℂ (hilbertSpace μ.1) := inferInstance
  let : FiniteDimensional ℂ (hilbertSpace μ.1) := inferInstance
  exact sampleOperator_weighted (V := hilbertSpace μ.1) (cardRepresentation d μ) (run d d)

def schattenMoment {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (A : V →L[ℂ] V) (p : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℂ V), (A.toLinearMap.singularValues i) ^ p

def schattenNorm {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (A : V →L[ℂ] V) (p : ℝ) : ℝ :=
  schattenMoment A p ^ (1 / p)

end CubeShuffle.WeightedSweep

end

end OAI
