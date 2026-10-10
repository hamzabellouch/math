import OAI.MathematicalPhysics.Transonic.Phase.RadialFlux

namespace OAI

section
noncomputable section
namespace SepticProfile
open Set
open scoped ContDiff BigOperators

abbrev PhysicalFunction := ℝ → PhysicalSpace → ℝ

def partialTime (s : PhysicalFunction) (t : ℝ) (X : PhysicalSpace) : ℝ :=
  deriv (fun q => s q X) t
def partialSpace (s : PhysicalFunction) (j : Fin 4) (t : ℝ) (X : PhysicalSpace) : ℝ :=
  deriv (fun r => s t (coordinateLine X j r)) 0
def minkowskiPair (s f : PhysicalFunction) (t : ℝ) (X : PhysicalSpace) : ℝ :=
  partialTime s t X*partialTime f t X-
    ∑ j : Fin 4, partialSpace s j t X*partialSpace f j t X

def phaseTransport (s : PhysicalFunction) (t : ℝ) (X : PhysicalSpace) : ℝ :=
  partialTime (fun q Z => (minkowskiSquare s q Z)^((1:ℝ)/3)*partialTime s q Z) t X-
    ∑ j : Fin 4, partialSpace (fun q Z =>
      (minkowskiSquare s q Z)^((1:ℝ)/3)*partialSpace s j q Z) j t X

def GlobalProfile.w0 (P : GlobalProfile) (t : ℝ) (X : PhysicalSpace) : ℝ :=
  (minkowskiSquare P.s0 t X)^((1:ℝ)/6)

def GlobalProfile.linearizedPhase (P : GlobalProfile) (f : PhysicalFunction)
    (t : ℝ) (X : PhysicalSpace) : ℝ :=
  partialTime (fun q Z => (P.w0 q Z)^2*partialTime f q Z+
    (2/3:ℝ)*(P.w0 q Z)^(-4:ℤ)*minkowskiPair P.s0 f q Z*partialTime P.s0 q Z) t X-
    ∑ j : Fin 4, partialSpace (fun q Z => (P.w0 q Z)^2*partialSpace f j q Z+
      (2/3:ℝ)*(P.w0 q Z)^(-4:ℤ)*minkowskiPair P.s0 f q Z*partialSpace P.s0 j q Z) j t X

def InProfileSpace (a : ℝ) (f : PhysicalFunction) : Prop :=
  ∃ (N : ℕ) (F : ℕ → ℝ → ℝ),
    (∀ j≤N, ContDiffOn ℝ ∞ (F j) (Ici 0)) ∧
    ∀ t : ℝ, 0<t → ∀ X : PhysicalSpace,
      f t X=t^a*∑ j∈Finset.range (N+1), (Real.log t)^j*F j (radiusSq X/t^2)

def ProfileSurjectivity (P : GlobalProfile) : Prop :=
  ∀ (a : ℝ) (f : PhysicalFunction), InProfileSpace (a-2-2*P.beta/3) f →
    ∃ phi : PhysicalFunction, InProfileSpace a phi ∧
      ∀ t : ℝ, 0<t → ∀ X : PhysicalSpace, P.linearizedPhase phi t X=f t X

def FullProfileInputExists : Prop :=
  ∃ P : GlobalProfile, (∀ t : ℝ, 0<t → ∀ X : PhysicalSpace,
    0 < minkowskiSquare P.s0 t X ∧ phaseTransport P.s0 t X=0) ∧ ProfileSurjectivity P

end SepticProfile

end
end

end OAI
