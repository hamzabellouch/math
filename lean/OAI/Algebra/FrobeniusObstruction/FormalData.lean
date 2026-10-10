import Mathlib
import OAI.Algebra.FrobeniusObstruction.LinearChange

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction

abbrev SlopeVar (d : ℕ) := Fin d × Fin 3
abbrev TangentVar {d : ℕ} (n : Fin d → ℕ) := (i : Fin d) × Fin (n i)
abbrev WallVar {d : ℕ} (n : Fin d → ℕ) (i : Fin d) := Fin 3 ⊕ Fin (n i)
abbrev InternalVar {d : ℕ} (n : Fin d → ℕ) := Bool × TangentVar n
abbrev GraphVar {d : ℕ} (n : Fin d → ℕ) := SlopeVar d ⊕ TangentVar n
abbrev AmbientVar {d : ℕ} (n : Fin d → ℕ) := SlopeVar d ⊕ InternalVar n

def originIdeal (k : Type*) [CommRing k] (ι : Type*) : Ideal (MvPowerSeries ι k) :=
  Ideal.span (Set.range (MvPowerSeries.X : ι → MvPowerSeries ι k))

variable {k : Type*} [Field k] {d : ℕ} (n : Fin d → ℕ)

def plusCoordinates (i : Fin d) : WallVar n i → MvPowerSeries (AmbientVar n) k
  | .inl j => MvPowerSeries.X (.inl (i, j))
  | .inr y => MvPowerSeries.X (.inr (true, ⟨i, y⟩))

def minusCoordinates (i : Fin d) : WallVar n i → MvPowerSeries (AmbientVar n) k
  | .inl _ => 0
  | .inr y => MvPowerSeries.X (.inr (false, ⟨i, y⟩))

def zeroSlopes (i : Fin d) : WallVar n i → MvPowerSeries (Fin (n i)) k
  | .inl _ => 0
  | .inr y => MvPowerSeries.X y

def potential (P : (i : Fin d) → MvPowerSeries (WallVar n i) k) :
    MvPowerSeries (AmbientVar n) k :=
  ∑ i, (MvPowerSeries.subst (plusCoordinates n i) (P i) -
    MvPowerSeries.subst (minusCoordinates n i) (P i))

def slopeDerivative (P : (i : Fin d) → MvPowerSeries (WallVar n i) k)
    (i : Fin d) : MvPowerSeries (Fin (n i)) k :=
  MvPowerSeries.subst (zeroSlopes n i) (MvPowerSeries.pderiv (.inl 0) (P i))

def graphCoordinates (Y : InternalVar n → MvPowerSeries (GraphVar n) k) :
    AmbientVar n → MvPowerSeries (GraphVar n) k
  | .inl a => MvPowerSeries.X (.inl a)
  | .inr c => Y c

def restrictedGradient (P : (i : Fin d) → MvPowerSeries (WallVar n i) k)
    (Y : InternalVar n → MvPowerSeries (GraphVar n) k) (c : InternalVar n) :
    MvPowerSeries (GraphVar n) k :=
  MvPowerSeries.subst (graphCoordinates n Y)
    (MvPowerSeries.pderiv (.inr c) (potential n P))

def gradientIdeal (P : (i : Fin d) → MvPowerSeries (WallVar n i) k)
    (Y : InternalVar n → MvPowerSeries (GraphVar n) k) :
    Ideal (MvPowerSeries (GraphVar n) k) :=
  Ideal.span (Set.range (restrictedGradient n P Y))

def negativeSlopeValue (P : (i : Fin d) → MvPowerSeries (WallVar n i) k)
    (Y : InternalVar n → MvPowerSeries (GraphVar n) k) (i : Fin d) :
    MvPowerSeries (GraphVar n) k :=
  MvPowerSeries.subst (fun j => Y (false, ⟨i, j⟩)) (slopeDerivative n P i)

def slope (i : Fin d) : MvPowerSeries (GraphVar n) k :=
  MvPowerSeries.X (.inl (i, 0))

def swapBlocks (c : InternalVar n) : InternalVar n := (!c.1, c.2)

def tangentMatrix (Y : InternalVar n → MvPowerSeries (GraphVar n) k) :
    Matrix (InternalVar n) (TangentVar n) k :=
  fun c t => MvPowerSeries.constantCoeff (MvPowerSeries.pderiv (.inr t) (Y c))

                                                                     
def complementaryMatrix (Y : InternalVar n → MvPowerSeries (GraphVar n) k) :
    Matrix (InternalVar n) (InternalVar n) k :=
  fun c bt => if bt.1 then tangentMatrix n Y (swapBlocks n c) bt.2
    else tangentMatrix n Y c bt.2

                                                                                            
structure FormalData where
  P : (i : Fin d) → MvPowerSeries (WallVar n i) k
  Y : InternalVar n → MvPowerSeries (GraphVar n) k
  order_three : ∀ i, P i ∈ (originIdeal k (WallVar n i)) ^ 3
  centered : ∀ c, Y c ∈ originIdeal k (GraphVar n)
  complementary : (complementaryMatrix n Y).det ≠ 0
  graph_zero : MvPowerSeries.subst (graphCoordinates n Y) (potential n P) = 0
  positive_cubic : ∀ i j l : Fin d,
    slope n i * slope n j * slope n l ∈ gradientIdeal n P Y
  negative_cubic : ∀ i j l : Fin d,
    negativeSlopeValue n P Y i * negativeSlopeValue n P Y j *
      negativeSlopeValue n P Y l ∈ gradientIdeal n P Y

end BoundaryOnly.FormalObstruction

end

end OAI
