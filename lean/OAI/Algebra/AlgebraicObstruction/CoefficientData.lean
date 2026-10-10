import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.CoefficientRing

abbrev SlopeVar (d : ℕ) := Fin d × Fin 3
abbrev TangentVar {d : ℕ} (n : Fin d → ℕ) := (i : Fin d) × Fin (n i)
abbrev WallVar {d : ℕ} (n : Fin d → ℕ) (i : Fin d) := Fin 3 ⊕ Fin (n i)
abbrev InternalVar {d : ℕ} (n : Fin d → ℕ) := Bool × TangentVar n
abbrev GraphVar {d : ℕ} (n : Fin d → ℕ) := SlopeVar d ⊕ TangentVar n
abbrev AmbientVar {d : ℕ} (n : Fin d → ℕ) := SlopeVar d ⊕ InternalVar n

def originIdeal (k : Type*) [CommRing k] (ι : Type*) : Ideal (MvPowerSeries ι k) :=
  Ideal.span (Set.range (MvPowerSeries.X : ι → MvPowerSeries ι k))

variable {k : Type*} [CommRing k] {d : ℕ} (n : Fin d → ℕ)

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
  complementary : IsUnit (complementaryMatrix n Y).det
  graph_zero : MvPowerSeries.subst (graphCoordinates n Y) (potential n P) = 0
  positive_cubic : ∀ i j l : Fin d,
    slope n i * slope n j * slope n l ∈ gradientIdeal n P Y
  negative_cubic : ∀ i j l : Fin d,
    negativeSlopeValue n P Y i * negativeSlopeValue n P Y j *
      negativeSlopeValue n P Y l ∈ gradientIdeal n P Y

end BoundaryOnly.FormalObstruction.CoefficientRing

namespace BoundaryOnly.FormalObstruction.CoefficientRing
open MvPowerSeries
variable {R S ι κ : Type*} [CommRing R] [CommRing S]

 theorem map_partial (f : R →+* S) (i : ι) (P : MvPowerSeries ι R) :
    MvPowerSeries.map f (pderiv i P) = pderiv i (MvPowerSeries.map f P) := by
  classical
  ext e
  simp only [coeff_map, coeff_pderiv, map_mul, map_add, map_natCast, map_one]

 theorem map_origin (f : R →+* S) :
    Ideal.map (MvPowerSeries.map f) (originIdeal R ι) ≤ originIdeal S ι := by
  rw [originIdeal, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨_, ⟨i,rfl⟩, rfl⟩
  change MvPowerSeries.map f (X i) ∈ Ideal.span (Set.range (X : ι → MvPowerSeries ι S))
  rw [map_X]
  exact Ideal.subset_span ⟨i,rfl⟩

 theorem map_mem_origin (f : R →+* S) {P : MvPowerSeries ι R}
    (h : P ∈ originIdeal R ι) : MvPowerSeries.map f P ∈ originIdeal S ι :=
  map_origin f (Ideal.mem_map_of_mem (MvPowerSeries.map f) h)

 theorem map_mem_origin_pow (f : R →+* S) (q : ℕ) {P : MvPowerSeries ι R}
    (h : P ∈ (originIdeal R ι)^q) : MvPowerSeries.map f P ∈ (originIdeal S ι)^q := by
  have hp := Ideal.mem_map_of_mem (MvPowerSeries.map f) h
  rw [Ideal.map_pow] at hp
  exact Ideal.pow_right_mono (map_origin f) q hp

 theorem origin_constant {P : MvPowerSeries ι R} (h : P ∈ originIdeal R ι) :
    constantCoeff P = 0 := by
  have hi : originIdeal R ι ≤ RingHom.ker (constantCoeff : MvPowerSeries ι R →+* R) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change constantCoeff (X i : MvPowerSeries ι R) = 0
    exact constantCoeff_X i
  exact hi h

 theorem hasSubst_origin [Finite ι] (v : ι → MvPowerSeries κ R)
    (hv : ∀ i, v i ∈ originIdeal R κ) : HasSubst v :=
  hasSubst_of_constantCoeff_zero (fun i => origin_constant (hv i))

end BoundaryOnly.FormalObstruction.CoefficientRing

namespace BoundaryOnly.FormalObstruction.CoefficientRing
open MvPowerSeries
variable {R S : Type*} [CommRing R] [CommRing S] {d : ℕ} (n : Fin d → ℕ)

 theorem plus_hasSubst (i : Fin d) : HasSubst (plusCoordinates (k := R) n i) := by
  apply hasSubst_of_constantCoeff_zero
  rintro (j | y) <;> simp only [plusCoordinates, constantCoeff_X]

 theorem minus_hasSubst (i : Fin d) : HasSubst (minusCoordinates (k := R) n i) := by
  apply hasSubst_of_constantCoeff_zero
  rintro (j | y) <;> simp only [minusCoordinates, map_zero, constantCoeff_X]

 theorem zeroSlopes_hasSubst (i : Fin d) : HasSubst (zeroSlopes (k := R) n i) := by
  apply hasSubst_of_constantCoeff_zero
  rintro (j | y) <;> simp only [zeroSlopes, map_zero, constantCoeff_X]

 theorem map_plus (f : R →+* S) (i : Fin d) :
    (fun j => MvPowerSeries.map f (plusCoordinates n i j)) = plusCoordinates n i := by
  funext j
  cases j <;> simp only [plusCoordinates, map_X]

 theorem map_minus (f : R →+* S) (i : Fin d) :
    (fun j => MvPowerSeries.map f (minusCoordinates n i j)) = minusCoordinates n i := by
  funext j
  cases j <;> simp only [minusCoordinates, map_X, map_zero]

 theorem map_zeroSlopes (f : R →+* S) (i : Fin d) :
    (fun j => MvPowerSeries.map f (zeroSlopes n i j)) = zeroSlopes n i := by
  funext j
  cases j <;> simp only [zeroSlopes, map_X, map_zero]

 theorem map_potential (f : R →+* S) (P : (i : Fin d) → MvPowerSeries (WallVar n i) R) :
    MvPowerSeries.map f (potential n P) =
      potential n (fun i => MvPowerSeries.map f (P i)) := by
  simp only [potential, map_sum, map_sub, map_subst (plus_hasSubst n _),
    map_subst (minus_hasSubst n _), map_plus, map_minus]

 theorem map_slopeDerivative (f : R →+* S) (P : (i : Fin d) → MvPowerSeries (WallVar n i) R)
    (i : Fin d) :
    MvPowerSeries.map f (slopeDerivative n P i) =
      slopeDerivative n (fun i => MvPowerSeries.map f (P i)) i := by
  simp only [slopeDerivative, map_subst (zeroSlopes_hasSubst n i), map_zeroSlopes, map_partial]

 theorem graph_hasSubst (Y : InternalVar n → MvPowerSeries (GraphVar n) R)
    (hY : ∀ c, Y c ∈ originIdeal R (GraphVar n)) : HasSubst (graphCoordinates n Y) := by
  apply hasSubst_of_constantCoeff_zero
  rintro (a | c)
  · exact constantCoeff_X _
  · exact origin_constant (hY c)

 theorem map_graph (f : R →+* S) (Y : InternalVar n → MvPowerSeries (GraphVar n) R) :
    (fun j => MvPowerSeries.map f (graphCoordinates n Y j)) =
      graphCoordinates n (fun c => MvPowerSeries.map f (Y c)) := by
  funext j
  cases j <;> simp only [graphCoordinates, map_X]

 theorem map_restrictedGradient (f : R →+* S)
    (P : (i : Fin d) → MvPowerSeries (WallVar n i) R)
    (Y : InternalVar n → MvPowerSeries (GraphVar n) R)
    (hY : ∀ c, Y c ∈ originIdeal R (GraphVar n)) (c : InternalVar n) :
    MvPowerSeries.map f (restrictedGradient n P Y c) =
      restrictedGradient n (fun i => MvPowerSeries.map f (P i))
        (fun c => MvPowerSeries.map f (Y c)) c := by
  simp only [restrictedGradient, map_subst (graph_hasSubst n Y hY), map_graph,
    map_partial, map_potential]

 theorem map_gradientIdeal (f : R →+* S)
    (P : (i : Fin d) → MvPowerSeries (WallVar n i) R)
    (Y : InternalVar n → MvPowerSeries (GraphVar n) R)
    (hY : ∀ c, Y c ∈ originIdeal R (GraphVar n)) :
    Ideal.map (MvPowerSeries.map f) (gradientIdeal n P Y) =
      gradientIdeal n (fun i => MvPowerSeries.map f (P i))
        (fun c => MvPowerSeries.map f (Y c)) := by
  simp only [gradientIdeal, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext c
  exact map_restrictedGradient n f P Y hY c

 theorem map_negativeSlopeValue (f : R →+* S)
    (P : (i : Fin d) → MvPowerSeries (WallVar n i) R)
    (Y : InternalVar n → MvPowerSeries (GraphVar n) R)
    (hY : ∀ c, Y c ∈ originIdeal R (GraphVar n)) (i : Fin d) :
    MvPowerSeries.map f (negativeSlopeValue n P Y i) =
      negativeSlopeValue n (fun i => MvPowerSeries.map f (P i))
        (fun c => MvPowerSeries.map f (Y c)) i := by
  rw [negativeSlopeValue, map_subst (hasSubst_origin _ (fun y => hY (false,⟨i,y⟩))),
    map_slopeDerivative]
  rfl

 theorem map_complementary (f : R →+* S)
    (Y : InternalVar n → MvPowerSeries (GraphVar n) R) :
    (complementaryMatrix n Y).map f =
      complementaryMatrix n (fun c => MvPowerSeries.map f (Y c)) := by
  ext c bt
  simp only [Matrix.map_apply, complementaryMatrix]
  split_ifs <;> simp only [tangentMatrix, ← map_partial, constantCoeff_map]

end BoundaryOnly.FormalObstruction.CoefficientRing

namespace BoundaryOnly.FormalObstruction.CoefficientRing
open MvPowerSeries
variable {R S : Type*} [CommRing R] [CommRing S] {d : ℕ} {n : Fin d → ℕ}

def FormalData.map (D : FormalData (k := R) n) (f : R →+* S) : FormalData (k := S) n where
  P := fun i => MvPowerSeries.map f (D.P i)
  Y := fun c => MvPowerSeries.map f (D.Y c)
  order_three := fun i => map_mem_origin_pow f 3 (D.order_three i)
  centered := fun c => map_mem_origin f (D.centered c)
  complementary := by
    rw [← map_complementary]
    change IsUnit (f.mapMatrix (complementaryMatrix n D.Y)).det
    rw [← RingHom.map_det]
    exact D.complementary.map f
  graph_zero := by
    have h := congrArg (MvPowerSeries.map f) D.graph_zero
    simpa only [MvPowerSeries.map_subst (graph_hasSubst n D.Y D.centered), map_potential,
      map_graph, map_zero] using h
  positive_cubic := by
    intro i j l
    have h := Ideal.mem_map_of_mem (MvPowerSeries.map f) (D.positive_cubic i j l)
    rw [map_gradientIdeal n f D.P D.Y D.centered] at h
    simpa only [map_mul, slope, map_X] using h
  negative_cubic := by
    intro i j l
    have h := Ideal.mem_map_of_mem (MvPowerSeries.map f) (D.negative_cubic i j l)
    rw [map_gradientIdeal n f D.P D.Y D.centered] at h
    simpa only [map_mul, map_negativeSlopeValue n f D.P D.Y D.centered] using h

variable {k : Type*} [Field k]

def FormalData.toField (D : FormalData (k := k) n) : BoundaryOnly.FormalObstruction.FormalData (k := k) n where
  P := D.P
  Y := D.Y
  order_three := D.order_three
  centered := D.centered
  complementary := D.complementary.ne_zero
  graph_zero := D.graph_zero
  positive_cubic := D.positive_cubic
  negative_cubic := D.negative_cubic

end BoundaryOnly.FormalObstruction.CoefficientRing

end

end OAI
