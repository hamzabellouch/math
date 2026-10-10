import OAI.Analysis.HyperbolicCones.Coordinates

namespace OAI

noncomputable section

open Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.L2Operator

universe u v

namespace Paper256

theorem qMatrix_map {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (y : Fin 3 → R) :
    (qMatrix y).map f = qMatrix (fun i => f (y i)) := by
  ext i j
  by_cases h : i = j <;> simp [qMatrix, h]

theorem phi_map {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (y : Fin 3 → R) (X : Mat 4 R) :
    (phi y X).map f = phi (fun i => f (y i)) (X.map f) := by
  ext i j
  have hq (a b : Fin 3) : f (qMatrix y a b) = qMatrix (fun k => f (y k)) a b :=
    congrFun (congrFun (qMatrix_map f y) a) b
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [phi, Matrix.trace, Matrix.diag, Matrix.mul_apply, hq]
    · simp [phi, hq]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [phi, hq]
    · simp [phi, hq]

theorem matrixValue_map {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (X Z : Mat 4 R) (y : Fin 3 → R) :
    f (matrixValue X Z y) = matrixValue (X.map f) (Z.map f) (fun i => f (y i)) := by
  unfold matrixValue
  rw [f.map_det]
  congr 1
  have hp := phi_map f y X.adjugate
  have ha : X.adjugate.map f = (X.map f).adjugate := f.map_adjugate X
  rw [ha] at hp
  ext i j
  have hp' := congrFun (congrFun hp i) j
  simpa [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, f.map_det] using
    congrArg (fun z => f X.det * f (Z i j) - z) hp'

theorem symmetricCoordinates_map {R : Type u} {S : Type v} (f : R → S) (v : SymIndex → R) :
    (symmetricCoordinates v).map f = symmetricCoordinates (fun i => f (v i)) := by
  ext i j
  by_cases h : i ≤ j <;> simp [symmetricCoordinates, h]

theorem symmetricCoordinates_entries (X : Sym 4) :
    symmetricCoordinates (fun ij => (X : Mat 4 ℝ) ij.val.1 ij.val.2) = (X : Mat 4 ℝ) := by
  exact congrArg Subtype.val (symmetricCoordinateEquiv.left_inv X)

theorem polynomial_evaluation (X Z : Sym 4) (y : Fin 3 → ℝ) :
    MvPolynomial.eval (coordinates ((X, Z), y)) polynomial =
      matrixValue (X : Mat 4 ℝ) (Z : Mat 4 ℝ) y := by
  let f := MvPolynomial.eval₂Hom (RingHom.id ℝ) (coordinates ((X, Z), y))
  change f (matrixValue _ _ _) = _
  rw [matrixValue_map, symmetricCoordinates_map, symmetricCoordinates_map]
  simp [f, coordinates, symmetricCoordinates_entries]

end Paper256

end

end OAI
