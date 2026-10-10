import Mathlib

namespace OAI

/-!
# Sharp Gaussian minorants with atomic interpolation

The sharp Gaussian minorants of the atomic certificate for triangular-lattice
universal optimality, including the construction for parameters at least one.
-/

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex Polynomial

namespace AtomicTriangular

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def b : ℝ := Real.sqrt 3 / 2

def triangularPoint (jk : ℤ × ℤ) : Plane :=
  (Real.sqrt b)⁻¹ •
    (EuclideanSpace.single 0 ((jk.1 : ℝ) + (jk.2 : ℝ) / 2) +
      EuclideanSpace.single 1 ((jk.2 : ℝ) * b))

def A : Set Plane := Set.range triangularPoint

def dualA : Set Plane := {w | ∀ a ∈ A, ∃ n : ℤ, inner ℝ a w = (n : ℝ)}

def gaussian (α : ℝ) (x : Plane) : ℝ := Real.exp (-Real.pi * α * ‖x‖ ^ 2)

def Radial (f : Plane → ℝ) : Prop := ∀ x y, ‖x‖ = ‖y‖ → f x = f y

def realFourier (f : Plane → ℝ) (w : Plane) : ℂ := 𝓕 (fun x => (f x : ℂ)) w

end AtomicTriangular

namespace AtomicTriangular.Construction

def b : ℝ := Real.sqrt 3 / 2

def h : ℝ := 17 / 50

def H : ℝ := 27 / 50

def eta : ℝ := 1 / 5

def kappa : ℝ := Real.pi / 36

def residues : Finset ℤ := {0,1,3,4,7,9,12,13,16,19,21,25,27,28,31}

def residue (a : Fin 15) : ℤ := ![0,1,3,4,7,9,12,13,16,19,21,25,27,28,31] a

def Node : Type := {n : ℤ // 0 < n ∧ n % 36 ∈ residues}

def FiniteNodes : Finset ℤ := {1,3,4,7,9,12,13,16,19,21}

def sineFactor (a : Fin 15) (s : ℂ) : ℂ :=
  2 * Complex.sin ((kappa : ℂ) * (s - (residue a : ℂ)))

def P (s : ℂ) : ℂ := ∏ a : Fin 15, (sineFactor a s)^2

def dBasis (n : Node) : ℂ → ℂ := dslope P (n.val : ℂ)

def cBasis (n : Node) : ℂ → ℂ := dslope (dBasis n) (n.val : ℂ)

def finiteC (a : Fin 15) (s : ℂ) : ℂ :=
  4 * (kappa : ℂ)^2 * ∏ r ∈ Finset.univ.erase a, (sineFactor r s)^2

def finiteD (a : Fin 15) (s : ℂ) : ℂ :=
  2 * (kappa : ℂ) * sineFactor a s *
    Complex.cos ((kappa : ℂ) * (s - (residue a : ℂ))) *
      ∏ r ∈ Finset.univ.erase a, (sineFactor r s)^2

def phase (s : ℂ) : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I * s / 18)

def atomFactor (a : Fin 15) : Polynomial ℂ :=
  -C (phase (residue a)) + C 2 * X - C (phase (-residue a)) * X^2

def atomPolynomial : Polynomial ℂ := ∏ a : Fin 15, atomFactor a

def cAtomPolynomial (a : Fin 15) : Polynomial ℂ :=
  C (4 * (kappa : ℂ)^2) * ∏ r ∈ Finset.univ.erase a, atomFactor r

def dAtomPolynomial (a : Fin 15) : Polynomial ℂ :=
  C (Complex.I * (kappa : ℂ)) *
    (C (phase (residue a)) - C (phase (-residue a)) * X^2) *
      ∏ r ∈ Finset.univ.erase a, atomFactor r

def fourierCoeff (j : Fin 31) : ℂ := atomPolynomial.coeff j.val

def frequency (j : Fin 31) : ℝ := ((j.val : ℝ)-15)/18

def waveDerivative (k : ℕ) (s : ℂ) : ℂ :=
  ∑ j : Fin 31, fourierCoeff j * (I*Real.pi*frequency j)^k *
    exp (I*Real.pi*frequency j*s)

def Q (n : ℤ) : ℝ := (waveDerivative 2 n).re / 2

def D (n : ℤ) : ℝ := (waveDerivative 3 n).re / (6 * Q n)

end AtomicTriangular.Construction

namespace AtomicTriangular.FiniteCertificate
open Construction

def cShiftPolynomial (a : Fin 15) : Polynomial ℂ := X * cAtomPolynomial a

def cCoefficient (a : Fin 15) (j : Fin 31) : ℂ := (cShiftPolynomial a).coeff j.val

def dCoefficient (a : Fin 15) (j : Fin 31) : ℂ := (dAtomPolynomial a).coeff j.val

end AtomicTriangular.FiniteCertificate

namespace AtomicTriangular.Construction

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def radial (x : Plane) : ℝ := b*‖x‖^2

def waveDen (k t : ℝ) : ℝ := k^2+t^2

def Xwave (k t : ℝ) : ℝ := (4/3)/waveDen k t

def lambda (k t : ℝ) : ℂ := ((k:ℂ)+I*t)/(b*waveDen k t : ℝ)

def zeta (k v t : ℝ) : ℂ := -(t:ℂ)*(Xwave k t:ℂ)+I*(k*Xwave k t-v:ℝ)

def transformedWave (k v t : ℝ) (s : ℂ) : ℂ := lambda k t*exp (I*Real.pi*zeta k v t*s)

def finiteColumn (col : Fin 23) (j : Fin 31) : ℂ :=
  if hc : col.val<22 then
    if col.val%2=0 then FiniteCertificate.cCoefficient ⟨col.val/2,by omega⟩ j
      else FiniteCertificate.dCoefficient ⟨col.val/2,by omega⟩ j
  else fourierCoeff j

def finiteNode (n : Fin 10) : ℤ := residue ⟨n.val+1,by omega⟩

def jetMultiplier (k v : ℝ) (n : ℤ) (d : Fin 2) (t : ℝ) : ℂ :=
  (Q n:ℂ)⁻¹*transformedWave k v t n *
    (if d.val=0 then -1 else (D n:ℂ)-I*Real.pi*zeta k v t)

def jet (k v : ℝ) (n : ℤ) (d : Fin 2) (S : Fin 31 → ℂ) : ℝ :=
  (∑ j : Fin 31, jetMultiplier k v n d (frequency j)*S j).re

def fullJetMatrix : Matrix (Fin 20) (Fin 23) ℝ := fun i col =>
  jet (if col.val=22 then h else H) H
    (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩ (finiteColumn col)

def R : Matrix (Fin 20) (Fin 20) ℝ := fun i j => fullJetMatrix i ⟨j.val+2,by omega⟩

def R0 : Matrix (Fin 20) (Fin 3) ℝ := fun i j =>
  fullJetMatrix i (if j.val<2 then ⟨j.val,by omega⟩ else 22)

abbrev TailNode := {n : Node // n.val ∉ FiniteNodes}

structure InputCoefficients where
  C : ℝ
  finiteC : Fin 11 → ℝ
  finiteD : Fin 11 → ℝ
  tailC : TailNode → ℝ
  tailD : TailNode → ℝ
  summable : Summable (fun n => |tailC n|+|tailD n|)

def tailInput (a : InputCoefficients) (s : ℂ) : ℂ :=
  (a.C:ℂ)*P s + ∑' n : TailNode, ((a.tailC n:ℂ)*cBasis n.val s+(a.tailD n:ℂ)*dBasis n.val s)

def finiteInput (a : InputCoefficients) (s : ℂ) : ℂ :=
  ∑ j : Fin 11, ((a.finiteC j:ℂ)*finiteC ⟨j.val,by omega⟩ s +
    (a.finiteD j:ℂ)*finiteD ⟨j.val,by omega⟩ s)

def inputComplex (a : InputCoefficients) (x : Plane) : ℂ :=
  exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*tailInput a (radial x) +
    exp (-(Real.pi:ℂ)*H*(radial x:ℂ))*finiteInput a (radial x)

def targetCoefficient (n : Fin 10) : ℝ := Q 1 / Q (finiteNode n) * Real.exp (Real.pi*eta*(finiteNode n))

def Yf : Matrix (Fin 20) (Fin 8) ℝ := fun i j =>
  if i.val<8 then
    targetCoefficient ⟨i.val/2,by omega⟩ *
      (if i.val%2=0 then (if j.val=i.val then 1 else 0)
       else (if j.val=i.val then -1 else if j.val=i.val-1 then Real.pi*eta-D (finiteNode ⟨i.val/2,by omega⟩) else 0))
  else 0

def gamma (side : Fin 2) : Matrix (Fin 3) (Fin 8) ℝ := fun i j =>
  if j.val=1 then (if i.val=0 then 11/25 else if i.val=1 then 0 else if side.val=0 then -(3/500) else 3/500) else 0

def Uplus : Matrix (Fin 20) (Fin 8) ℝ :=
  (1-R)⁻¹*(Yf+R0*(gamma 1+gamma 0))

def Uminus : Matrix (Fin 20) (Fin 8) ℝ :=
  (1+R)⁻¹*(Yf+R0*(gamma 1-gamma 0))

def finiteSolution (side : Fin 2) : Matrix (Fin 20) (Fin 8) ℝ :=
  if side.val=0 then (1/2:ℝ) • (Uplus+Uminus) else (1/2:ℝ) • (Uplus-Uminus)

def Acoefficient (side : Fin 2) : Matrix (Fin 23) (Fin 8) ℝ := fun i j =>
  if hi : i.val<2 then gamma side ⟨i.val,by omega⟩ j
  else if h22 : i.val=22 then gamma side 2 j
  else finiteSolution side ⟨i.val-2,by omega⟩ j

def gaussianZ (α : ℝ) : ℝ := 1/(Real.pi*(α/b-h))

def actualParameter (z : ℝ) : Fin 8 → ℝ :=
  ![z,1,z*Real.exp (-2/z),Real.exp (-2/z),z*Real.exp (-3/z),Real.exp (-3/z),
    z*Real.exp (-6/z),Real.exp (-6/z)]

def normalizingDen (z : ℝ) := Q 1*z*Real.exp (1/z)

end AtomicTriangular.Construction

end

noncomputable section
open scoped BigOperators FourierTransform

namespace AtomicTriangular.Construction

def correctedFinite (side : Fin 2) (z : ℝ) (δ : Fin 20 → ℝ) (j : Fin 22) : ℝ :=
  (∑ r : Fin 8, Acoefficient side ⟨j.val, by omega⟩ r * actualParameter z r) +
    if hj : j.val < 2 then 0 else δ ⟨j.val - 2, by omega⟩

end AtomicTriangular.Construction

namespace AtomicTriangular
open Construction

local instance finite_pair_neZero : NeZero (2 : ℕ) := inferInstance
local instance three_atLeastTwo : Nat.AtLeastTwo 3 := inferInstance
local instance ten_atLeastTwo : Nat.AtLeastTwo 10 := inferInstance
local instance five_hundred_atLeastTwo : Nat.AtLeastTwo 500 := inferInstance
local instance plane_borelSpace : BorelSpace Plane := inferInstance
local instance plane_finite : Module.Finite ℝ Plane := inferInstance

def AtomicConstruction (α : ℝ) (f : Plane → ℝ) : Prop :=
  IsUnit (1 - R) ∧ IsUnit (1 + R) ∧
  (1 - R) * Uplus = Yf + R0 * (gamma 1 + gamma 0) ∧
  (1 + R) * Uminus = Yf + R0 * (gamma 1 - gamma 0) ∧
  ∃ (δ : Fin 2 → Fin 20 → ℝ) (a : Fin 2 → InputCoefficients),
    (∀ side, (∑ j : Fin 20, |δ side j|) < (1 / 10^5 : ℝ)) ∧
    (∀ side, (a side).C = if side.val = 0 then -(3/500) else 3/500) ∧
    (∀ side (j : Fin 11),
      (a side).finiteC j =
        correctedFinite side (gaussianZ α) (δ side) ⟨2*j.val, by omega⟩ ∧
      (a side).finiteD j =
        correctedFinite side (gaussianZ α) (δ side) ⟨2*j.val+1, by omega⟩) ∧
    (∀ side, Summable (fun n => |(a side).tailC n| + |(a side).tailD n|) ∧
      (∑' n, (|(a side).tailC n| + |(a side).tailD n|)) < (3 / 10^9 : ℝ)) ∧
    (∀ x, (f x : ℂ) =
      (inputComplex (a 0) x + 𝓕 (inputComplex (a 1)) x) /
        (normalizingDen (gaussianZ α) : ℂ))

end AtomicTriangular
end

noncomputable section
open scoped BigOperators FourierTransform

namespace AtomicTriangular
open Construction

theorem sharp_gaussian_minorants_with_construction (α : ℝ) (hα : 0 < α) :
    ∃ f : SchwartzMap Plane ℝ,
      Radial f ∧ (∀ x, f x ≤ gaussian α x) ∧
      (∀ w, (realFourier f w).im = 0 ∧ 0 ≤ (realFourier f w).re) ∧
      (∀ a ∈ A, a ≠ 0 → f a = gaussian α a) ∧
      (∀ w ∈ dualA, w ≠ 0 → realFourier f w = 0) ∧
      (1 ≤ α → AtomicConstruction α f) := by
  sorry

end AtomicTriangular
end

end OAI
