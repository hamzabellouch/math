import OAI.MathematicalPhysics.DefocusingNLS.Certificates.PolynomialEnclosure

namespace OAI

/-! # The integer boundary certificate recipe

The depth-eight forward recurrence gives coefficient enclosures for the
boundary determinant and its homogeneous chart transforms.
-/

namespace DefocusingNLS.BoundaryCertificate
open GaussianEnclosure

abbrev EnclosurePolynomial := List GaussianEnclosure

def coefficient (r i e : ℤ) : GaussianEnclosure := ⟨⟨r, i⟩, e⟩
def constant (r : ℤ) : EnclosurePolynomial := [coefficient r 0 0]

def sharpAux : Bool → EnclosurePolynomial → EnclosurePolynomial
  | _, [] => []
  | false, a :: as => conj a :: sharpAux true as
  | true, a :: as => neg (conj a) :: sharpAux false as

def sharp (as : EnclosurePolynomial) : EnclosurePolynomial := sharpAux false as

abbrev Row := EnclosurePolynomial × EnclosurePolynomial
abbrev State := Row × Row

def step (ell n : ℕ) (xy : State) : State :=
  let M := constant (100000000 * (ell + 5))
  let s := [coefficient 0 270506819 2]
  let t := [coefficient ((50000000 : ℤ) * ((ell : ℤ) + 2 * (n : ℤ)) - 3125000) (-33477607) 2,
    coefficient 0 100000000 0]
  let d := subPolynomial t M
  let x₀ := addPolynomial (mulPolynomial t xy.1.1) (mulPolynomial s xy.2.1)
  let x₁ := addPolynomial (mulPolynomial t xy.1.2) (mulPolynomial s xy.2.2)
  ((x₀, x₁), (subPolynomial (mulPolynomial d xy.2.1) x₀,
    subPolynomial (mulPolynomial d xy.2.2) x₁))

def state (ell : ℕ) : ℕ → State
  | 0 => ((constant 1, constant 0), (constant 0, constant 1))
  | n + 1 => step ell n (state ell n)

def hermitian (ell : ℕ) (x y z w : EnclosurePolynomial) : EnclosurePolynomial :=
  addPolynomial
    (mulPolynomial (mulPolynomial (constant (100000000 * (ell + 5))) (conjPolynomial x)) z)
    (mulPolynomial [coefficient 0 270506819 2]
      (subPolynomial (mulPolynomial (conjPolynomial x) w) (mulPolynomial (conjPolynomial y) z)))

def symmetrize (p : EnclosurePolynomial) : EnclosurePolynomial := addPolynomial p (sharp p)

def determinant (ell : ℕ) : EnclosurePolynomial :=
  let xy := state ell 8
  let A := symmetrize (hermitian ell xy.1.1 xy.2.1 xy.1.1 xy.2.1)
  let D := symmetrize (hermitian ell xy.1.2 xy.2.2 xy.1.2 xy.2.2)
  let C := symmetrize (hermitian ell xy.1.1 xy.2.1 xy.1.2 xy.2.2)
  subPolynomial (mulPolynomial A D) (mulPolynomial C (conjPolynomial C))

/-- The degree-30 real-even truncation. Its use requires the structural proof. -/
def evenCoefficients (ell : ℕ) : List GaussianEnclosure :=
  (List.range 16).map fun j =>
    let a := (determinant ell)[2 * j]?.getD zero
    coefficient a.center.re 0 a.error

def transformAux (U V J : ℤ) : List GaussianEnclosure →
    EnclosurePolynomial × EnclosurePolynomial → EnclosurePolynomial × EnclosurePolynomial
  | [], qm => qm
  | a :: as, qm =>
    let q := addPolynomial (mulPolynomial qm.1 [coefficient U 0 0, coefficient V 0 0])
      (mulPolynomial qm.2 [a])
    let m := mulPolynomial qm.2 [coefficient 1 0 0, coefficient J 0 0]
    transformAux U V J as (q, m)

def transformed (ell : ℕ) (U V J : ℤ) : EnclosurePolynomial :=
  (transformAux U V J (evenCoefficients ell).reverse (constant 0, constant 1)).1

def coefficientPositive (a : GaussianEnclosure) : Bool :=
  decide (a.error < a.center.re)

def positiveFirst16 (p : EnclosurePolynomial) : Bool :=
  ((List.range 16).map fun n => coefficientPositive (p[n]?.getD zero)).all id

end DefocusingNLS.BoundaryCertificate

end OAI
