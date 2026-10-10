import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryCertificateArithmetic

namespace OAI

/-! The depth-five exterior certificate with a free real spatial variable. -/

namespace DefocusingNLS.ExteriorCertificate
open GaussianEnclosure
open BoundaryCertificate (EnclosurePolynomial coefficient constant Row State)

def step (z₀ : ℤ) (n : ℕ) (xy : State) : State :=
  let M := constant 500000000
  let t := [coefficient (100000000*(n : ℤ)) (-33477607) 2]
  let s := [coefficient 0 z₀ 0, coefficient 0 100000000 0]
  let d := subPolynomial t M
  let x₀ := addPolynomial (mulPolynomial t xy.1.1) (mulPolynomial s xy.2.1)
  let x₁ := addPolynomial (mulPolynomial t xy.1.2) (mulPolynomial s xy.2.2)
  ((x₀,x₁), (subPolynomial (mulPolynomial d xy.2.1) x₀,
    subPolynomial (mulPolynomial d xy.2.2) x₁))

def state (z₀ : ℤ) : ℕ → State
  | 0 => ((constant 1,constant 0),(constant 0,constant 1))
  | n+1 => step z₀ n (state z₀ n)

def hermitian (z₀ : ℤ) (x y z w : EnclosurePolynomial) : EnclosurePolynomial :=
  addPolynomial
    (mulPolynomial (mulPolynomial (constant 500000000) (conjPolynomial x)) z)
    (mulPolynomial [coefficient 0 z₀ 0, coefficient 0 100000000 0]
      (subPolynomial (mulPolynomial (conjPolynomial x) w)
        (mulPolynomial (conjPolynomial y) z)))

def diagonal (z₀ : ℤ) : EnclosurePolynomial :=
  let xy := state z₀ 5
  hermitian z₀ xy.1.2 xy.2.2 xy.1.2 xy.2.2

def lowerOffDiagonal (z₀ : ℤ) : EnclosurePolynomial :=
  let xy := state z₀ 5
  hermitian z₀ xy.1.2 xy.2.2 xy.1.1 xy.2.1

def realCoefficients (as : EnclosurePolynomial) (N : ℕ) : EnclosurePolynomial :=
  (List.range N).map fun n : ℕ =>
    let a := (as[n]?).getD zero
    coefficient a.center.re 0 a.error

def negImagCoefficients (as : EnclosurePolynomial) (N : ℕ) : EnclosurePolynomial :=
  (List.range N).map fun n : ℕ =>
    let a := (as[n]?).getD zero
    coefficient (-a.center.im) 0 a.error

def determinantMargin (z₀ : ℤ) : EnclosurePolynomial :=
  [coefficient (1130*100000000^10*z₀) 0 0,
    coefficient (1130*100000000^11) 0 0]

def realBound : EnclosurePolynomial :=
  addPolynomial (mulPolynomial (constant 43) (realCoefficients (diagonal 270400000) 11))
    (mulPolynomial (constant 1000)
      (subPolynomial (realCoefficients (lowerOffDiagonal 270400000) 11)
        (determinantMargin 270400000)))

def imaginaryBound : EnclosurePolynomial :=
  subPolynomial (negImagCoefficients (lowerOffDiagonal 300000000) 9)
    (determinantMargin 300000000)

def positiveCoefficients (as : EnclosurePolynomial) : Bool :=
  as.all (fun a => decide (a.error < a.center.re))

end DefocusingNLS.ExteriorCertificate

end OAI
