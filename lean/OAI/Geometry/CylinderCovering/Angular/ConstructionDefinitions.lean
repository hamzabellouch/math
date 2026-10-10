import OAI.Geometry.TriangularCovering.Main

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace TriangularCovering

def lowerAngularIndex {N : ℕ} (j : Fin N) : Fin (2*N) :=
  Fin.cast (two_mul N).symm (Fin.castAdd N j)

def upperAngularIndex {N : ℕ} (j : Fin N) : Fin (2*N) :=
  Fin.cast (two_mul N).symm (Fin.natAdd N j)

def lowerAngularAxis (ε : ℝ) (j : ℕ) : Space :=
  let a := mesh (n ε) j
  let b := mesh (n ε) (j+1)
  unit (tiltV ε (alpha a b) (beta a b))

def upperAngularAxis (ε : ℝ) (j : ℕ) : Space :=
  let a := mesh (n ε) j
  let b := mesh (n ε) (j+1)
  unit (tiltW ε (alpha a b) (beta a b))

def lowerAngularBase (ε : ℝ) (j : ℕ) : Set Space :=
  let a := mesh (n ε) j
  let b := mesh (n ε) (j+1)
  let v := lowerVertices a b (cutoff ε a b)
  projection (lowerAngularAxis ε j) '' triangle (v 0) (v 1) (v 2)

def upperAngularBase (ε : ℝ) (j : ℕ) : Set Space :=
  let a := mesh (n ε) j
  let b := mesh (n ε) (j+1)
  let v := upperVertices a b (cutoff ε a b)
  projection (upperAngularAxis ε j) '' triangle (v 0) (v 1) (v 2)

def ExplicitAngularFamily (ε : ℝ) (c : Fin (2*n ε) → TriCylinder) : Prop :=
  ∀ j : Fin (n ε),
    (c (lowerAngularIndex j)).axis = lowerAngularAxis ε j ∧
    (c (lowerAngularIndex j)).base = lowerAngularBase ε j ∧
    (c (upperAngularIndex j)).axis = upperAngularAxis ε j ∧
    (c (upperAngularIndex j)).base = upperAngularBase ε j

def AngularAreaStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    ∃ c : Fin (2*n ε) → TriCylinder,
      ExplicitAngularFamily ε c ∧
      totalArea c/H = ∑ j : Fin (n ε),
        normalizedTerm ε (mesh (n ε) j) (mesh (n ε) (j+1)) ∧
      |totalArea c/H - (1/2-(13/6000:ℝ)*ε^2)| ≤ 2*ε^4

def ExplicitAngularStatement : Prop :=
  A_min = H ∧
  ∀ ε : ℝ, 0 < ε → ε ≤ 1/2000 →
    ∃ c : Fin (2*n ε) → TriCylinder,
      ExplicitAngularFamily ε c ∧ Covers c ∧
      |totalArea c/H - (1/2-(13/6000:ℝ)*ε^2)| ≤ 2*ε^4 ∧
      totalArea c < A_min/2 ∧ relativeCost c < 1/2

end TriangularCovering

end

end OAI
