import OAI.Analysis.Quantum.PPTSquare.Mod131Powers01
import OAI.Analysis.Quantum.PPTSquare.Mod131Powers02
import OAI.Analysis.Quantum.PPTSquare.Mod131Powers03
import OAI.Analysis.Quantum.PPTSquare.Mod131Powers04
import OAI.Analysis.Quantum.PPTSquare.Mod131Data
import OAI.Analysis.Quantum.PPTSquare.Mod131Products
import OAI.Analysis.Quantum.PPTSquare.Mod131Reduction
import OAI.Analysis.Quantum.PPTSquare.Mod139Powers01
import OAI.Analysis.Quantum.PPTSquare.Mod139Powers02
import OAI.Analysis.Quantum.PPTSquare.Mod139Powers03
import OAI.Analysis.Quantum.PPTSquare.Mod139Powers04
import OAI.Analysis.Quantum.PPTSquare.Mod139Powers05
import OAI.Analysis.Quantum.PPTSquare.Mod139Data
import OAI.Analysis.Quantum.PPTSquare.Mod139Products
import OAI.Analysis.Quantum.PPTSquare.Mod139Reduction
import OAI.Analysis.Quantum.PPTSquare.Mod41Powers01
import OAI.Analysis.Quantum.PPTSquare.Mod41Powers02
import OAI.Analysis.Quantum.PPTSquare.Mod41Powers03
import OAI.Analysis.Quantum.PPTSquare.Mod41Powers04
import OAI.Analysis.Quantum.PPTSquare.Mod41Powers05
import OAI.Analysis.Quantum.PPTSquare.Mod41Powers06
import OAI.Analysis.Quantum.PPTSquare.Mod41Data
import OAI.Analysis.Quantum.PPTSquare.Mod41Products
import OAI.Analysis.Quantum.PPTSquare.Mod41Reduction
import OAI.Analysis.Quantum.PPTSquare.ModularSupport
import OAI.Analysis.Quantum.PPTSquare.GaloisAction

namespace OAI

open Polynomial
noncomputable section
namespace PolynomialGcdDegree
attribute [local instance] Classical.propDecidable
local instance : Fact (Nat.Prime 41) := ⟨by decide⟩
def dg (e : ℕ) : Prop := (EuclideanDomain.gcd ModularPencil.P41.f (X^e-X)).natDegree = 0
def dgc (e : ℕ) : Prop := by
  classical
  exact (EuclideanDomain.gcd ModularPencil.P41.f (X^e-X)).natDegree = 0
lemma bridge (e n : ℕ) (h : ModularPencil.P41.degreeCert e n) :
    (EuclideanDomain.gcd ModularPencil.P41.f (X^e-X)).natDegree = n := by
  unfold ModularPencil.P41.degreeCert at h
  convert h using 2
lemma concrete : dg (41^4) := by
  exact bridge (41^4) 0 ModularPencil.P41.gcd_degree4

end PolynomialGcdDegree

end

end OAI
