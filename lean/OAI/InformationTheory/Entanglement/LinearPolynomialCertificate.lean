import Mathlib
import OAI.Analysis.Quantum.PPTSquare.ModularSupport

namespace OAI

noncomputable section
open Polynomial

namespace LinearPolynomialCertificate
open PolynomialCertificate
local instance : Fact (Nat.Prime 41) := ⟨by decide⟩
def ff : (ZMod 41)[X] := X+1
def powerCert (e : ℕ) (a : List (ZMod 41)) : Prop := ff ∣ X ^ e - poly a
def degreeCert (e n : ℕ) : Prop := by
  classical
  exact (EuclideanDomain.gcd ff (X ^ e-X)).natDegree = n
lemma degreeStep (e n : ℕ) (r g : List (ZMod 41))
    (hfnz : ff ≠ 0)
    (hpow : powerCert e r) (hg : poly g ≠ 0) (hgf : poly g ∣ ff) (hgr : poly g ∣ poly r-X)
    (hb : ∃ a b, a*ff+b*(poly r-X)=poly g) (hdeg : (poly g).natDegree = n) : degreeCert e n := by
  unfold degreeCert
  exact (gcd_degree_of_mod hfnz hg hpow hgf hgr hb).trans hdeg
end LinearPolynomialCertificate

namespace LinearPolynomialCertificateBridge
attribute [local instance] Classical.propDecidable
open LinearPolynomialCertificate
lemma bridge (e n : ℕ) (h : degreeCert e n) : (EuclideanDomain.gcd ff (X^e-X)).natDegree = n := by
  unfold degreeCert at h
  convert h using 2
end LinearPolynomialCertificateBridge

end

end OAI
