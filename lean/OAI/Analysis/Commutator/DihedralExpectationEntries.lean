import Mathlib
import OAI.Analysis.Commutator.DihedralCompressionMoments
import OAI.Analysis.Commutator.DihedralHaar
import OAI.Analysis.Commutator.SubfactorExpectation

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.DihedralCorner

open FreeMoments

variable {A : Type*} [CStarAlgebra A]

lemma wave_mem (R : StarSubalgebra ℂ A) (u : unitary A) (hu : (u:A)∈R)
    (n : ℤ) : wave u n∈R := by
  cases n with
  | ofNat n =>
    change wave u (n:ℤ)∈R
    rw [wave_nat]
    exact R.pow_mem hu n
  | negSucc n =>
    change wave u (-((n+1:ℕ):ℤ))∈R
    rw [←wave_star,wave_nat]
    exact star_mem (R.pow_mem hu _)

lemma cosineAlgebra_coe_mem (R : StarSubalgebra ℂ A) (u d : unitary A)
    (hr : MulAut.conj d u=u⁻¹) {p : A} (hp : IsStarProjection p)
    (hpform : p=(1/2:ℂ) • (1+(d:A))) (hdp : (d:A)*p=p)
    (hpR : p∈R) (huR : (u:A)∈R) {b : Corner hp}
    (hb : b∈cosineAlgebra u d hr hp hpform hdp) : (b:A)∈R := by
  change b∈cosineSpace u hp at hb
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨n,rfl⟩ := hb
    exact R.mul_mem (R.mul_mem hpR (wave_mem R u huR n)) hpR
  | zero => exact R.zero_mem
  | add b c _ _ hb hc => exact R.add_mem hb hc
  | smul z b _ hb => exact R.smul_mem hb z

variable (S : Bool → StarSubalgebra ℂ A) (τ : A →ₗ[ℂ] ℂ)

variable (h1 : τ 1=1) (htr : ∀ a b : A, τ (a*b)=τ (b*a))
  (hstar : ∀ a : A, τ (star a)=star (τ a)) (hfree : Free S τ)

variable (d s : unitary A) (hd : (d:A)∈S false) (hs : (s:A)∈S true)
  (hd0 : τ (d:A)=0) (hs0 : τ (s:A)=0)

variable (hr : MulAut.conj d (d*s)=(d*s)⁻¹) (hd2 : (d:A)*(d:A)=1)
  (hs2 : (s:A)*(s:A)=1)

variable {p : A} (hp : IsStarProjection p) (hpform : p=(1/2:ℂ) • (1+(d:A)))
  (hpd : p*(d:A)=p) (hdp : (d:A)*p=p)

include h1 htr hstar hfree hd hs hd0 hs0 hd2 hpd hs2 in
theorem compression_expectation_pairing (hpD : p∈S false) (e b : Corner hp)
    (he : e∈cornerFactor hp (S false) hpD)
    (hb : b∈cosineAlgebra (d*s) d hr hp hpform hdp)
    (hb0 : halfCornerTrace hp τ b=0) {a : A} (ha : a∈S true) (j k : ℤ) :
    τ (a*(wave (d*s) j*((e:A)*(b:A)*(e:A))*wave (d*s) (-k)))=
      τ a*(halfCornerTrace hp τ e)^2*τ (wave (d*s) (j-k)*(b:A))+
      τ (a*(s:A))*(halfCornerTrace hp τ e)^2*τ (wave (d*s) (j+k+1)*(b:A)) := by
  let R := ⨆ i,SymmetryAlgebra.factors (s:A) (symmetry_star s hs2) hs2 S i
  have hDR : S false≤R := le_iSup (fun i => SymmetryAlgebra.factors
    (s:A) (symmetry_star s hs2) hs2 S i) false
  have hsR : (s:A)∈R := (le_iSup (fun i => SymmetryAlgebra.factors
    (s:A) (symmetry_star s hs2) hs2 S i) true) (SymmetryAlgebra.self_mem (s:A) (symmetry_star s hs2) hs2)
  have hwR : ((d*s:unitary A):A)∈R := R.mul_mem (hDR hd) hsR
  have heR : (e:A)∈R := hDR he
  have hbR := cosineAlgebra_coe_mem R (d*s) d hr hp hpform hdp (hDR hpD) hwR hb
  have hx : wave (d*s) j*((e:A)*(b:A)*(e:A))*wave (d*s) (-k)∈R :=
    R.mul_mem (R.mul_mem (wave_mem R _ hwR _) (R.mul_mem (R.mul_mem heR hbR) heR))
      (wave_mem R _ hwR _)
  rw [SymmetryAlgebra.pairing_projection (s:A) (symmetry_star s hs2) hs2 S τ
      hs hs0 hstar h1 hfree ha hx,
    compression_rotation_sandwich τ h1 htr hstar hfree d s false true Bool.false_ne_true
      hd hs hd0 hs0 hr hd2 hp hpform hpd hdp hpD e b he hb hb0,
    compression_symmetry_sandwich τ h1 htr hstar hfree d s false true Bool.false_ne_true
      hd hs hd0 hs0 hr hd2 hp hpform hpd hdp hpD e b he hb hb0]
  ring

end Kadison.DihedralCorner

end

end
end

end OAI
