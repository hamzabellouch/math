import OAI.Algebra.AffineCancellation.InvariantRestriction
import OAI.Algebra.AffineCancellation.BezoutFrame
import OAI.Algebra.AffineCancellation.TorsorClearing

namespace OAI

noncomputable section

namespace ComplexCancellation.SliceDerivative
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
def derivation : Derivation k (Polynomial F) (Polynomial F) :=
  Derivation.mk' ((Polynomial.derivative (R := F)).restrictScalars k) (by
    intro p q
    change (p*q).derivative=p*q.derivative+q*p.derivative
    rw [Polynomial.derivative_mul,mul_comm p.derivative q,add_comm])
lemma apply_eq (p : Polynomial F) : derivation (k := k) p=p.derivative := rfl
lemma locallyNilpotent : LND.LocallyNilpotent (derivation (k := k) (F := F)) := by
  intro p
  exact ⟨p.natDegree+1,Polynomial.iterate_derivative_eq_zero (by omega)⟩
end ComplexCancellation.SliceDerivative

namespace ComplexCancellation.Bundle
instance finiteType : Algebra.FiniteType ℂ B := by
  let : Algebra.FiniteType ℂ Determinant.T := Algebra.FiniteType.quotient ℂ _
  infer_instance
end ComplexCancellation.Bundle

namespace ComplexCancellation.Torsor
open LaurentPolynomial
variable {P : Type*} [CommRing P] [IsDomain P] [Algebra ℂ P]
variable (ρ : Degeneration.G →ₐ[ℂ] P) (Q : Frame ρ) (D : Derivation ℂ Degeneration.G Degeneration.G)
variable (hρ : Function.Injective ρ) (hc : ∀ p, p ∈ InvariantClearing.subalgebra ρ D)
variable (Dp : Derivation ℂ P P) (hDp : LND.LocallyNilpotent Dp) (hder : ∀ r, Dp (ρ r)=ρ (D r))
include hder in
omit [IsDomain P] in
lemma extension_base (r : Degeneration.G) : LaurentDerivation.extension Dp (base ρ r)=base ρ (D r) := by
  change LaurentDerivation.extension Dp (C (ρ r))=C (ρ (D r))
  rw [LaurentDerivation.extension_C,hder]
include hρ hc hDp hder
lemma invariant_replica (hf : Function.Injective (forward ρ Q)) :
    ∃ c : Degeneration.G, ∃ E : Derivation ℂ Bundle.B Bundle.B,
      D c=0 ∧ c≠0 ∧ LND.LocallyNilpotent E ∧
      ∀ b, forward ρ Q (E b)=base ρ c*LaurentDerivation.extension Dp (forward ρ Q b) := by
  have hbase (r : Degeneration.G) : forward ρ Q (Bundle.pullback r)=base ρ r :=
    DFunLike.congr_fun (forward_pullback ρ Q hρ) r
  obtain ⟨c,E,hDc,hcn,hE,hs⟩ := InvariantRestriction.exists_restriction Bundle.pullback (forward ρ Q) hf D
    (LaurentDerivation.extension Dp) (LaurentDerivation.locallyNilpotent Dp hDp)
    (fun r => by rw [hbase,hbase,extension_base ρ D Dp hder]) (clear_laurent ρ Q D hρ hc)
  exact ⟨c,E,hDc,hcn,hE,fun b => by rw [hs,hbase]⟩
end ComplexCancellation.Torsor

namespace ComplexCancellation.PolynomialTorsor
open PolynomialModel
instance : CharZero Degeneration.G := Algebra.charZero_of_charZero ℂ Degeneration.G
variable (D : Derivation ℂ Degeneration.G Degeneration.G) (hD : LND.LocallyNilpotent D)
abbrev K := FractionRing Degeneration.G
abbrev P := Polynomial (PolynomialModel.F D)
variable {t : K} (ht : FractionDerivation.extend D t=1)
noncomputable def ρ : Degeneration.G →ₐ[ℂ] P D := model D hD ht
lemma ρ_injective : Function.Injective (ρ D hD ht) := model_injective D hD ht
lemma exists_frame : Nonempty (Torsor.Frame (ρ D hD ht)) := by
  have h := congrArg (ρ D hD ht) Degeneration.equation
  simp only [map_mul,map_add,map_one] at h
  obtain ⟨a,d,b,c,hab,hdc,hdb,hdet⟩ := BezoutFrame.exists_frame _ _ _ h
  exact ⟨⟨a,d,b,c,hab,hdc,hdb,hdet⟩⟩
def toField : K →ₐ[ℂ] Torsor.KB :=
  IsFractionRing.liftAlgHom (g := Torsor.ib.comp Bundle.pullback)
    ((IsFractionRing.injective Bundle.B Torsor.KB).comp Bundle.pullback_injective)
def inverseCoefficient : P D →ₐ[ℂ] Torsor.KB := (toField).comp (PolynomialModel.evaluation (D := D) (t := t))
lemma inverseCoefficient_comp : (inverseCoefficient (D := D) (t := t)).comp (ρ D hD ht)=Torsor.ib.comp Bundle.pullback := by
  ext r
  change toField (PolynomialModel.evaluation (D := D) (t := t) (model D hD ht r))=_
  rw [evaluation_model]
  exact IsFractionRing.lift_algebraMap
    (g := (Torsor.ib.comp Bundle.pullback).toRingHom)
    ((IsFractionRing.injective Bundle.B Torsor.KB).comp Bundle.pullback_injective) r
lemma forward_injective (Q : Torsor.Frame (ρ D hD ht)) : Function.Injective (Torsor.forward (ρ D hD ht) Q) :=
  Torsor.forward_injective _ Q (inverseCoefficient (D := D) (t := t)) (inverseCoefficient_comp D hD ht)
end ComplexCancellation.PolynomialTorsor

end

end OAI
