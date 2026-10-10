import OAI.NumberTheory.DirichletL.Moments.SecondSourceSeededPowerDescent
import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalScalar

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondReferenceNormalization
open HeckeFamily CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondNonexceptionalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentSectorLocalization CenteredMomentSecondSourcePowerDescent
open CenteredMomentSecondSourceSeededPowerDescent
local notation "O"=>HeckeFamily.O

def referenceEnvelope (qref:ℝ)(C D:Ideal O)(U:Finset (CommonIndex C D))(n:Fin 4→ℤ):ℝ:=
  (fixedFactor:ℝ)*qref*(∏P∈U,P.val).absNorm*
    (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm*dyadicScale (n 1)

lemma envelope_rescale (η:Character)(qref E:ℝ)(C D:Ideal O)
    (U:Finset (CommonIndex C D))(n:Fin 4→ℤ):
    (qref/(η.modulus.absNorm:ℝ)*E)*childEnvelope η C D U n=
      E*referenceEnvelope qref C D U n:=by
  have hq:(η.modulus.absNorm:ℝ)≠0:=by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot
  unfold childEnvelope referenceEnvelope
  field_simp

lemma paired_rescale (q qref E₁ E₂:ℝ)(hq:0<q)(hr:0≤qref):
    q*Real.sqrt ((qref/q*E₁)*(qref/q*E₂))=qref*Real.sqrt (E₁*E₂):=by
  rw [show (qref/q*E₁)*(qref/q*E₂)=(qref/q)^2*(E₁*E₂) by ring,
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (div_nonneg hr hq.le)]
  field_simp

lemma physicalFactors_rescale (Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t q qref E₁ E₂ r
    loProduct wlo:ℝ)(J₁ J₂:ℕ)(SΦ:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hq:0<q)(hr:0≤qref):
    physicalFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t q
      (qref/q*E₁) (qref/q*E₂) r loProduct wlo J₁ J₂ SΦ W=
    physicalFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t qref
      E₁ E₂ r loProduct wlo J₁ J₂ SΦ W:=by
  funext j
  fin_cases j
  · dsimp [physicalFactors]
    have hh:=paired_rescale q qref E₁ E₂ hq hr
    calc
      _=Cmain*Z^(2*δ+ε)*(q*Real.sqrt ((qref/q*E₁)*(qref/q*E₂)))*
        CenteredMomentSecondWindowBudget.heightEnvelope t^(J₁+J₂)*
        CenteredMomentSecondWindowBudget.profileMoment J₁*CenteredMomentSecondWindowBudget.profileMoment J₂:=by ring
      _=_:=by rw [hh];ring
  all_goals rfl

lemma seededFactors_rescale (Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t q qref E₁ E₂ r
    loProduct wlo seed:ℝ)(J₁ J₂:ℕ)(SΦ:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hq:0<q)(hr:0≤qref):
    seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t q
      (qref/q*E₁) (qref/q*E₂) r loProduct wlo seed J₁ J₂ SΦ W=
    seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t qref
      E₁ E₂ r loProduct wlo seed J₁ J₂ SΦ W:=by
  unfold seededFactors
  rw [physicalFactors_rescale Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t q qref E₁ E₂ r
    loProduct wlo J₁ J₂ SΦ W hq hr]

end SevenEighths.CenteredMomentSecondReferenceNormalization

end

end OAI
