import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNonzeroRowCoordinates

namespace OAI

/-! The exact off-diagonal Gram integrand. Its two additive phases are
separated from the common inversion kernel, with the Kubota phase retained. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaGramRowPhase (h k : Eisenstein) (r : CubicThetaBottomRow) : ℂ :=
  star r.phase*cubicThetaHorizontalCharacter h ((r.d:ℂ)/(r.c:ℂ))*
    cubicThetaHorizontalCharacter k (((r.completion.val 0 0:Eisenstein):ℂ)/(r.c:ℂ))

def cubicThetaGramInversionKernel (h k : Eisenstein) (V : C_c(ℝ,ℂ))
    (c z : ℂ) (v : ℝ) : ℂ :=
  star (cubicThetaHorizontalCharacter h z)*V (cubicThetaInversion c (z,v)).2*
    cubicThetaHorizontalCharacter k (cubicThetaInversion c (z,v)).1

lemma cubicThetaFourierProfileTerm_inversion (k : Eisenstein) (r : CubicThetaBottomRow)
    (hr : r.c≠0) (V : C_c(ℝ,ℂ)) {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaFourierProfileTerm k r p V=
      star r.phase*cubicThetaHorizontalCharacter k
        (((r.completion.val 0 0:Eisenstein):ℂ)/(r.c:ℂ))*
      (V (cubicThetaInversion (r.c:ℂ) (p.1+(r.d:ℂ)/(r.c:ℂ),p.2)).2*
        cubicThetaHorizontalCharacter k
          (cubicThetaInversion (r.c:ℂ) (p.1+(r.d:ℂ)/(r.c:ℂ),p.2)).1) := by
  have he := cubicThetaNonzeroRow_coordinates r hr hp
  have hh : r.height p=(cubicThetaInversion (r.c:ℂ)
      (p.1+(r.d:ℂ)/(r.c:ℂ),p.2)).2 := by
    have ht := congrArg Prod.snd he
    change (cubicThetaBottomRow r.completion).height p=_ at ht
    rwa [r.completion_row] at ht
  rw [cubicThetaFourierProfileTerm,cubicThetaRadialProfileTerm,hh,he,
    cubicThetaHorizontalCharacter_add]
  ring

theorem cubicThetaGramRowKernel_identity (h k : Eisenstein) (r : CubicThetaBottomRow)
    (hr : r.c≠0) (V : C_c(ℝ,ℂ)) {p : ℂ × ℝ} (hp : 0<p.2) :
    star (cubicThetaHorizontalCharacter h p.1)*cubicThetaFourierProfileTerm k r p V=
      cubicThetaGramRowPhase h k r*cubicThetaGramInversionKernel h k V
        (r.c:ℂ) (p.1+(r.d:ℂ)/(r.c:ℂ)) p.2 := by
  rw [cubicThetaFourierProfileTerm_inversion k r hr V hp]
  unfold cubicThetaGramRowPhase cubicThetaGramInversionKernel
  rw [cubicThetaHorizontalCharacter_add,star_mul]
  have hu := cubicThetaHorizontalCharacter_unit h ((r.d:ℂ)/(r.c:ℂ))
  linear_combination -(star r.phase*
    cubicThetaHorizontalCharacter k (((r.completion.val 0 0:Eisenstein):ℂ)/(r.c:ℂ))*
    star (cubicThetaHorizontalCharacter h p.1)*
    V (cubicThetaInversion (r.c:ℂ) (p.1+(r.d:ℂ)/(r.c:ℂ),p.2)).2*
    cubicThetaHorizontalCharacter k (cubicThetaInversion (r.c:ℂ)
      (p.1+(r.d:ℂ)/(r.c:ℂ),p.2)).1)*hu

end CubicFirstMoment

end

end OAI
