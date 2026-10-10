import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveProfileGram
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalFourierCharacter

namespace OAI

/-! Exact Bruhat coordinates for the nonidentity rows in the Gram kernel. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaMobius_bruhat_matrix (g : SL(2,ℂ)) (hc : g 1 0≠0) :
    g=cubicThetaTranslationMatrix (g 0 0/g 1 0)*
      cubicThetaInversionMatrix (g 1 0) hc*cubicThetaTranslationMatrix (g 1 1/g 1 0) := by
  have hd := cubicThetaMobius_det g
  have hm : (g : Matrix (Fin 2) (Fin 2) ℂ)=
      (cubicThetaTranslationMatrix (g 0 0/g 1 0) : Matrix (Fin 2) (Fin 2) ℂ)*
      (cubicThetaInversionMatrix (g 1 0) hc : Matrix (Fin 2) (Fin 2) ℂ)*
      (cubicThetaTranslationMatrix (g 1 1/g 1 0) : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two,
        cubicThetaTranslationMatrix,cubicThetaInversionMatrix]
    · field_simp
    · field_simp
      linear_combination -hd
    · field_simp
  apply Subtype.ext
  simpa only [Matrix.SpecialLinearGroup.coe_mul] using hm

lemma cubicThetaMobius_bruhat (g : SL(2,ℂ)) (hc : g 1 0≠0)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaMobius g p=
      ((cubicThetaInversion (g 1 0) (p.1+g 1 1/g 1 0,p.2)).1+g 0 0/g 1 0,
       (cubicThetaInversion (g 1 0) (p.1+g 1 1/g 1 0,p.2)).2) := by
  calc
    _ = cubicThetaMobius (cubicThetaTranslationMatrix (g 0 0/g 1 0)*
        cubicThetaInversionMatrix (g 1 0) hc*cubicThetaTranslationMatrix (g 1 1/g 1 0)) p :=
      congrArg (fun M => cubicThetaMobius M p) (cubicThetaMobius_bruhat_matrix g hc)
    _ = _ := by
      rw [←cubicThetaMobius_comp _ _ hp,cubicThetaMobius_translation]
      have hcpt := cubicThetaMobius_comp (cubicThetaInversionMatrix (g 1 0) hc)
        (cubicThetaTranslationMatrix (g 0 0/g 1 0))
        (p:=(p.1+g 1 1/g 1 0,p.2)) hp
      rw [←hcpt,cubicThetaMobius_inversion hc (p:=(p.1+g 1 1/g 1 0,p.2)) hp,
        cubicThetaMobius_translation]

lemma cubicThetaNonzeroRow_coordinates (r : CubicThetaBottomRow) (hr : r.c≠0)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaMobius (cubicThetaPrincipalComplex r.completion) p=
      ((cubicThetaInversion (r.c:ℂ) (p.1+(r.d:ℂ)/(r.c:ℂ),p.2)).1+
          ((r.completion.val 0 0:Eisenstein):ℂ)/(r.c:ℂ),
       (cubicThetaInversion (r.c:ℂ) (p.1+(r.d:ℂ)/(r.c:ℂ),p.2)).2) := by
  have he := r.completion_row
  have hc : r.completion.val 1 0=r.c := congrArg CubicThetaBottomRow.c he
  have hd : r.completion.val 1 1=r.d := congrArg CubicThetaBottomRow.d he
  have hcz : cubicThetaPrincipalComplex r.completion 1 0≠0 := by
    change ((r.completion.val 1 0:Eisenstein):ℂ)≠0
    rw [hc]
    exact fun hz => hr (Subtype.ext hz)
  simpa only [cubicThetaPrincipalComplex_apply,hc,hd] using
    cubicThetaMobius_bruhat (cubicThetaPrincipalComplex r.completion) hcz hp

end CubicFirstMoment

end

end OAI
