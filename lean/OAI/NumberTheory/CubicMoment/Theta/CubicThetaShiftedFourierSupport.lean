import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspStep
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowFiniteFourier

namespace OAI

/-! The actual shifted-cusp finite Fourier coefficient can be nonzero
only at frequencies matching its ramified translation character. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma finiteFourier_translation_eigenvalue {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (f : R → ℂ) (a t : R) (ζ : ℂ)
    (hf : ∀ x : R, f (x+t)=ζ*f x)
    (hF : (∑ x : R, f x*ψ (a*x))≠0) : ζ*ψ (a*t)=1 := by
  classical
  let F : ℂ := ∑ x : R, f x*ψ (a*x)
  have he : F=(ζ*ψ (a*t))*F := by
    calc
      F = ∑ x : R, f (x+t)*ψ (a*(x+t)) :=
        (Equiv.sum_comp (Equiv.addRight t) _).symm
      _ = (ζ*ψ (a*t))*F := by
        simp_rw [hf,mul_add,ψ.map_add_eq_mul]
        dsimp only [F]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
  exact (mul_right_cancel₀ hF (he.symm.trans (one_mul F).symm))

lemma cubicThetaShiftedResidueWeight_step {c : Eisenstein} (hc : primary c)
    (b : Eisenstein) (x : Residues (3*c)) (m : Eisenstein) :
    cubicThetaShiftedResidueWeight b c (x+Ideal.Quotient.mk (modulus (3*c)) (c*m))=
      star (cubicThetaCuspStepValue b m)*cubicThetaShiftedResidueWeight b c x := by
  obtain ⟨u,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [←map_add,cubicThetaShiftedResidueWeight_mk hc,
    cubicThetaShiftedResidueWeight_mk hc,cubicThetaShiftedRowWeight_step hc]

theorem cubicThetaShiftedGaussCoefficient_fourier {c : Eisenstein} (hc : c≠0)
    (b h : Eisenstein) :
    cubicThetaShiftedGaussCoefficient b c h=
      ∑' x : Residues (3*c), cubicThetaShiftedResidueWeight b c x*
        residueFourierChar (3*c) (mul_ne_zero (by norm_num) hc)
          (Ideal.Quotient.mk (modulus (3*c)) h*x) := by
  unfold cubicThetaShiftedGaussCoefficient
  apply tsum_congr
  intro x
  rw [residueFourierChar_mk_mul]

theorem cubicThetaShiftedGaussCoefficient_support {c : Eisenstein} (hc : primary c)
    (b h m : Eisenstein) (hF : cubicThetaShiftedGaussCoefficient b c h≠0) :
    star (cubicThetaCuspStepValue b m)*
      (Real.fourierChar (tracePair (m:ℂ) ((h:ℂ)/(3*traceLambda))):ℂ)=1 := by
  have hc0 := primary_ne_zero hc
  have hcC : (c:ℂ)≠0 := fun he => hc0 (Subtype.ext he)
  have h3c := mul_ne_zero (show (3:Eisenstein)≠0 by norm_num) hc0
  let : Finite (Residues (3*c)) := finite_residues h3c
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  rw [cubicThetaShiftedGaussCoefficient_fourier hc0,tsum_fintype] at hF
  have he := finiteFourier_translation_eigenvalue (residueFourierChar (3*c) h3c)
    (cubicThetaShiftedResidueWeight b c) (Ideal.Quotient.mk (modulus (3*c)) h)
    (Ideal.Quotient.mk (modulus (3*c)) (c*m)) (star (cubicThetaCuspStepValue b m))
    (fun x => cubicThetaShiftedResidueWeight_step hc b x m) hF
  rw [←map_mul,residueFourierChar_mk] at he
  have ht : tracePair ((h*(c*m):Eisenstein):ℂ)
      (1/(((3*c:Eisenstein):ℂ)*traceLambda))=
      tracePair (m:ℂ) ((h:ℂ)/(3*traceLambda)) := by
    unfold tracePair
    congr 2
    push_cast
    simp only [show ((3:Eisenstein):ℂ)=3 from rfl]
    field_simp
  rwa [ht] at he

end CubicFirstMoment

end

end OAI
