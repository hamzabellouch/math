import OAI.NumberTheory.CubicMoment.Estimates.ResidueGaussianScale
import OAI.NumberTheory.CubicMoment.Estimates.ResidueThetaCompletion

namespace OAI

/-! The primitive Hecke completion constructed from the finite Gauss Fourier
computation. This bridge assumes no analytic continuation or growth result. -/
noncomputable section
namespace CubicFirstMoment

lemma residueLatticeTheta_inversion_from_fourier {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (G : ℂ)
    (hFourier : ∀ h : Eisenstein, residueFiniteFourier q χ h =
      G*(star χ) (Ideal.Quotient.mk (modulus q) h)) :
    ∀ t : ℝ, 0 < t → residueLatticeTheta q χ (residueHeckeScale q) (1/t) =
      (G/(Real.sqrt (norm q):ℝ))*(t:ℂ)*residueLatticeTheta q (star χ) (residueHeckeScale q) t := by
  intro t ht
  rw [residueGaussian_selfDual hq χ (one_div_pos.mpr ht)]
  simp_rw [hFourier]
  have he (h : Eisenstein) : -norm h/(residueHeckeScale q*(1/t)) = -norm h*t/residueHeckeScale q := by
    field_simp
  simp_rw [he,mul_assoc]
  rw [tsum_mul_left]
  change ((1/(Real.sqrt (norm q)*(1/t)):ℝ):ℂ) * (G * residueLatticeTheta q (star χ) (residueHeckeScale q) t) = _
  push_cast
  field_simp

lemma residueHecke_from_finiteFourier {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (hn : χ ≠ 1)
    (hu : ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u) = 1)
    (G : ℂ) (hG : ‖G‖ = Real.sqrt (norm q))
    (hFourier : ∀ h : Eisenstein, residueFiniteFourier q χ h =
      G*(star χ) (Ideal.Quotient.mk (modulus q) h)) :
    ∃ (root : ℂ) (L Ldual : ℂ → ℂ), ‖root‖ = 1 ∧ Differentiable ℂ L ∧
      (∀ s : ℂ, 1 < s.re → L s = normDirichletSeries (residueIdealChar q χ) idealExponentNorm s) ∧
      (∀ s : ℂ, 1 < s.re → Ldual s = normDirichletSeries (residueIdealChar q (star χ)) idealExponentNorm s) ∧
      HeckeFunctionalEquation (residueHeckeScale q) 0 root L Ldual ∧
      CompletedHeckeFiniteOrder (residueHeckeScale q) L := by
  let : Nontrivial (Residues q) := residue_nontrivial_of_nonprincipal χ hn
  let root : ℂ := G/(Real.sqrt (norm q):ℝ)
  have hs : 0 < Real.sqrt (norm q) := Real.sqrt_pos.mpr (norm_pos_of_ne_zero hq)
  have hr : ‖root‖ = 1 := by
    dsimp [root]
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),hG,div_self hs.ne']
  have hr0 : root ≠ 0 := by intro he; rw [he,norm_zero] at hr; norm_num at hr
  have hd (u : Eisensteinˣ) : (star χ) (Ideal.Quotient.mk (modulus q) u) = 1 := by
    rw [MulChar.star_apply,hu,star_one]
  have hFE := residueTheta_inversion_of_lattice hq χ hu hd (residueHeckeScale_pos hq)
    (residueLatticeTheta_inversion_from_fourier hq χ G hFourier)
  obtain ⟨L,Ldual,hL,hseries,hdual,hfunctional,horder⟩ := residueTheta_completion hq χ hr0 hFE
  exact ⟨root,L,Ldual,hr,hL,hseries,hdual,hfunctional,horder⟩

end CubicFirstMoment

end

end OAI
