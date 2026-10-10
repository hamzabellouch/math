import OAI.NumberTheory.CubicMoment.Angular.AngularHeatNormalization
import OAI.NumberTheory.CubicMoment.Angular.AngularHeckeFromHeat

namespace OAI

/-! The complete angular analytic package constructed from the finite
Gauss Fourier identity and its norm, via the proved harmonic Poisson formula. -/
noncomputable section
namespace CubicFirstMoment

lemma angularHecke_from_finiteFourier {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) (hu : AngularUnitCompatible q χ ℓ)
    (hn : ℓ ≠ 0 ∨ χ ≠ 1) (G : ℂ) (hG : ‖G‖ = Real.sqrt (norm q))
    (hFourier : ∀ h : Eisenstein, residueFiniteFourier q χ h =
      G*(star χ) (Ideal.Quotient.mk (modulus q) h)) :
    ∃ (root : ℂ) (L Ldual : ℂ → ℂ), ‖root‖ = 1 ∧ Differentiable ℂ L ∧
      (∀ s : ℂ, 1 < s.re → L s =
        normDirichletSeries (angularResidueIdealChar q χ ℓ) idealExponentNorm s) ∧
      (∀ s : ℂ, 1 < s.re → Ldual s =
        normDirichletSeries (angularResidueIdealChar q (star χ) (-ℓ)) idealExponentNorm s) ∧
      HeckeFunctionalEquation (residueHeckeScale q) (|(ℓ:ℝ)|/2) root L Ldual ∧
      ShiftedCompletedHeckeFiniteOrder (residueHeckeScale q) (|(ℓ:ℝ)|/2) L := by
  have hbase : ‖G/(Real.sqrt (norm q):ℝ)‖ = 1 := by
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),hG,
      div_self (Real.sqrt_pos.mpr (norm_pos_of_ne_zero hq)).ne']
  obtain ⟨n,rfl | rfl⟩ := Int.eq_nat_or_neg ℓ
  · let root := (G/(Real.sqrt (norm q):ℝ))*(angularConductorPhase q)^n
    have hr : ‖root‖ = 1 := by
      simp only [root,norm_mul,hbase,norm_pow,angularConductorPhase_norm hq,one_pow,mul_one]
    have hFE : ∀ t : ℝ, 0 < t →
        angularLatticeHeat q χ (n:ℤ) (residueHeckeScale q) (|((n:ℤ):ℝ)|/2) (1/t) =
          root*(t:ℂ)*angularLatticeHeat q (star χ) (-(n:ℤ))
            (residueHeckeScale q) (|((n:ℤ):ℝ)|/2) t := by
      intro t ht
      simpa only [Int.cast_natCast,abs_of_nonneg ((Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ)))] using
        angularHeat_nat_transformation hq χ G hFourier n ht
    obtain ⟨L,Ldual,hL,hs,hds,hfunctional,horder⟩ :=
      angularHecke_from_heatTransformation hq χ (n:ℤ) hu hn root hr hFE
    exact ⟨root,L,Ldual,hr,hL,hs,hds,hfunctional,horder⟩
  · let root := (G/(Real.sqrt (norm q):ℝ))*(angularConductorPhaseNeg q)^n
    have hr : ‖root‖ = 1 := by
      simp only [root,norm_mul,hbase,norm_pow,angularConductorPhaseNeg_norm hq,one_pow,mul_one]
    have hFE : ∀ t : ℝ, 0 < t →
        angularLatticeHeat q χ (-(n:ℤ)) (residueHeckeScale q) (|(Int.cast (-(n:ℤ)) : ℝ)|/2) (1/t) =
          root*(t:ℂ)*angularLatticeHeat q (star χ) (-(-(n:ℤ)))
            (residueHeckeScale q) (|(Int.cast (-(n:ℤ)) : ℝ)|/2) t := by
      intro t ht
      simpa only [Int.cast_neg,Int.cast_natCast,abs_neg,abs_of_nonneg ((Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))),neg_neg] using
        angularHeat_neg_nat_transformation hq χ G hFourier n ht
    obtain ⟨L,Ldual,hL,hs,hds,hfunctional,horder⟩ :=
      angularHecke_from_heatTransformation hq χ (-(n:ℤ)) hu hn root hr hFE
    exact ⟨root,L,Ldual,hr,hL,hs,hds,hfunctional,horder⟩

end CubicFirstMoment

end

end OAI
