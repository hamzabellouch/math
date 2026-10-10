import OAI.NumberTheory.CubicMoment.Angular.AngularSquareCompletion
import OAI.NumberTheory.CubicMoment.Estimates.HeckePrimeSquareDisk
import OAI.NumberTheory.CubicMoment.Estimates.CubicPrimeConductorScale

namespace OAI

/-! The sharp angular prime-ideal estimate is derived from the actual
primitive completions. The square uses its own conductor and finite Euler correction. -/
noncomputable section
namespace CubicFirstMoment

lemma primeSetExponent_support_norm_le {q : Eisenstein} (hq : q ≠ 0) :
    idealExponentNorm (primeSetExponent (idealExponentOf q).support) ≤ norm q := by
  rw [←idealExponentOf_norm hq]
  apply idealExponentNorm_mono
  apply (primeSetExponent_le_iff _ _).mpr
  intro p hp
  exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)

lemma angularResidueIdealChar_at_zero (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ℓ : ℤ) : angularResidueIdealChar q χ ℓ 0=1 := by
  simp [angularResidueIdealChar,residueIdealChar,idealExponentGenerator]

theorem primitive_angular_prime_ideal_estimate (hpub : PrimitiveAngularHeckeInput) :
    ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ c ≤ 1/4 ∧ 1 < X0 ∧
    ∀ (q : Eisenstein), q ≠ 0 → ∀ χ : MulChar (Residues q) ℂ,
    PrimitiveResidueCharacter q χ → ∀ ℓ : ℤ, ℓ ≠ 0 → AngularUnitCompatible q χ ℓ →
    ∀ Q : ℝ, 1 ≤ Q → 2*norm q*(1+norm q) ≤ Q → |(ℓ:ℝ)|+7 ≤ Q →
    ∀ X : ℝ, X0 ≤ X → ‖idealPrimeChebyshev (angularResidueIdealChar q χ ℓ) X‖ ≤
      B*primeCancellationWeight c Q X := by
  obtain ⟨B,c,X0,hB,hc,hc1,hX0,hbound⟩ := hecke_prime_ideal_bound_of_square_disk
  refine ⟨B,c,X0,hB,hc,hc1,hX0,?_⟩
  intro q hq χ hp ℓ hℓ hu Q hQ hQN hQk X hX
  obtain ⟨root,L,Ldual,hr,hL,hs,hds,hFE,hcomp⟩ := hpub ℓ q hq χ hp hu (Or.inl hℓ)
  obtain ⟨d,ψ,root2,L2,L2dual,hd,hN,hp2,_hu2,hr2,hL2,hs2,hds2,hFE2,hcomp2,hcorr,hsq⟩ :=
    angular_square_primitive_completion hpub hq χ hℓ hu
  let S := (idealExponentOf q).support
  let A2 := 2*idealExponentNorm (primeSetExponent S)*(1+residueHeckeScale d)
  have hn : 1 ≤ norm q := one_le_norm hq
  have hnd : norm d ≤ norm q := by
    simpa only [normNat_cast] using (Nat.cast_le.mpr hN : (normNat d:ℝ) ≤ (normNat q:ℝ))
  have hscale : residueHeckeScale q ≤ Q :=
    (residueHeckeScale_le_norm hq).trans (by nlinarith)
  have hscale2 : A2 ≤ Q := by
    have hsN : idealExponentNorm (primeSetExponent S) ≤ norm q := primeSetExponent_support_norm_le hq
    have hsd := (residueHeckeScale_le_norm hd).trans hnd
    have hh : A2 ≤ 2*norm q*(1+norm q) := by
      dsimp [A2]
      gcongr; linarith [residueHeckeScale_pos hd]
    exact hh.trans hQN
  have hk2 : |((2*ℓ:ℤ):ℝ)|/2 = |(ℓ:ℝ)| := by
    push_cast
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    ring
  apply hbound (k2 := |((2*ℓ:ℤ):ℝ)|/2) (angularResidueIdealChar_norm_le_one hq χ ℓ)
    (angularResidueIdealChar_at_zero q χ ℓ) (angularResidueIdealChar_add q χ ℓ)
    (angularResidueIdealChar_norm_le_one hq (star χ) (-ℓ)) hL hcorr hs hsq hds
    (residueHeckeScale_pos hq) (show 0<A2 by
      dsimp [A2]
      exact mul_pos (mul_pos (by norm_num) (idealExponentNorm_pos _))
        (by linarith [residueHeckeScale_pos hd]))
    (by positivity) (by positivity) hr.le (show ‖(1:ℂ)‖≤1 by simp) hQ hscale hscale2
    (by have hh := abs_nonneg (ℓ:ℝ); linarith) (by rw [hk2]; exact hQk) hFE hcomp _ X hX
  intro t z hz
  exact euler_corrected_normalized_disk S (angularResidueIdealChar d ψ (2*ℓ))
    (angularResidueIdealChar d (star ψ) (-(2*ℓ)))
    (angularResidueIdealChar_norm_le_one hd ψ (2*ℓ))
    (angularResidueIdealChar_at_zero d ψ (2*ℓ)) (angularResidueIdealChar_add d ψ (2*ℓ))
    (angularResidueIdealChar_norm_le_one hd (star ψ) (-(2*ℓ)))
    (residueHeckeScale_pos hd) (by positivity) hr2.le hL2 hs2 hds2 hFE2 hcomp2 t z (hz.trans (by norm_num))

end CubicFirstMoment

end

end OAI
