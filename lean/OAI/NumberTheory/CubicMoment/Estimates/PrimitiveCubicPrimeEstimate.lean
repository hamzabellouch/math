import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveCharacterStar
import OAI.NumberTheory.CubicMoment.Estimates.PublishedPrimitiveHecke
import OAI.NumberTheory.CubicMoment.Estimates.HeckePrimeIdealEstimate

namespace OAI

/-! The character and square analytic data in the sharp prime theorem
are supplied by primitive Hecke completion for a cubic finite character.
Conjugation preserves its conductor and supplies precisely its square. -/
noncomputable section
namespace CubicFirstMoment

theorem primitive_cubic_prime_ideal_estimate (hpub : PrimitiveResidueHeckeInput) :
    ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ c ≤ 1/4 ∧ 1 < X0 ∧
    ∀ (q : Eisenstein), q ≠ 0 → ∀ χ : MulChar (Residues q) ℂ,
    PrimitiveResidueCharacter q χ → χ ≠ 1 → χ^3=1 →
    (∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u)=1) →
    ∀ Q : ℝ, 1 ≤ Q → residueHeckeScale q ≤ Q → 7 ≤ Q →
    ∀ X : ℝ, X0 ≤ X → ‖idealPrimeChebyshev (residueIdealChar q χ) X‖ ≤
      B*primeCancellationWeight c Q X := by
  obtain ⟨B,c,X0,hB,hc,hc1,hX0,hbound⟩ := hecke_prime_ideal_bound_of_analytic_pair
  refine ⟨B,c,X0,hB,hc,hc1,hX0,?_⟩
  intro q hq χ hp hn h3 hu Q hQ hA h7 X hX
  obtain ⟨root,L,Ldual,hr,hL,hs,hds,hFE,hcomp⟩ := hpub q hq χ hp hn hu
  obtain ⟨root2,L2,L2dual,hr2,hL2,hs2,hds2,hFE2,hcomp2⟩ :=
    hpub q hq (star χ) hp.star (star_residue_character_ne_one hn) (star_residue_character_units hu)
  have hs2' : ∀ s : ℂ, 1 < s.re → L2 s=
      normDirichletSeries (fun ν => (residueIdealChar q χ ν)^2) idealExponentNorm s := by
    intro s hss
    rw [hs2 s hss]
    congr 1
    ext ν
    exact (residueIdealChar_cubic_square hq χ h3 ν).symm
  have hds2' : ∀ s : ℂ, 1 < s.re → L2dual s=
      normDirichletSeries (residueIdealChar q χ) idealExponentNorm s := by
    simpa only [star_star] using hds2
  have hcomp' : ShiftedCompletedHeckeFiniteOrder (residueHeckeScale q) 0 L := by
    simpa only [ShiftedCompletedHeckeFiniteOrder,CompletedHeckeFiniteOrder,Complex.ofReal_zero,add_zero] using hcomp
  have hcomp2' : ShiftedCompletedHeckeFiniteOrder (residueHeckeScale q) 0 L2 := by
    simpa only [ShiftedCompletedHeckeFiniteOrder,CompletedHeckeFiniteOrder,Complex.ofReal_zero,add_zero] using hcomp2
  apply hbound (residueIdealChar_norm_le_one hq χ) _ (residueIdealChar_add q χ)
    (residueIdealChar_norm_le_one hq (star χ)) (residueIdealChar_norm_le_one hq χ)
    hL hL2 hs hs2' hds hds2' (residueHeckeScale_pos hq) (residueHeckeScale_pos hq)
    (by norm_num) (by norm_num) hr.le hr2.le hQ hA hA (by simpa using h7) (by simpa using h7)
    hFE hFE2 hcomp' hcomp2' X hX
  simp [residueIdealChar,idealExponentGenerator]

end CubicFirstMoment

end

end OAI
