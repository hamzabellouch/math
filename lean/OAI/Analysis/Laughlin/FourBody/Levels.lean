import OAI.Analysis.Laughlin.FourBody.MiddleForm
import OAI.Analysis.Laughlin.FourBody.NormalForm
import OAI.Analysis.Laughlin.Operators.RowNormalSquare
import OAI.Analysis.Laughlin.Spin.TwoBodyCertificateHaar

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

theorem pairOrbitalUnit_family_sum (Q p j : ℕ) (hp : p < 2*Q-2+1) (hj : j ≤ Q)
    (v : PairOrbitalIndex Q → Space Q) :
    (∑ i, (pairOrbitalUnit Q p j i : ℂ) • v i) = v (⟨p,hp⟩,⟨j,by omega⟩) := by
  classical
  have he (i : PairOrbitalIndex Q) : (i.1.val=p ∧ i.2.val=j) ↔
      i=(⟨p,hp⟩,⟨j,by omega⟩) := by
    constructor
    · rintro ⟨h1,h2⟩; exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · intro h; subst i; exact ⟨rfl,rfl⟩
  simp only [pairOrbitalUnit,apply_ite,Complex.ofReal_one,Complex.ofReal_zero,
    ite_smul,one_smul,zero_smul,he]
  simp

noncomputable def sourceRowLevel (Q t T : ℕ) (entries : List (ℕ × ℕ × ℤ))
    (x : Space Q) : Space Q :=
  ∑ i, (threeBodyLevelVector Q t T entries i : ℂ) • sourceThreeEnd Q i x

theorem contractionForm_realOuter {I : Type*} [Fintype I] (Q : ℕ)
    (L : I → Module.End ℂ (Space Q)) (u v : I → ℝ) (x : Space Q) :
    contractionForm Q L ((realOuter u v).map Complex.ofReal) x =
      occupationInner Q (∑ i, (u i : ℂ) • L i x) (∑ j, (v j : ℂ) • L j x) := by
  have he : (realOuter u v).map Complex.ofReal =
      complexOuter (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) := by
    ext i j
    simp [realOuter,complexOuter]
  rw [he,contractionForm_outer_cross]
  simp only [Complex.star_def,Complex.conj_ofReal]

theorem threeBodyLevelMatrix_Fock (Q t T : ℕ) (ell : ℤ)
    (entries : List (ℕ × ℕ × ℤ)) (ht : t < 2*Q-2+1) (hT : T-t ≤ Q) (x : Space Q) :
    contractionForm Q (sourceThreeEnd Q)
      ((threeBodyLevelMatrix Q t T ell entries).map Complex.ofReal) x =
      ((ell : ℂ)/10^7) *
        (occupationInner Q (annihilate ⟨T-t,by omega⟩ (sourcePairEnd Q t x))
          (sourceRowLevel Q t T entries x) +
        occupationInner Q (sourceRowLevel Q t T entries x)
          (annihilate ⟨T-t,by omega⟩ (sourcePairEnd Q t x))) +
      (occupationNormSq Q (sourceRowLevel Q t T entries x) : ℂ) := by
  have hadd (M N : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ) :
      (M+N).map Complex.ofReal = M.map Complex.ofReal + N.map Complex.ofReal := by
    ext i j; simp
  have hsmul (r : ℝ) (M : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ) :
      (r • M).map Complex.ofReal = (r : ℂ) • M.map Complex.ofReal := by
    ext i j; simp
  simp only [threeBodyLevelMatrix,hadd,hsmul,contractionForm_add,contractionForm_smul,
    contractionForm_realOuter,pairOrbitalUnit_family_sum Q t (T-t) ht hT]
  simp only [sourceRowLevel,sourceThreeEnd,Module.End.mul_apply,occupationInner_self,
    Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_ofNat,
    Complex.ofReal_intCast]

end Laughlin.Fock

end OAI
