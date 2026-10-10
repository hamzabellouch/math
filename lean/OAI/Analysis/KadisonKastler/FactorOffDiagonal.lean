import OAI.Analysis.KadisonKastler.SpectralCoefficientBound
import OAI.Analysis.KadisonKastler.ProjectionModuleMaps

namespace OAI

/-! The spectral-cut step of Paulsen's localized row-averaging argument.
If every diagonal compression preserves the norm of a right factor, then
every off-diagonal coefficient vanishes and the factored map is right modular.
-/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H}

local instance offDiagonalOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance offDiagonalPreorder : Preorder (Algebra M) :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance offDiagonalLE : LE (Algebra M) := (CStarAlgebra.spectralOrder _).toLE
local instance offDiagonalStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

omit [CompleteSpace H] in
theorem norm_preserved_by_larger_projection
    (P Q : K →L[ℂ] K) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hPQ : P.comp Q = P) (T : H →L[ℂ] K)
    (hT : ‖P.comp T‖ = ‖T‖) : ‖Q.comp T‖ = ‖T‖ := by
  have hb (A : K →L[ℂ] K) (hA : IsStarProjection A) (B : H →L[ℂ] K) :
      ‖A.comp B‖ ≤ ‖B‖ :=
    (A.opNorm_comp_le B).trans ((mul_le_mul_of_nonneg_right hA.norm_le (norm_nonneg B)).trans_eq
      (one_mul _))
  apply le_antisymm (hb Q hQ T)
  calc
    ‖T‖ = ‖P.comp T‖ := hT.symm
    _ = ‖P.comp (Q.comp T)‖ := by rw [← ContinuousLinearMap.comp_assoc, hPQ]
    _ ≤ ‖Q.comp T‖ := hb P hP _

theorem factor_offDiagonal_eq_zero
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L R : H →L[ℂ] K)
    (F : Algebra M →L[ℂ] Algebra M)
    (hF : ∀ a, (F a : H →L[ℂ] H) = L.adjoint.comp ((π a).comp R))
    (hdiag : ∀ p : AlgebraProjection M,
      ‖(π p.val).comp (R.comp (p.val : H →L[ℂ] H))‖ =
        ‖R.comp (p.val : H →L[ℂ] H)‖)
    (e : AlgebraProjection M) (a : Algebra M) :
    F (a * (1 - e.val)) * e.val = 0 := by
  by_contra hn
  let b := F (a * (1 - e.val)) * e.val
  have hb : b * e.val = b := by
    dsimp [b]
    rw [mul_assoc, e.property.isIdempotentElem.eq]
  obtain ⟨p, t, hpe, hpn, ht, hbound⟩ := exists_corner_spectral_lower_bound e b hb hn
  let P : H →L[ℂ] H := p.val
  let Q : K →L[ℂ] K := π e.val
  have hP : IsStarProjection P := p.property.map M.toStarSubalgebra.subtype
  have hQ : IsStarProjection Q := e.property.map π
  have hPn : P ≠ 0 := by
    intro he
    exact hpn (Subtype.ext he)
  have hep : e.val * p.val = p.val := hpe
  have hnorm : ‖Q.comp (R.comp P)‖ = ‖R.comp P‖ := by
    apply norm_preserved_by_larger_projection (π p.val) Q (p.property.map π) hQ
      (T := R.comp P) (hT := hdiag p)
    change π p.val * π e.val = π p.val
    rw [← map_mul, projection_mul_of_le hpe]
  let A : K →L[ℂ] H := L.adjoint.comp (π a)
  apply projection_norm_equality_no_spectral_gap P hP hPn Q hQ R A hnorm ht
  intro ξ
  have heval : (b : H →L[ℂ] H) (P ξ) = A (R (P ξ) - Q (R (P ξ))) := by
    have hepξ : (e.val : H →L[ℂ] H) (P ξ) = P ξ :=
      congrArg (fun c : Algebra M => (c : H →L[ℂ] H) ξ) hep
    change (F (a * (1 - e.val)) : H →L[ℂ] H)
      ((e.val : H →L[ℂ] H) (P ξ)) = _
    rw [hepξ, hF, map_mul, map_sub, map_one]
    rfl
  have hl := spectral_lower_bound_on_vectors p b hbound ξ
  rw [heval] at hl
  exact hl

theorem right_module_of_no_offDiagonal (F : Algebra M →L[ℂ] Algebra M)
    (hF : ∀ (e : AlgebraProjection M) a, F (a * (1 - e.val)) * e.val = 0) :
    ∀ a b, F (a * b) = F a * b := by
  apply right_module_of_projection_tests M F
  intro e he a
  let p : AlgebraProjection M := ⟨e, he⟩
  let q : AlgebraProjection M := ⟨1 - e, he.one_sub⟩
  have hq := hF q a
  change F (a * (1 - (1 - e))) * (1 - e) = 0 at hq
  rw [sub_sub_cancel] at hq
  have hp := hF p a
  change F (a * (1 - e)) * e = 0 at hp
  have hqe : F (a * e) * e = F (a * e) := by
    rw [mul_sub, mul_one] at hq
    exact (sub_eq_zero.mp hq).symm
  have hs : F a = F (a * e) + F (a * (1 - e)) := by
    rw [← map_add, ← mul_add, add_sub_cancel, mul_one]
  rw [hs, add_mul, hqe, hp, add_zero]

theorem right_module_of_factor_diagonal_norm
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L R : H →L[ℂ] K)
    (F : Algebra M →L[ℂ] Algebra M)
    (hF : ∀ a, (F a : H →L[ℂ] H) = L.adjoint.comp ((π a).comp R))
    (hdiag : ∀ p : AlgebraProjection M,
      ‖(π p.val).comp (R.comp (p.val : H →L[ℂ] H))‖ =
        ‖R.comp (p.val : H →L[ℂ] H)‖) :
    ∀ a b, F (a * b) = F a * b :=
  right_module_of_no_offDiagonal F (factor_offDiagonal_eq_zero π L R F hF hdiag)

end

end KadisonKastler

end OAI
