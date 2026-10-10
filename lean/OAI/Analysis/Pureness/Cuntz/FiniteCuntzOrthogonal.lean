import OAI.Analysis.Pureness.Projections.FiniteSpectralIntegralOrthogonal

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma finitePositiveClass_polar (n : ℕ) (x : FinMatrix A n) :
    finitePositiveClass n (Positive.starMul x) = finitePositiveClass n (Positive.mulStar x) := by
  apply le_antisymm
  · exact (finitePositiveClass_le_iff n _ _).mpr (star_mul_self_cuntzSubequiv x)
  · exact (finitePositiveClass_le_iff n _ _).mpr (mul_star_self_cuntzSubequiv x)

theorem finitePositiveClass_orthogonal_add (n : ℕ) (M N : Positive (FinMatrix A n))
    (hMN : M.1*N.1 = 0) :
    finitePositiveClass n (Positive.add M N) = finitePositiveClass n M + finitePositiveClass n N := by
  obtain ⟨u, v, hu, hv, huu, hvv, hcross⟩ := positive_orthogonal_square_roots M N hMN
  let e := CStarMatrix.reindexₐ ℂ A (finProdFinEquiv : (Fin n × Fin 2) ≃ Fin (n*2))
  let y := e (finiteOrthogonalColumn n (u) (v))
  have hcross' : v * u = 0 := by
    simpa only [star_mul,hu,hv,star_zero] using congrArg star hcross
  have hl : Positive.starMul y = Positive.map (matrixInterleave n) (positiveProduct (Positive.add M N) Positive.zero) := by
    apply Subtype.ext
    change star (e (finiteOrthogonalColumn n (u) (v))) *
      e (finiteOrthogonalColumn n (u) (v)) =
      e (matrixInterleaveRaw n (M.1+N.1,0))
    rw [← map_star,← map_mul,finiteOrthogonalColumn_starMul,
      hu,hv,
      huu,hvv]
  have hr : Positive.mulStar y = Positive.map (matrixInterleave n) (positiveProduct M N) := by
    apply Subtype.ext
    change e (finiteOrthogonalColumn n (u) (v)) *
      star (e (finiteOrthogonalColumn n (u) (v))) =
      e (matrixInterleaveRaw n (M.1,N.1))
    rw [← map_star,← map_mul,finiteOrthogonalColumn_mulStar n _ _
      (by simpa only [hv] using hcross)
      (by simpa only [hu] using hcross'),
      hu,hv,
      huu,hvv]
  have h := finitePositiveClass_polar (n*2) y
  rw [hl,hr,finitePositiveClass_add,finitePositiveClass_add,
    finitePositiveClass_zero,add_zero] at h
  exact h
end CuntzPureness

end

end OAI
