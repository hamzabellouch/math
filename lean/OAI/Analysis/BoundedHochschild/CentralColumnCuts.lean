import OAI.Analysis.BoundedHochschild.TypeICentralPieces
import OAI.Analysis.BoundedHochschild.OrthogonalProjectionSums

namespace OAI

/-! Extracting homogeneous central pieces from finite column families. -/

noncomputable section

open scoped ComplexOrder BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- If a central cut annihilates the residual of a finite abelian column
family, the cut is a finite homogeneous type I summand. -/
theorem homogeneousCorner_of_annihilated_residual {p z : M} (hp : AbelianProjection p)
    (hz : CentralProjection z) (hz0 : z ≠ 0) {n : ℕ}
    (v : Fin n → PartialIso M) (hi : ∀ i, (v i).initial = p)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0)
    (hann : z * (1 - ∑ i, (v i).final) = 0) : HomogeneousTypeICorner z := by
  classical
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst n
    exact hz0 (by simpa using hann)
  let w (i : Fin n) := centralCutPartialIso z hz.1 (fun a => (hz.2 a).eq) (v i)
  have hzp : IsStarProjection (z * p) := hz.1.mul hp.1 (hz.2 p)
  have hzpp : z * p ≤ p := (hzp.le_iff_mul_eq_left hp.1).mpr
    (by rw [mul_assoc, hp.1.isIdempotentElem.eq])
  have hpz : z * p ≤ z := (hzp.le_iff_mul_eq_right hz.1).mpr
    (by rw [← mul_assoc, hz.1.isIdempotentElem.eq])
  have hwi (i : Fin n) : (w i).initial = z * p := by
    simp only [w, centralCutPartialIso_initial, hi]
  have hwf (i : Fin n) : (w i).final ≤ z := by
    apply ((w i).final_proj.le_iff_mul_eq_right hz.1).mpr
    simp only [w, centralCutPartialIso_final]
    rw [← mul_assoc, hz.1.isIdempotentElem.eq]
  have hwo (i j : Fin n) (hij : i ≠ j) : (w i).final * (w j).final = 0 := by
    simp only [w, centralCutPartialIso_final]
    rw [central_idempotent_mul z hz.1.isIdempotentElem.eq (fun a => (hz.2 a).eq),
      ho i j hij, mul_zero]
  have hws : ∑ i, (w i).final = z := by
    simp only [w, centralCutPartialIso_final, ← Finset.mul_sum]
    rw [mul_sub, mul_one, sub_eq_zero] at hann
    exact hann.symm
  exact homogeneousCorner_of_columns hz.1 (HochschildTypeII.abelian_of_le hp hzp hzpp)
    hpz ⟨0, hn⟩ w hwi hwf hwo hws

end KadisonRingrose
end BoundedHochschild

end

end OAI
