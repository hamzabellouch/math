import OAI.Analysis.KadisonSimilarity.Tracial.SourceWeakPowers
import OAI.Analysis.BoundedHochschild.FiniteMoments

namespace OAI

/-! Partial unitaries remain in the source while their moments are evaluated
in the ambient algebra. -/

noncomputable section
namespace KadisonSimilarity

open HochschildComparison HochschildPatching BoundedHochschild
open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

namespace SourcePartialUnitary
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- Apply the given inclusion to a partial unitary. -/
def map (φ : A →⋆ₐ[ℂ] B) (v : PartialUnitary A) : PartialUnitary B :=
  ⟨⟨φ (v : A), by
    rw [← map_star, ← map_mul, ← map_mul, v.val.mul_star_mul]⟩, by
    change φ (v : A) * star (φ (v : A)) = star (φ (v : A)) * φ (v : A)
    rw [← map_star, ← map_mul, ← map_mul, v.mul_star_self_eq_support,
      v.star_mul_self_eq_support]⟩

@[simp] theorem coe_map (φ : A →⋆ₐ[ℂ] B) (v : PartialUnitary A) :
    (map φ v : B) = φ (v : A) := rfl

@[simp] theorem support_map (φ : A →⋆ₐ[ℂ] B) (v : PartialUnitary A) :
    (map φ v).support = φ v.support := by
  change star (φ (v : A)) * φ (v : A) = φ (star (v : A) * (v : A))
  rw [map_mul, map_star]

@[simp] theorem map_zero (φ : A →⋆ₐ[ℂ] B) : map φ 0 = 0 :=
  PartialUnitary.ext (show φ (0 : A) = (0 : B) from _root_.map_zero φ)

@[simp] theorem power_map (φ : A →⋆ₐ[ℂ] B) (v : PartialUnitary A) (k : Bool × ℕ) :
    (map φ v).power k = φ (v.power k) := by
  dsimp only [PartialUnitary.power]
  split <;> simp only [coe_map, map_pow, map_star]

theorem map_orthogonalSum (φ : A →⋆ₐ[ℂ] B) (v w : PartialUnitary A)
    (h : v.support * w.support = 0) :
    map φ (v.orthogonalSum w h) =
      (map φ v).orthogonalSum (map φ w) (by rw [support_map, support_map, ← map_mul, h, _root_.map_zero]) := by
  apply PartialUnitary.ext
  simp only [coe_map, PartialUnitary.coe_orthogonalSum, map_add]

end SourcePartialUnitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hNM : N ≤ M)

/-- Source trace-norm convergence is exactly convergence after inclusion. -/
theorem source_gns_tendsto {J : Type*} {l : Filter J}
    {a : J → N.toStarSubalgebra} {b : N.toStarSubalgebra}
    (h : GNSTendsto (vectorPositiveFunctional N υ.vector) a l b) :
    GNSTendsto (vectorPositiveFunctional M υ.vector)
      (fun j => coordinateInclusion hNM (a j)) l (coordinateInclusion hNM b) := by
  apply h.congr
  intro j
  exact (preGNS_norm_map_eq (vectorPositiveFunctional N υ.vector)
    (vectorPositiveFunctional M υ.vector) (coordinateInclusion hNM) (fun _ => rfl)
    (a j - b)).symm.trans (by rw [map_sub])

end KadisonSimilarity

end

end OAI
