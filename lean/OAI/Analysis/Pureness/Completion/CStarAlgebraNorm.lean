import Mathlib.Analysis.Normed.Unbundled.AlgebraNorm
import Mathlib.Analysis.CStarAlgebra.Hom

namespace OAI
noncomputable section
namespace CuntzPureness

structure CStarAlgebraNorm (R : Type*) [Ring R] [StarRing R] [Algebra ℂ R]
    extends AlgebraNorm ℂ R where
  cstar : ∀ x, toAlgebraNorm (star x * x) = toAlgebraNorm x * toAlgebraNorm x

namespace CStarAlgebraNorm
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]

def ofFaithful {N : Type*} [CStarAlgebra N]
    (f : R →⋆ₐ[ℂ] N) (hf : Function.Injective f) : CStarAlgebraNorm R where
  toFun x := ‖f x‖
  map_zero' := by simp
  add_le' x y := by simpa only [map_add] using norm_add_le (f x) (f y)
  neg' x := by simp
  mul_le' x y := by simpa only [map_mul] using norm_mul_le (f x) (f y)
  eq_zero_of_map_eq_zero' x hx := hf (by simpa using norm_eq_zero.mp hx)
  smul' c x := by simp [norm_smul]
  cstar x := by
    change ‖f (star x * x)‖ = ‖f x‖ * ‖f x‖
    rw [map_mul, map_star, CStarRing.norm_star_mul_self]

@[simp] lemma ofFaithful_apply {N : Type*} [CStarAlgebra N]
    (f : R →⋆ₐ[ℂ] N) (hf : Function.Injective f) (x : R) :
    (ofFaithful f hf).toAlgebraNorm x = ‖f x‖ := rfl

abbrev normedRing (p : CStarAlgebraNorm R) : NormedRing R :=
  p.toAlgebraNorm.toRingNorm.toNormedRing

@[instance_reducible] def normedAlgebra (p : CStarAlgebraNorm R) :
    letI := p.normedRing
    NormedAlgebra ℂ R := by
  letI := p.normedRing
  exact ⟨fun c x => (p.toAlgebraNorm.smul' c x).le⟩

theorem cstarRing (p : CStarAlgebraNorm R) :
    letI := p.normedRing
    CStarRing R := by
  let := p.normedRing
  exact ⟨fun x => (p.cstar x).ge⟩

end CStarAlgebraNorm
end CuntzPureness

end

end OAI
