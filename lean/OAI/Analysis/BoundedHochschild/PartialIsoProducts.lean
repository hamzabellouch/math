import OAI.Analysis.BoundedHochschild.FiniteProjectionExtension

namespace OAI

/-! Products of composable partial isometries and comparison of complements. -/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma partialIso_product_initial (v w : PartialIso M) (h : w.final ≤ v.initial) :
    star ((v : M) * w) * ((v : M) * w) = w.initial := by
  calc
    _ = star (w : M) * (v.initial * (w : M)) := by
      simp only [star_mul, PartialIso.initial, mul_assoc]
    _ = w.initial := by rw [partialIso_left_support v.initial_proj w h]; rfl

/-- Compose two partial isometries when the final support of the second lies
in the initial support of the first. -/
def composePartialIso (v w : PartialIso M) (h : w.final ≤ v.initial) : PartialIso M :=
  ⟨(v : M) * w, by
    rw [mul_assoc, partialIso_product_initial v w h, mul_assoc, w.mul_initial]⟩

@[simp] lemma composePartialIso_initial (v w : PartialIso M) (h : w.final ≤ v.initial) :
    (composePartialIso v w h).initial = w.initial := partialIso_product_initial v w h

lemma composePartialIso_final_le (v w : PartialIso M) (h : w.final ≤ v.initial) :
    (composePartialIso v w h).final ≤ v.final := by
  apply ((composePartialIso v w h).final_proj.le_iff_mul_eq_right v.final_proj).mpr
  change v.final * (((v : M) * w) * star ((v : M) * w)) = _
  rw [← mul_assoc, ← mul_assoc, v.final_mul]
  rfl

/-- Finiteness reverses subequivalence on complementary projections. -/
theorem finite_complement_subequivalence (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) {p q : M} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (v : PartialIso M)
    (hi : v.initial = p) (hf : v.final ≤ q) :
    ∃ w : PartialIso M, w.initial = 1 - q ∧ w.final ≤ 1 - p := by
  obtain ⟨u, hu⟩ := finite_partialIso_extends_unitary e hfinite v
  rw [hi] at hu
  have huunit : star (u : M) * u = 1 ∧ (u : M) * star (u : M) = 1 :=
    Unitary.mem_iff.mp u.property
  have hvq : q * (v : M) = v := partialIso_left_support hq v hf
  have hzero : (1 - q) * (u : M) * p = 0 := by
    rw [mul_assoc, hu, sub_mul, one_mul, hvq, sub_self]
  have hzero' : p * star (u : M) * (1 - q) = 0 := by
    simpa only [star_mul, star_sub, star_one, star_star, hp.isSelfAdjoint.star_eq,
      hq.isSelfAdjoint.star_eq, star_zero, mul_assoc] using congrArg star hzero
  let a := star (u : M) * (1 - q)
  have hai : star a * a = 1 - q := by
    dsimp [a]
    rw [star_mul, star_sub, star_one, hq.isSelfAdjoint.star_eq, star_star]
    calc
      _ = (1 - q) * ((u : M) * star (u : M)) * (1 - q) := by simp only [mul_assoc]
      _ = 1 - q := by rw [huunit.2, mul_one, hq.one_sub.isIdempotentElem.eq]
  have hap : a * (1 - q) = a := by
    dsimp [a]
    rw [mul_assoc, hq.one_sub.isIdempotentElem.eq]
  let w : PartialIso M := ⟨a, by rw [mul_assoc, hai, hap]⟩
  refine ⟨w, hai, ?_⟩
  have hpa : (1 - p) * a = a := by
    change (1 - p) * (star (u : M) * (1 - q)) = _
    rw [sub_mul, one_mul, ← mul_assoc, hzero', sub_zero]
  apply (w.final_proj.le_iff_mul_eq_right hp.one_sub).mpr
  change (1 - p) * (a * star a) = a * star a
  rw [← mul_assoc, hpa]

end KadisonRingrose
end BoundedHochschild

end

end OAI
