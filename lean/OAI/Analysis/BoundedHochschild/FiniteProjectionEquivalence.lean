import OAI.Analysis.BoundedHochschild.FiniteCentralDecomposition
import OAI.Analysis.BoundedHochschild.TraceFreeComparison

namespace OAI

/-!
# Unitary equivalence of finite projections

In a finite von Neumann algebra a partial isometry extends to a unitary.
The proof uses trace-free central comparison of the complementary projections
and finiteness of central corners. No scalar trace is used.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison FinitePathMain

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def adjointPartialIso (v : PartialIso M) : PartialIso M :=
  ⟨star (v : M), by
    simpa only [star_mul, star_star, mul_assoc] using congrArg star v.mul_star_mul⟩

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma adjointPartialIso_initial (v : PartialIso M) :
    (adjointPartialIso v).initial = v.final := by simp [adjointPartialIso, PartialIso.initial, PartialIso.final]

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma adjointPartialIso_final (v : PartialIso M) :
    (adjointPartialIso v).final = v.initial := by simp [adjointPartialIso, PartialIso.initial, PartialIso.final]

/-- Restrict a partial isometry to a central summand. -/
def centralCutPartialIso (z : M) (hz : IsStarProjection z)
    (hc : ∀ a : M, z * a = a * z) (v : PartialIso M) : PartialIso M where
  val := z * (v : M)
  mul_star_mul := by
    have hstar : star (z * (v : M)) = z * star (v : M) := by
      rw [star_mul, hz.isSelfAdjoint.star_eq, hc]
    rw [hstar, central_idempotent_mul z hz.isIdempotentElem.eq hc,
      central_idempotent_mul z hz.isIdempotentElem.eq hc, v.mul_star_mul]

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma centralCutPartialIso_initial (z : M) (hz : IsStarProjection z)
    (hc : ∀ a : M, z * a = a * z) (v : PartialIso M) :
    (centralCutPartialIso z hz hc v).initial = z * v.initial := by
  change star (z * (v : M)) * (z * (v : M)) = z * (star (v : M) * v)
  rw [star_mul, hz.isSelfAdjoint.star_eq, ← hc (star (v : M)),
    central_idempotent_mul z hz.isIdempotentElem.eq hc]

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma centralCutPartialIso_final (z : M) (hz : IsStarProjection z)
    (hc : ∀ a : M, z * a = a * z) (v : PartialIso M) :
    (centralCutPartialIso z hz hc v).final = z * v.final := by
  change (z * (v : M)) * star (z * (v : M)) = z * ((v : M) * star (v : M))
  rw [star_mul, hz.isSelfAdjoint.star_eq, ← hc (star (v : M)),
    central_idempotent_mul z hz.isIdempotentElem.eq hc]

omit [PartialOrder M] [StarOrderedRing M] in
/-- A central cut of a partial isometry exhausts its initial projection
exactly when it exhausts its final projection in a finite algebra. -/
lemma finite_central_initial_iff_final (hfinite : FiniteAlgebra M)
    (z : M) (hz : IsStarProjection z) (hc : ∀ a : M, z * a = a * z)
    (v : PartialIso M) : z * v.initial = z ↔ z * v.final = z := by
  have forward (w : PartialIso M) (hi : z * w.initial = z) : z * w.final = z := by
    let a := centralCutPartialIso z hz hc w
    have hL : z * (a : M) = a := by
      change z * (z * (w : M)) = z * (w : M)
      rw [← mul_assoc, hz.isIdempotentElem.eq]
    have hR : (a : M) * z = a := by rw [← hc, hL]
    have hin : star (a : M) * a = z := by
      change a.initial = z
      change (centralCutPartialIso z hz hc w).initial = z
      rw [centralCutPartialIso_initial, hi]
    have hout := finiteCorner_of_finiteAlgebra hfinite z hz (a : M) hL hR hin
    change a.final = z at hout
    simpa only [a, centralCutPartialIso_final] using hout
  exact ⟨forward v, fun h => by simpa using forward (adjointPartialIso v) (by simpa using h)⟩

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A partial isometry in a finite von Neumann algebra extends to a unitary. -/
theorem finite_partialIso_extends_unitary (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (v : PartialIso M) :
    ∃ u : unitary M, (u : M) * v.initial = v := by
  classical
  obtain ⟨z, w, hz, hwi, hwf, hzf, hzi⟩ := trace_free_central_comparison e
    v.initial_proj.one_sub v.final_proj.one_sub
  have hi : v.initial * w.initial = 0 :=
    HochschildTypeII.projection_orthogonal_of_le_complement v.initial_proj w.initial_proj hwi
  have hf : v.final * w.final = 0 :=
    HochschildTypeII.projection_orthogonal_of_le_complement v.final_proj w.final_proj hwf
  let t := v.orthogonalSum w hi hf
  have hti : t.initial = v.initial + w.initial := PartialIso.orthogonalSum_initial v w hi hf
  have htf : t.final = v.final + w.final := PartialIso.orthogonalSum_final v w hi hf
  have hzc : ∀ a : M, z * a = a * z := fun a => (hz.2 a).eq
  have hzc' : ∀ a : M, (1 - z) * a = a * (1 - z) := by
    intro a
    simp only [sub_mul, mul_sub, one_mul, mul_one, hzc]
  have hzfinal : z * t.final = z := by
    rw [htf, mul_add, hzf, mul_sub, mul_one]
    abel
  have hczinitial : (1 - z) * t.initial = 1 - z := by
    rw [hti, mul_add, hzi, mul_sub, mul_one]
    abel
  have hzinitial := (finite_central_initial_iff_final hfinite z hz.1 hzc t).mpr hzfinal
  have hczfinal := (finite_central_initial_iff_final hfinite (1 - z) hz.1.one_sub hzc' t).mp hczinitial
  have hsplit (a : M) : z * a + (1 - z) * a = a := by noncomm_ring
  have htinitial : t.initial = 1 := by
    rw [← hsplit t.initial, hzinitial, hczinitial]
    abel
  have htfinal : t.final = 1 := by
    rw [← hsplit t.final, hzfinal, hczfinal]
    abel
  let u : unitary M := ⟨(t : M), by
    rw [Unitary.mem_iff]
    exact ⟨htinitial, htfinal⟩⟩
  refine ⟨u, ?_⟩
  change ((v : M) + (w : M)) * v.initial = v
  have hwv : (w : M) * v.initial = 0 := by
    calc
      (w : M) * v.initial = ((w : M) * w.initial) * v.initial := by rw [w.mul_initial]
      _ = 0 := by
        rw [mul_assoc]
        have hzero : w.initial * v.initial = 0 := by
          simpa only [star_mul, v.initial_proj.isSelfAdjoint.star_eq,
            w.initial_proj.isSelfAdjoint.star_eq, star_zero] using congrArg star hi
        rw [hzero, mul_zero]
  rw [add_mul, v.mul_initial, hwv, add_zero]

/-- Equivalent projections in a finite von Neumann algebra are unitarily conjugate. -/
theorem finite_equivalent_unitarily_conjugate (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (v : PartialIso M) :
    ∃ u : unitary M, (u : M) * v.initial * star (u : M) = v.final := by
  obtain ⟨u, hu⟩ := finite_partialIso_extends_unitary e hfinite v
  refine ⟨u, ?_⟩
  calc
    (u : M) * v.initial * star (u : M) =
        ((u : M) * v.initial) * star ((u : M) * v.initial) := by
      rw [star_mul, v.initial_proj.isSelfAdjoint.star_eq]
      simp only [mul_assoc]
      rw [← mul_assoc v.initial v.initial, v.initial_proj.isIdempotentElem.eq]
    _ = v.final := by rw [hu]; rfl

end KadisonRingrose
end BoundedHochschild

end

end OAI
