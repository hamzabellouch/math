import OAI.Analysis.KadisonKastler.CentralProjectionComparison
import OAI.Analysis.KadisonKastler.ReducingRestriction

namespace OAI

/-! # A nonzero factor projection separates its commutant

This is the faithfulness needed when reducing the semifinite spatial
splitting problem to a finite corner.
-/

namespace KadisonKastler

noncomputable section

open Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem commutant_eq_zero_of_mul_factor_projection
    (N : VonNeumannAlgebra H) (hN : ScalarCenter N)
    (p : AlgebraProjection N) (hp : p.val ≠ 0)
    (a : H →L[ℂ] H) (ha : a ∈ N.commutant) (hap : a * p.val.val = 0) : a = 0 := by
  have hf : ∀ c : Algebra N, (∀ b : Algebra N, b * c = c * b) →
      ∃ z : ℂ, c = z • (1 : Algebra N) := by
    intro c hc
    obtain ⟨z, hz⟩ := hN c.val c.property (fun b hb => congrArg Subtype.val (hc ⟨b, hb⟩))
    exact ⟨z, Subtype.ext hz⟩
  have hs := centralSupport_eq_one_of_factor hf p hp
  have hK : projectionOrbitClosure p ≤ a.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro y ⟨b, x, rfl⟩
      change a (b.val (p.val.val x)) = 0
      have hab := (VonNeumannAlgebra.mem_commutant_iff.mp ha b.val b.property).symm
      calc
        a (b.val (p.val.val x)) = b.val (a (p.val.val x)) :=
          congrArg (fun T : H →L[ℂ] H => T (p.val.val x)) hab
        _ = 0 := by
          have hx := congrArg (fun T : H →L[ℂ] H => T x) hap
          change a (p.val.val x) = 0 at hx
          rw [hx, map_zero]
    · exact a.isClosed_ker
  apply ContinuousLinearMap.ext
  intro x
  have hpx : (projectionOrbitClosure p).starProjection x = x := by
    have he : (projectionOrbitClosure p).starProjection = (1 : H →L[ℂ] H) :=
      congrArg Subtype.val hs
    rw [he, one_apply_eq_self]
  exact hK (hpx ▸ (projectionOrbitClosure p).starProjection_apply_mem x)

end

end KadisonKastler

end OAI
