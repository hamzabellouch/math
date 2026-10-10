import OAI.Analysis.KadisonKastler.CyclicFactorCompression
import OAI.Analysis.KadisonKastler.ProjectionModuleMaps

namespace OAI

/-! Right modularity is exactly the intertwining condition on the unique
right operator of a cyclic factorization. -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H}

theorem cyclicFactor_right_module_iff
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K)
    (R : H →L[ℂ] factorizationCyclicSpace π L)
    (F : Algebra M →ₗ[ℂ] Algebra M)
    (hF : ∀ a, (F a : H →L[ℂ] H) = (cyclicFactorLeft π L).adjoint.comp
      ((cyclicFactorRepresentation π L a).comp R)) :
    (∀ a b, F (a * b) = F a * b) ↔
      ∀ b, (cyclicFactorRepresentation π L b).comp R = R.comp (b : H →L[ℂ] H) := by
  constructor
  · intro hm b
    apply cyclicFactorRight_unique π L
    intro a
    calc
      _ = (F (a * b) : H →L[ℂ] H) := by
        rw [hF, map_mul]
        ext ξ
        rfl
      _ = (F a * b : Algebra M) := congrArg Subtype.val (hm a b)
      _ = _ := by
        rw [show (F a * b : Algebra M).val = (F a).val * b.val from rfl, hF]
        ext ξ
        rfl
  · intro hi a b
    apply Subtype.ext
    calc
      _ = (cyclicFactorLeft π L).adjoint.comp
          ((cyclicFactorRepresentation π L a).comp
            ((cyclicFactorRepresentation π L b).comp R)) := by
        rw [hF, map_mul]
        ext ξ
        rfl
      _ = (cyclicFactorLeft π L).adjoint.comp
          ((cyclicFactorRepresentation π L a).comp (R.comp b.val)) := by rw [hi b]
      _ = (F a * b : Algebra M).val := by
        rw [show (F a * b : Algebra M).val = (F a).val * b.val from rfl, hF]
        ext ξ
        rfl

theorem representationRowAverage_eq_of_intertwines
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (R : H →L[ℂ] K)
    (hR : ∀ b, (π b).comp R = R.comp (b : H →L[ℂ] H))
    {ι : Type*} [Fintype ι] (r : ι → Algebra M)
    (hr : ∑ i, r i * star (r i) = 1) : representationRowAverage π r R = R := by
  apply ContinuousLinearMap.ext
  intro ξ
  simp only [representationRowAverage, sum_apply, ContinuousLinearMap.comp_apply]
  have hi (i : ι) : π (r i) (R ((star (r i) : H →L[ℂ] H) ξ)) =
      R ((r i : H →L[ℂ] H) ((star (r i) : H →L[ℂ] H) ξ)) :=
    congrArg (fun T : H →L[ℂ] K => T ((star (r i) : H →L[ℂ] H) ξ)) (hR (r i))
  simp_rw [hi]
  rw [← map_sum]
  apply congrArg R
  have he := congrArg (fun a : Algebra M => (a : H →L[ℂ] H) ξ) hr
  simpa only [AddSubmonoidClass.coe_finsetSum, sum_apply, MulMemClass.coe_mul,
    StarMemClass.coe_star, mul_apply_eq_comp, OneMemClass.coe_one, one_apply_eq_self] using he

end

end KadisonKastler

end OAI
