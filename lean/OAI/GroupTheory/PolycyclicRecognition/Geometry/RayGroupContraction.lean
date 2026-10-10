import OAI.GroupTheory.PolycyclicRecognition.Geometry.RayQuotientContraction
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeQuotientHaarAction

namespace OAI

/-!
# Logarithmic contraction of the actual quotient-group action

The Lie-coordinate estimate is transported through the actual bijective
exponential. Compact subsets have bounded logarithmic coordinates. The
action is the exponential conjugate already identified with the descended
Cartan action in `ConeQuotientHaarAction`.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped Manifold

section Logarithm

variable {V E G : Type*} [LieRing V] [LieAlgebra ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  (e : V ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hbij : Function.Bijective Exp)

/-- The logarithm in a specified Lie-algebra realization of a bijective
group exponential. -/
def exponentialLog : G → V :=
  (Equiv.ofBijective (Exp ∘ e) (hbij.comp e.bijective)).symm

@[simp] theorem exponentialLog_exp (v : V) :
    exponentialLog e Exp hbij (Exp (e v)) = v :=
  (Equiv.ofBijective (Exp ∘ e) (hbij.comp e.bijective)).symm_apply_apply v

theorem exp_exponentialLog (g : G) :
    Exp (e (exponentialLog e Exp hbij g)) = g :=
  (Equiv.ofBijective (Exp ∘ e) (hbij.comp e.bijective)).apply_symm_apply g

/-- Conjugation through the exponential acts on its logarithm by the
specified Lie automorphism, exactly. -/
theorem exponentialLog_conjugate (F : V ≃ₗ⁅ℝ⁆ V) (g : G) :
    exponentialLog e Exp hbij (exponentialConjugate e Exp hbij F g) =
      F (exponentialLog e Exp hbij g) := by
  conv_lhs => rw [← exp_exponentialLog e Exp hbij g]
  rw [exponentialConjugate_apply_exp, exponentialLog_exp]

/-- Compact sets in the group have uniformly bounded logarithms in each
finite coordinate basis, using the actual exponential homeomorphism. -/
theorem exists_bound_exponentialLog
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ v, chart v = Exp v)
    {J : Type*} [Fintype J] (b : Basis J ℝ V)
    {K : Set G} (hK : IsCompact K) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ g ∈ K, ‖b.equivFun (exponentialLog e Exp hbij g)‖ ≤ R := by
  let a := (e.toLinearEquiv.symm.trans b.equivFun).toContinuousLinearEquiv
  have hlog (g : G) : exponentialLog e Exp hbij g = e.symm (chart.symm g) := by
    apply e.injective
    apply hbij.injective
    simp only [LieEquiv.coe_coe, LieEquiv.apply_symm_apply]
    rw [exp_exponentialLog e Exp hbij g, ← hchart, chart.apply_symm_apply]
  have hc : Continuous (fun g => b.equivFun (exponentialLog e Exp hbij g)) := by
    simp_rw [hlog]
    exact a.continuous.comp chart.symm.continuous
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨max R 0, le_max_right _ _, fun g hg => (hR g hg).trans (le_max_left _ _)⟩

end Logarithm

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

/-- Every fixed compact set of the actual ray quotient contracts at the
polynomial-exponential rate in logarithmic coordinates. -/
theorem exists_ray_group_compact_contraction
    (α : H →ₗ[ℝ] ℝ)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α)))
    (Exp : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hbij : Function.Bijective Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (hchart : ∀ v, chart v = Exp v) :
    ∃ (b : Basis
        (Fin (finrank ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α))))
        ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α)))
      (p : ℕ) (c : ℝ), 0 < c ∧
      ∀ K : Set Q.carrier, IsCompact K → ∃ A : ℝ, 0 ≤ A ∧
        ∀ (h : H), α h ≤ 0 → ∀ g ∈ K,
        ‖b.equivFun (exponentialLog Q.equiv Exp hbij
          (exponentialConjugate Q.equiv Exp hbij
            (M.coneAdjointAutomorphism T (positiveWeightRay α)
              (positiveWeightRay_add α) h) g))‖ ≤
        A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p * Real.exp (c * α h) := by
  obtain ⟨b, A, p, c, hA, hc, hbound⟩ := M.exists_ray_quotient_contraction T α
  refine ⟨b, p, c, hc, ?_⟩
  intro K hK
  obtain ⟨R, hR, hlog⟩ := exists_bound_exponentialLog Q.equiv Exp hbij chart hchart b hK
  refine ⟨A * R, mul_nonneg hA hR, ?_⟩
  intro h hh g hg
  rw [exponentialLog_conjugate]
  apply (hbound h hh (exponentialLog Q.equiv Exp hbij g)).trans
  calc
    _ ≤ A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p * Real.exp (c * α h) * R := by
      gcongr
      exact hlog g hg
    _ = _ := by ring

end CartanWordModel
end PolycyclicRecognition

end

end OAI
