import OAI.Analysis.BoundedHochschild.NormalOrbitInvariance

namespace OAI

/-!
# Normal traces in finite von Neumann algebras

Ringrose, Theorem 5.4: the compact convex unitary orbit of a positive normal
functional contains a normal trace with the same values on the center.
This construction assumes no scalar or center-valued trace.
-/

noncomputable section

open Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma tracial_of_unitary_invariant (F : StrongDual ℂ M)
    (hinv : ∀ (u : unitary M) (a : M), F ((u : M) * a * star (u : M)) = F a) :
    ∀ a b : M, F (a * b) = F (b * a) := by
  classical
  have hu (u : unitary M) (b : M) : F ((u : M) * b) = F (b * (u : M)) := by
    calc
      F ((u : M) * b) = F ((u : M) * (b * (u : M)) * star (u : M)) := by
        simp only [mul_assoc, Unitary.mul_star_self_of_mem u.property, mul_one]
      _ = F (b * (u : M)) := hinv u _
  intro a b
  obtain ⟨u, c, ha, _⟩ := CStarAlgebra.exists_sum_four_unitary a
  rw [ha, Finset.sum_mul, Finset.mul_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_mul_assoc, mul_smul_comm, map_smul, map_smul, hu]

variable [PartialOrder M] [StarOrderedRing M]

/-- Every positive normal functional on a finite von Neumann algebra has a
normal tracial average agreeing with it on the center. -/
theorem exists_normal_tracial_average (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ) :
    ∃ τ : M →ₚ[ℂ] ℂ, TraceInPredual e τ ∧ τ 1 = ψ 1 ∧
      (∀ a b : M, τ (a * b) = τ (b * a)) ∧
      ∀ a : M, (∀ b : M, a * b = b * a) → τ a = ψ a := by
  classical
  let C : Set (WeakSpace ℂ X) := (weakPredualMap e) ⁻¹'
    weakFunctionalClosure (unitaryOrbitHull (positiveFunctionalCLM ψ))
  have hC : IsCompact C := normal_positive_predual_orbit_compact e hfinite ψ hψ
  obtain ⟨z, hz⟩ := hψ
  have hemb : predualEmbedding e z = positiveFunctionalCLM ψ := by
    ext a
    exact (hz a).symm
  have hn : C.Nonempty := by
    refine ⟨toWeakSpace ℂ X z, ?_⟩
    change StrongDual.toWeakDual (predualEmbedding e z) ∈
      weakFunctionalClosure (unitaryOrbitHull (positiveFunctionalCLM ψ))
    rw [hemb]
    apply subset_closure
    refine ⟨positiveFunctionalCLM ψ, ?_, rfl⟩
    have hmem := subset_closure (subset_convexHull ℝ
      (Set.range (unitaryPullback (positiveFunctionalCLM ψ))) (Set.mem_range_self 1))
    simpa only [unitaryPullback_one, unitaryOrbitHull] using hmem
  obtain ⟨x, hx, hfix⟩ := weakCompact_isometric_fixedPoint (unitaryPredualAction e)
    (unitaryPredualAction_one e) (unitaryPredualAction_mul e) C hC hn
    (weakPredualOrbit_convex e _) (weakPredualOrbit_invariant e _)
  let F := weakPredualMap e x
  have hFpos : ∀ a : M, 0 ≤ a → 0 ≤ F a :=
    weakFunctionalClosure_positive _ (unitaryOrbitHull_positive ψ) hx
  let τ : M →ₚ[ℂ] ℂ :=
    { toLinearMap := (WeakDual.toStrongDual F).toLinearMap
      monotone' := (monotone_iff_map_nonneg _).mpr hFpos }
  have hτnormal : TraceInPredual e τ := by
    exact ⟨(toWeakSpace ℂ X).symm x, fun _ => rfl⟩
  have hτcenter (a : M) (ha : ∀ b : M, a * b = b * a) : τ a = ψ a :=
    weakFunctionalClosure_eval_eq _ a (ψ a)
      (unitaryOrbitHull_central (positiveFunctionalCLM ψ) ha) hx
  have hτinv : ∀ (u : unitary M) (a : M), τ ((u : M) * a * star (u : M)) = τ a := by
    intro u a
    have hxfix : unitaryPredualAction e (star u) ((toWeakSpace ℂ X).symm x) =
        (toWeakSpace ℂ X).symm x := congrArg (toWeakSpace ℂ X).symm (hfix (star u))
    have heq := congrArg (predualEmbedding e) hxfix
    rw [predualEmbedding_unitaryAction, star_star] at heq
    exact congrArg (fun f : StrongDual ℂ M => f a) heq
  exact ⟨τ, hτnormal, hτcenter 1 (fun b => by rw [one_mul, mul_one]),
    tracial_of_unitary_invariant (positiveFunctionalCLM τ) hτinv, hτcenter⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
