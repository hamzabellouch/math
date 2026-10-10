import OAI.Analysis.BoundedHochschild.FiniteNormalOrbit

namespace OAI

/-!
# The norm-closed convex orbit of a normal positive functional

This family remains normal and positive, preserves values on the center,
and satisfies the uniform orthogonal-projection decay in Ringrose Lemma 5.2.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The bounded functional underlying a positive functional. -/
def positiveFunctionalCLM (ψ : M →ₚ[ℂ] ℂ) : StrongDual ℂ M :=
  ⟨ψ.toLinearMap, map_continuous ψ⟩

/-- Pull a functional back along conjugation by a unitary. -/
def unitaryPullback (F : StrongDual ℂ M) (u : unitary M) : StrongDual ℂ M :=
  (F.comp ((ContinuousLinearMap.mul ℂ M).flip (star (u : M)))).comp
    (ContinuousLinearMap.mul ℂ M (u : M))

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma unitaryPullback_apply (F : StrongDual ℂ M) (u : unitary M) (a : M) :
    unitaryPullback F u a = F ((u : M) * a * star (u : M)) := rfl

/-- The closed convex orbit used in the fixed-point construction of a trace. -/
def unitaryOrbitHull (F : StrongDual ℂ M) : Set (StrongDual ℂ M) :=
  closure (convexHull ℝ (Set.range (unitaryPullback F)))

lemma unitaryOrbitHull_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {F : StrongDual ℂ M} (hF : F ∈ normalDual e) :
    unitaryOrbitHull F ⊆ normalDual e := by
  apply closure_minimal _ (normalDual_closed e)
  apply convexHull_min _ ((normalDual e).restrictScalars ℝ).convex
  rintro _ ⟨u, rfl⟩
  apply normalDual_comp e _ _ (HochschildSakai.mul_hasPreadjoint e (u : M))
  exact normalDual_comp e hF _ ((HochschildSakai.abstract_multiplication_normal e).2 (star (u : M)))

omit [PartialOrder M] [StarOrderedRing M] in
lemma unitaryOrbitHull_eval_bound (F : StrongDual ℂ M) (a : M) (C : ℝ)
    (hbound : ∀ u : unitary M, ‖unitaryPullback F u a‖ ≤ C) :
    ∀ G ∈ unitaryOrbitHull F, ‖G a‖ ≤ C := by
  let E := (ContinuousLinearMap.apply ℂ ℂ a : StrongDual ℂ M →L[ℂ] ℂ)
  have hc : convexHull ℝ (Set.range (unitaryPullback F)) ⊆
      E ⁻¹' Metric.closedBall 0 C := by
    apply convexHull_min
    · rintro _ ⟨u, rfl⟩
      simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, E, ContinuousLinearMap.apply_apply] using hbound u
    · exact (convex_closedBall (0 : ℂ) C).linear_preimage (E.restrictScalars ℝ).toLinearMap
  have hh := closure_minimal hc (Metric.isClosed_closedBall.preimage E.continuous)
  intro G hG
  simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, E, ContinuousLinearMap.apply_apply] using hh hG

omit [PartialOrder M] [StarOrderedRing M] in
lemma unitaryOrbitHull_eval_eq (F : StrongDual ℂ M) (a : M) (c : ℂ)
    (hbound : ∀ u : unitary M, unitaryPullback F u a = c) :
    ∀ G ∈ unitaryOrbitHull F, G a = c := by
  let E := (ContinuousLinearMap.apply ℂ ℂ a : StrongDual ℂ M →L[ℂ] ℂ)
  have hc : convexHull ℝ (Set.range (unitaryPullback F)) ⊆ {G | E G = c} := by
    apply convexHull_min
    · rintro _ ⟨u, rfl⟩
      exact hbound u
    · intro G hG H hH r t _hr _ht hrt
      change r • E G + t • E H = c
      rw [hG, hH, ← add_smul, hrt, one_smul]
  exact closure_minimal hc (isClosed_eq E.continuous continuous_const)

lemma unitaryOrbitHull_positive (ψ : M →ₚ[ℂ] ℂ) :
    ∀ G ∈ unitaryOrbitHull (positiveFunctionalCLM ψ), ∀ a : M, 0 ≤ a → 0 ≤ G a := by
  intro G hG a ha
  let E := (ContinuousLinearMap.apply ℂ ℂ a : StrongDual ℂ M →L[ℂ] ℂ)
  have hc : convexHull ℝ (Set.range (unitaryPullback (positiveFunctionalCLM ψ))) ⊆
      E ⁻¹' Set.Ici 0 := by
    apply convexHull_min
    · rintro _ ⟨u, rfl⟩
      exact ψ.map_nonneg (star_right_conjugate_nonneg ha (u : M))
    · intro F hF H hH r t hr ht _
      change 0 ≤ r • E F + t • E H
      exact add_nonneg (smul_nonneg hr hF) (smul_nonneg ht hH)
  exact (closure_minimal hc (isClosed_Ici.preimage E.continuous)) hG

omit [PartialOrder M] [StarOrderedRing M] in
lemma unitaryOrbitHull_central (F : StrongDual ℂ M) {a : M}
    (hc : ∀ b : M, a * b = b * a) :
    ∀ G ∈ unitaryOrbitHull F, G a = F a := by
  apply unitaryOrbitHull_eval_eq F a (F a)
  intro u
  rw [unitaryPullback_apply, ← hc (u : M), mul_assoc,
    (Unitary.mem_iff.mp u.property).2, mul_one]

/-- Uniform decay survives both convex averaging and norm closure. -/
theorem normal_positive_uniform_orbit_hull (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (q : ℕ → M) (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ G ∈ unitaryOrbitHull (positiveFunctionalCLM ψ), ‖G (q n)‖ < ε := by
  have heps : 0 < ε / 2 := half_pos hε
  filter_upwards [normal_positive_uniform_unitary_orbit e hfinite ψ hψ q hq horth
    (ε / 2) heps] with n hn G hG
  exact (unitaryOrbitHull_eval_bound (positiveFunctionalCLM ψ) (q n) (ε / 2)
    (fun u => (hn u).le) G hG).trans_lt (half_lt_self hε)

end KadisonRingrose
end BoundedHochschild

end

end OAI
