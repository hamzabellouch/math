import OAI.Analysis.BoundedHochschild.UniformProjectionSums
import OAI.Analysis.BoundedHochschild.NormalOrderIntervals

namespace OAI

/-!
# Weak compactness of positive normal orbits

The positive-functional specialization of Ringrose, Theorem 4.7 and Lemma 5.3.
The gliding-block estimate and complete-additivity criterion ensure that no
singular functional enters the weak-star closure.
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

/-- Weak-star closure of a family of bounded functionals. -/
def weakFunctionalClosure (K : Set (StrongDual ℂ M)) : Set (WeakDual ℂ M) :=
  closure (StrongDual.toWeakDual '' K)

omit [StarOrderedRing M] in
lemma weakFunctionalClosure_positive (K : Set (StrongDual ℂ M))
    (hpos : ∀ F ∈ K, ∀ a : M, 0 ≤ a → 0 ≤ F a)
    {F : WeakDual ℂ M} (hF : F ∈ weakFunctionalClosure K) :
    ∀ a : M, 0 ≤ a → 0 ≤ F a := by
  intro a ha
  apply closure_minimal (t := {G : WeakDual ℂ M | 0 ≤ G a}) _
    (isClosed_le continuous_const (WeakDual.eval_continuous a)) hF
  rintro _ ⟨G, hGK, rfl⟩
  exact hpos G hGK a ha

/-- A uniform orthogonal-sequence estimate makes every positive weak-star
cluster functional normal. -/
theorem weakFunctionalClosure_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (K : Set (StrongDual ℂ M))
    (hpos : ∀ F ∈ K, ∀ a : M, 0 ≤ a → 0 ≤ F a)
    (hnormal : ∀ F ∈ K, F ∈ normalDual e)
    (hdecay : ∀ q : ℕ → M, (∀ n, IsStarProjection (q n)) →
      (∀ m n, m ≠ n → q m * q n = 0) → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ F ∈ K, ‖F (q n)‖ < ε)
    {F : WeakDual ℂ M} (hF : F ∈ weakFunctionalClosure K) :
    WeakDual.toStrongDual F ∈ normalDual e := by
  classical
  have hFpos := weakFunctionalClosure_positive K hpos hF
  let ψ : M →ₚ[ℂ] ℂ :=
    { toLinearMap := (WeakDual.toStrongDual F).toLinearMap
      monotone' := (monotone_iff_map_nonneg _).mpr hFpos }
  apply (mem_normalDual e (positiveFunctionalCLM ψ)).mpr
  apply positive_normal_of_completelyAdditive e ψ
  intro I p hp ho P hP hu hl
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨s, hs⟩ := uniform_orthogonal_sum_remainder K
    (fun G hG => normal_completelyAdditive e (hnormal G hG))
    hdecay I p hp ho P hP hu hl (ε / 2) (half_pos hε)
  have hsmall : (F (P - ∑ i ∈ s, p i)).re ≤ ε / 2 := by
    apply closure_minimal
      (t := {G : WeakDual ℂ M | (G (P - ∑ i ∈ s, p i)).re ≤ ε / 2}) _
      (isClosed_le (Complex.continuous_re.comp (WeakDual.eval_continuous _))
        continuous_const) hF
    rintro _ ⟨G, hGK, rfl⟩
    exact (hs G hGK).le
  refine ⟨s, fun t hst => ?_⟩
  have hsum : (∑ i ∈ s, p i) ≤ ∑ i ∈ t, p i :=
    Finset.sum_le_sum_of_subset_of_nonneg hst (fun i _ _ => (hp i).nonneg)
  have htail : 0 ≤ P - ∑ i ∈ t, p i :=
    sub_nonneg.mpr (orthogonal_projection_finset_sum_le p hp ho hP hu t)
  have horder : 0 ≤ F (P - ∑ i ∈ s, p i) - F (P - ∑ i ∈ t, p i) := by
    rw [← map_sub]
    apply hFpos
    exact sub_nonneg.mpr (sub_le_sub_left hsum P)
  have hposval := hFpos _ htail
  have hnorm : ‖F (P - ∑ i ∈ t, p i)‖ ≤ ε / 2 := by
    have hle : F (P - ∑ i ∈ t, p i) ≤ (ε / 2 : ℝ) := by
      apply Complex.le_def.mpr
      constructor
      · exact ((Complex.nonneg_iff.mp horder).1 |> fun h => by
          rw [Complex.sub_re] at h
          simpa only [Complex.ofReal_re] using (by linarith : (F (P - ∑ i ∈ t, p i)).re ≤ ε / 2))
      · simpa only [Complex.ofReal_im] using (Complex.nonneg_iff.mp hposval).2.symm
    calc
      ‖F (P - ∑ i ∈ t, p i)‖ ≤ ‖((ε / 2 : ℝ) : ℂ)‖ :=
        CStarAlgebra.norm_le_norm_of_le_of_nonneg hle hposval
      _ = ε / 2 := Complex.norm_of_nonneg (half_pos hε).le
  rw [dist_eq_norm, ← map_sum]
  change ‖F (∑ i ∈ t, p i) - F P‖ < ε
  simpa only [map_sub, norm_sub_rev] using hnorm.trans_lt (half_lt_self hε)

omit [PartialOrder M] [StarOrderedRing M] in
lemma unitaryPullback_norm_le (F : StrongDual ℂ M) (u : unitary M) :
    ‖unitaryPullback F u‖ ≤ ‖F‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro a
  have hn : ‖(u : M) * a * star (u : M)‖ = ‖a‖ := by
    rw [show star (u : M) = (star u : unitary M) from rfl,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  simpa only [unitaryPullback_apply, hn] using F.le_opNorm ((u : M) * a * star (u : M))

omit [PartialOrder M] [StarOrderedRing M] in
lemma unitaryOrbitHull_norm_le (F : StrongDual ℂ M) {G : StrongDual ℂ M}
    (hG : G ∈ unitaryOrbitHull F) : ‖G‖ ≤ ‖F‖ := by
  have hsubset : unitaryOrbitHull F ⊆ Metric.closedBall 0 ‖F‖ := by
    apply closure_minimal _ Metric.isClosed_closedBall
    apply convexHull_min _ (convex_closedBall (0 : StrongDual ℂ M) ‖F‖)
    rintro _ ⟨u, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using unitaryPullback_norm_le F u
  simpa only [Metric.mem_closedBall, dist_zero_right] using hsubset hG

/-- The weak-star closure of the positive normal orbit is compact. -/
theorem normal_positive_orbit_compact (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ) :
    IsCompact (weakFunctionalClosure (unitaryOrbitHull (positiveFunctionalCLM ψ))) ∧
      ∀ F ∈ weakFunctionalClosure (unitaryOrbitHull (positiveFunctionalCLM ψ)),
        WeakDual.toStrongDual F ∈ normalDual e := by
  constructor
  · apply (WeakDual.isCompact_closedBall (0 : StrongDual ℂ M)
      ‖positiveFunctionalCLM ψ‖).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (WeakDual.isClosed_closedBall 0 _)
    rintro _ ⟨G, hG, rfl⟩
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      StrongDual.toStrongDual_toWeakDual] using
      unitaryOrbitHull_norm_le (positiveFunctionalCLM ψ) hG
  · intro F hF
    apply weakFunctionalClosure_normal e _ (unitaryOrbitHull_positive ψ)
      (fun _ hG => unitaryOrbitHull_normal e
        ((mem_normalDual e (positiveFunctionalCLM ψ)).mpr hψ) hG) _ hF
    exact fun q hq ho ε hε => normal_positive_uniform_orbit_hull e hfinite ψ hψ q hq ho ε hε

end KadisonRingrose
end BoundedHochschild

end

end OAI
