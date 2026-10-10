import OAI.Analysis.KadisonKastler.StateOrbitGap

namespace OAI

/-! # Compact asymptotic state-central orbit hulls

The intersection of the decreasing weakly closed convex hulls contains
the original operator and remains in its operator-norm ball.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem weakOperatorBall_convex (M : VonNeumannAlgebra H) (r : ℝ) :
    Convex ℝ (weakOperatorBall M r) := by
  intro X hX Y hY a b ha hb hab
  refine ⟨M.toStarSubalgebra.add_mem
    ((M.toStarSubalgebra.restrictScalars ℝ).smul_mem hX.1 a)
    ((M.toStarSubalgebra.restrictScalars ℝ).smul_mem hY.1 b),?_⟩
  have h := (convex_closedBall (0 : H →L[ℂ] H) r)
    (show X.toCLM ∈ Metric.closedBall 0 r by simpa using hX.2)
    (show Y.toCLM ∈ Metric.closedBall 0 r by simpa using hY.2) ha hb hab
  simpa using h

theorem stateOrbitHull_subset_ball (ξ : H) (a : Algebra M) (δ : ℝ) :
    closedConvexHull ℝ (stateUnitaryOrbit ξ a δ) ⊆ weakOperatorBall M ‖a‖ := by
  apply closedConvexHull_min ?_ (weakOperatorBall_convex M ‖a‖)
    (weakOperatorBall_isCompact M ‖a‖).isClosed
  rintro T ⟨u,_,rfl⟩
  refine ⟨(star u.val*a*u.val).property,?_⟩
  change ‖star u.val*a*u.val‖ ≤ ‖a‖
  calc
    _ ≤ ‖star u.val*a‖*‖u.val‖ := norm_mul_le _ _
    _ ≤ ‖star u.val*a‖ := mul_le_of_le_one_right (norm_nonneg _) (norm_unitary_le_one u)
    _ ≤ ‖star u.val‖*‖a‖ := norm_mul_le _ _
    _ ≤ ‖a‖ := mul_le_of_le_one_left (norm_nonneg _) (norm_unitary_le_one (star u))

theorem stateOrbitHull_compact (ξ : H) (a : Algebra M) (δ : ℝ) :
    IsCompact (closedConvexHull ℝ (stateUnitaryOrbit ξ a δ)) :=
  (weakOperatorBall_isCompact M ‖a‖).of_isClosed_subset isClosed_closedConvexHull
    (stateOrbitHull_subset_ball ξ a δ)

theorem stateOrbitHull_mono (ξ : H) (a : Algebra M) {δ ε : ℝ} (h : δ ≤ ε) :
    closedConvexHull ℝ (stateUnitaryOrbit ξ a δ) ⊆
      closedConvexHull ℝ (stateUnitaryOrbit ξ a ε) := by
  apply (closedConvexHull ℝ).monotone
  rintro T ⟨u,hu,hT⟩
  exact ⟨u,hu.trans h,hT⟩

theorem self_mem_stateOrbitHull (ξ : H) (a : Algebra M) {δ : ℝ} (hδ : 0 ≤ δ) :
    ContinuousLinearMapWOT.ofCLM a.val ∈ closedConvexHull ℝ (stateUnitaryOrbit ξ a δ) := by
  apply subset_closedConvexHull
  refine ⟨1,?_,?_⟩
  · change ‖vectorStateCommutator ξ (1 : Algebra M)‖ ≤ δ
    simpa only [vectorStateCommutator_one,norm_zero] using hδ
  · change ContinuousLinearMapWOT.ofCLM a.val =
      ContinuousLinearMapWOT.ofCLM (star (1 : Algebra M)*a*1).val
    simp only [star_one,one_mul,mul_one]

def stateOrbitCore (ξ : H) (a : Algebra M) : Set (H →WOT[ℂ] H) :=
  {T | ∀ δ : ℝ, 0 < δ → T ∈ closedConvexHull ℝ (stateUnitaryOrbit ξ a δ)}

theorem self_mem_stateOrbitCore (ξ : H) (a : Algebra M) :
    ContinuousLinearMapWOT.ofCLM a.val ∈ stateOrbitCore ξ a :=
  fun _ hδ => self_mem_stateOrbitHull ξ a hδ.le

theorem stateOrbitCore_closed (ξ : H) (a : Algebra M) : IsClosed (stateOrbitCore ξ a) := by
  simp only [stateOrbitCore,Set.ofPred_forall]
  exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_closedConvexHull

theorem stateOrbitCore_convex (ξ : H) (a : Algebra M) : Convex ℝ (stateOrbitCore ξ a) := by
  intro X hX Y hY r s hr hs hrs δ hδ
  exact convex_closedConvexHull (hX δ hδ) (hY δ hδ) hr hs hrs

theorem stateOrbitCore_subset_ball (ξ : H) (a : Algebra M) :
    stateOrbitCore ξ a ⊆ weakOperatorBall M ‖a‖ := by
  intro T hT
  exact stateOrbitHull_subset_ball ξ a 1 (hT 1 zero_lt_one)

theorem stateOrbitCore_compact (ξ : H) (a : Algebra M) : IsCompact (stateOrbitCore ξ a) :=
  (weakOperatorBall_isCompact M ‖a‖).of_isClosed_subset (stateOrbitCore_closed ξ a)
    (stateOrbitCore_subset_ball ξ a)

end

end KadisonKastler

end OAI
