import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfileUniformBound

namespace OAI

/-! # The actual finite-slab solution as a bounded real-linear operator -/

open Set

namespace DefocusingNLS

attribute [local irreducible] expandingProfileTrajectory

noncomputable def expandingProfileOperator (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (m : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) (q : C(Icc (0 : ℝ) T, FourierL2))
    (hq : ∀ t, ‖q t‖ ≤ Q) : FourierL2 →L[ℝ] C(Icc (0 : ℝ) T, FourierL2) :=
  let S := expandingProfileTrajectory a b k L T ha ha1 hk hL hT m Q hQ q hq
  let K := Classical.choose (exists_expandingProfileTrajectory_bound a b k ha ha1 hk m Q hQ)
  let A : FourierL2 →ₗ[ℝ] C(Icc (0 : ℝ) T, FourierL2) :=
    { toFun := S
      map_add' := expandingProfileTrajectory_add a b k L T ha ha1 hk hL hT m Q hQ q hq
      map_smul' := expandingProfileTrajectory_smul a b k L T ha ha1 hk hL hT m Q hQ q hq }
  A.mkContinuous ((K + 1) * Real.exp ((K + 1) * T))
    ((Classical.choose_spec (exists_expandingProfileTrajectory_bound a b k ha ha1 hk m Q hQ)).2
      L T hL hT q hq)

@[simp] theorem expandingProfileOperator_apply (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (m : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) (q : C(Icc (0 : ℝ) T, FourierL2))
    (hq : ∀ t, ‖q t‖ ≤ Q) (f : FourierL2) :
    expandingProfileOperator a b k L T ha ha1 hk hL hT m Q hQ q hq f =
      expandingProfileTrajectory a b k L T ha ha1 hk hL hT m Q hQ q hq f := rfl

noncomputable def expandingProfileEndpoint (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (m : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) (q : C(Icc (0 : ℝ) T, FourierL2))
    (hq : ∀ t, ‖q t‖ ≤ Q) : FourierL2 →L[ℝ] FourierL2 :=
  (ContinuousMap.evalCLM (R := ℝ) ⟨T, hT, le_rfl⟩).comp
    (expandingProfileOperator a b k L T ha ha1 hk hL hT m Q hQ q hq)

@[simp] theorem expandingProfileEndpoint_apply (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (m : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) (q : C(Icc (0 : ℝ) T, FourierL2))
    (hq : ∀ t, ‖q t‖ ≤ Q) (f : FourierL2) :
    expandingProfileEndpoint a b k L T ha ha1 hk hL hT m Q hQ q hq f =
      expandingProfileTrajectory a b k L T ha ha1 hk hL hT m Q hQ q hq f ⟨T, hT, le_rfl⟩ := rfl

end DefocusingNLS

end OAI
