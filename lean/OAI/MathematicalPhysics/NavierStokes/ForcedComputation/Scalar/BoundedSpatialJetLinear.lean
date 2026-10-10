import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetOperators

namespace OAI

/-! Fixed linear maps and directional derivatives on bounded spatial jets. -/

noncomputable section
namespace ForcedComputation.BoundedSpatialJets

open scoped Topology BoundedContinuousFunction

variable (E F G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Postcomposition acts boundedly on every derivative in a finite jet. -/
def postcompose (k : ℕ) (L : F →L[ℝ] G) (J : Space E F k) : Space E G k :=
  ofFunction E G k (L ∘ function E F k J)
    (L.contDiff.comp (function_contDiff E F k J)) (‖L‖ * ‖J‖)
    (fun n hn x =>
      (L.norm_iteratedFDeriv_comp_left (function_contDiff E F k J).contDiffAt
        (by exact_mod_cast hn)).trans
        (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_le E F k J n hn x) (norm_nonneg L)))

@[simp] theorem function_postcompose (k : ℕ) (L : F →L[ℝ] G) (J : Space E F k) (x : E) :
    function E G k (postcompose E F G k L J) x = L (function E F k J x) :=
  function_ofFunction E G k _ _ _ _ x

theorem norm_postcompose_le (k : ℕ) (L : F →L[ℝ] G) (J : Space E F k) :
    ‖postcompose E F G k L J‖ ≤ ‖L‖ * ‖J‖ :=
  norm_ofFunction_le E G k _ _ _ _ (mul_nonneg (norm_nonneg L) (norm_nonneg J))

/-- Apply one fixed bounded linear map to a jet-valued function. -/
def postcomposeCLM (k : ℕ) (L : F →L[ℝ] G) : Space E F k →L[ℝ] Space E G k :=
  LinearMap.mkContinuous
    { toFun := postcompose E F G k L
      map_add' := by
        intro J K
        apply function_injective E G k
        ext x
        simp only [function_postcompose, function_add, map_add]
      map_smul' := by
        intro c J
        apply function_injective E G k
        ext x
        simp only [function_postcompose, function_smul, map_smul, RingHom.id_apply] }
    ‖L‖ (norm_postcompose_le E F G k L)

@[simp] theorem postcomposeCLM_apply (k : ℕ) (L : F →L[ℝ] G) (J : Space E F k) :
    postcomposeCLM E F G k L J = postcompose E F G k L J := rfl

theorem norm_postcomposeCLM_le (k : ℕ) (L : F →L[ℝ] G) :
    ‖postcomposeCLM E F G k L‖ ≤ ‖L‖ :=
  (postcomposeCLM E F G k L).opNorm_le_bound (norm_nonneg L) (norm_postcompose_le E F G k L)

theorem postcomposeCLM_truncate (k n : ℕ) (hkn : k ≤ n) (L : F →L[ℝ] G)
    (J : Space E F n) :
    truncateCLM E G k n hkn (postcomposeCLM E F G n L J) =
      postcomposeCLM E F G k L (truncateCLM E F k n hkn J) := by
  apply function_injective E G k
  ext x
  change function E G k (truncate E G k n hkn (postcompose E F G n L J)) x = _
  simp only [function_truncate, postcomposeCLM_apply, function_postcompose]
  rfl

omit [NormedAddCommGroup G] [NormedSpace ℝ G] in
private theorem norm_evaluation_le (v : E) : ‖ContinuousLinearMap.apply ℝ F v‖ ≤ ‖v‖ := by
  apply (ContinuousLinearMap.apply ℝ F v).opNorm_le_bound (norm_nonneg v)
  intro L
  simpa only [ContinuousLinearMap.apply_apply, mul_comm] using L.le_opNorm v

omit [NormedAddCommGroup G] [NormedSpace ℝ G] in
/-- One directional derivative loses one order and has norm at most the direction norm. -/
def directionalDerivativeCLM (k : ℕ) (v : E) : Space E F (k+1) →L[ℝ] Space E F k :=
  (postcomposeCLM E (E →L[ℝ] F) F k (ContinuousLinearMap.apply ℝ F v)).comp
    (derivativeCLM E F k)

omit [NormedAddCommGroup G] [NormedSpace ℝ G] in
@[simp] theorem function_directionalDerivativeCLM (k : ℕ) (v : E)
    (J : Space E F (k+1)) (x : E) :
    function E F k (directionalDerivativeCLM E F k v J) x =
      fderiv ℝ (function E F (k+1) J) x v := by
  change function E F k (postcompose E (E →L[ℝ] F) F k
    (ContinuousLinearMap.apply ℝ F v) (derivative E F k J)) x = _
  rw [function_postcompose, function_derivative]
  rfl

omit [NormedAddCommGroup G] [NormedSpace ℝ G] in
theorem norm_directionalDerivativeCLM_le (k : ℕ) (v : E) :
    ‖directionalDerivativeCLM E F k v‖ ≤ ‖v‖ := by
  calc
    _ ≤ ‖postcomposeCLM E (E →L[ℝ] F) F k (ContinuousLinearMap.apply ℝ F v)‖ *
        ‖derivativeCLM E F k‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖ContinuousLinearMap.apply ℝ F v‖ * 1 :=
      mul_le_mul (norm_postcomposeCLM_le E (E →L[ℝ] F) F k _)
        (norm_derivativeCLM_le_one E F k) (norm_nonneg (derivativeCLM E F k))
        (norm_nonneg (ContinuousLinearMap.apply ℝ F v))
    _ ≤ ‖v‖ := by simpa only [mul_one] using norm_evaluation_le E F v

omit [NormedAddCommGroup G] [NormedSpace ℝ G] in
theorem directionalDerivativeCLM_truncate (k n : ℕ) (hkn : k ≤ n) (v : E)
    (J : Space E F (n+1)) :
    truncateCLM E F k n hkn (directionalDerivativeCLM E F n v J) =
      directionalDerivativeCLM E F k v
        (truncateCLM E F (k+1) (n+1) (Nat.add_le_add_right hkn 1) J) := by
  apply function_injective E F k
  ext x
  change function E F k
    (truncate E F k n hkn (directionalDerivativeCLM E F n v J)) x = _
  rw [function_truncate, function_directionalDerivativeCLM, function_directionalDerivativeCLM]
  have he : (function E F (k+1)
      (truncateCLM E F (k+1) (n+1) (Nat.add_le_add_right hkn 1) J) : E → F) =
      function E F (n+1) J := by
    funext y
    exact function_truncate E F (k+1) (n+1) (Nat.add_le_add_right hkn 1) J y
  rw [he]

end ForcedComputation.BoundedSpatialJets

end

end OAI
