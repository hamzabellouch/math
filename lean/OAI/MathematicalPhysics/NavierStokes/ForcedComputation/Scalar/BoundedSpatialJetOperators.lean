import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetProduct

namespace OAI

/-! Bounded operators needed for the finite-order Volterra equation:
fixed-coefficient multiplication, lossless truncation, and one spatial derivative.
-/

noncomputable section
namespace ForcedComputation.BoundedSpatialJets

open scoped Topology BoundedContinuousFunction

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

@[simp] theorem function_add (k : ℕ) (J K : Space E F k) (x : E) :
    function E F k (J + K) x = function E F k J x + function E F k K x := by
  simpa only [functionMap_apply, BoundedContinuousFunction.add_apply] using
    congrArg (fun f : E →ᵇ F => f x) ((functionMap E F k).map_add J K)

@[simp] theorem function_smul (k : ℕ) (c : ℝ) (J : Space E F k) (x : E) :
    function E F k (c • J) x = c • function E F k J x := by
  simpa only [functionMap_apply, BoundedContinuousFunction.smul_apply] using
    congrArg (fun f : E →ᵇ F => f x) ((functionMap E F k).map_smul c J)

section Product

variable (G H : Type*) [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Fixing the first factor of a pointwise bilinear product gives a bounded linear map. -/
def fixedBilinear (k : ℕ) (B : F →L[ℝ] G →L[ℝ] H) (J : Space E F k) :
    Space E G k →L[ℝ] Space E H k :=
  LinearMap.mkContinuous
    { toFun := bilinear E F G H k B J
      map_add' := by
        intro K L
        apply function_injective E H k
        ext x
        simp only [function_bilinear, function_add, map_add]
      map_smul' := by
        intro c K
        apply function_injective E H k
        ext x
        simp only [function_bilinear, function_smul, map_smul, RingHom.id_apply] }
    (‖B‖ * (2 : ℝ) ^ k * ‖J‖)
    (fun K => norm_bilinear_le E F G H k B J K)

@[simp] theorem fixedBilinear_apply (k : ℕ) (B : F →L[ℝ] G →L[ℝ] H)
    (J : Space E F k) (K : Space E G k) :
    fixedBilinear E F G H k B J K = bilinear E F G H k B J K := rfl

theorem norm_fixedBilinear_le (k : ℕ) (B : F →L[ℝ] G →L[ℝ] H) (J : Space E F k) :
    ‖fixedBilinear E F G H k B J‖ ≤ ‖B‖ * (2 : ℝ) ^ k * ‖J‖ := by
  refine (fixedBilinear E F G H k B J).opNorm_le_bound (by positivity) ?_
  exact fun K => norm_bilinear_le E F G H k B J K

end Product

/-- Forget higher regularity without changing the represented function. -/
def truncate (k n : ℕ) (hkn : k ≤ n) (J : Space E F n) : Space E F k :=
  ofFunction E F k (function E F n J)
    ((function_contDiff E F n J).of_le (by exact_mod_cast hkn)) ‖J‖
    (fun m hm x => norm_iteratedFDeriv_le E F n J m (hm.trans hkn) x)

@[simp] theorem function_truncate (k n : ℕ) (hkn : k ≤ n) (J : Space E F n) (x : E) :
    function E F k (truncate E F k n hkn J) x = function E F n J x :=
  function_ofFunction E F k _ _ _ _ x

theorem norm_truncate_le (k n : ℕ) (hkn : k ≤ n) (J : Space E F n) :
    ‖truncate E F k n hkn J‖ ≤ ‖J‖ :=
  norm_ofFunction_le E F k _ _ _ _ (norm_nonneg J)

/-- The lossless bounded linear map forgetting higher spatial jets. -/
def truncateCLM (k n : ℕ) (hkn : k ≤ n) : Space E F n →L[ℝ] Space E F k :=
  LinearMap.mkContinuous
    { toFun := truncate E F k n hkn
      map_add' := by
        intro J K
        apply function_injective E F k
        ext x
        simp only [function_truncate, function_add]
      map_smul' := by
        intro c J
        apply function_injective E F k
        ext x
        simp only [function_truncate, function_smul, RingHom.id_apply] }
    1 (fun J => by
      change ‖truncate E F k n hkn J‖ ≤ 1 * ‖J‖
      simpa only [one_mul] using norm_truncate_le E F k n hkn J)

theorem norm_truncateCLM_le_one (k n : ℕ) (hkn : k ≤ n) :
    ‖truncateCLM E F k n hkn‖ ≤ 1 := by
  refine (truncateCLM E F k n hkn).opNorm_le_bound zero_le_one ?_
  intro J
  change ‖truncate E F k n hkn J‖ ≤ 1 * ‖J‖
  simpa only [one_mul] using norm_truncate_le E F k n hkn J

/-- A spatial derivative loses exactly one order, with no increase of jet norm. -/
def derivative (k : ℕ) (J : Space E F (k + 1)) : Space E (E →L[ℝ] F) k :=
  ofFunction E (E →L[ℝ] F) k (fderiv ℝ (function E F (k + 1) J))
    ((function_contDiff E F (k + 1) J).fderiv_right (by simp)) ‖J‖
    (fun m hm x => by
      rw [norm_iteratedFDeriv_fderiv]
      exact norm_iteratedFDeriv_le E F (k + 1) J (m + 1) (Nat.add_le_add_right hm 1) x)

@[simp] theorem function_derivative (k : ℕ) (J : Space E F (k + 1)) (x : E) :
    function E (E →L[ℝ] F) k (derivative E F k J) x =
      fderiv ℝ (function E F (k + 1) J) x :=
  function_ofFunction E (E →L[ℝ] F) k _ _ _ _ x

theorem norm_derivative_le (k : ℕ) (J : Space E F (k + 1)) :
    ‖derivative E F k J‖ ≤ ‖J‖ :=
  norm_ofFunction_le E (E →L[ℝ] F) k _ _ _ _ (norm_nonneg J)

private theorem function_differentiable (k : ℕ) (J : Space E F (k + 1)) :
    Differentiable ℝ (function E F (k + 1) J) :=
  (function_contDiff E F (k + 1) J).differentiable (by simp)

/-- Bounded spatial differentiation between consecutive finite jet spaces. -/
def derivativeCLM (k : ℕ) : Space E F (k + 1) →L[ℝ] Space E (E →L[ℝ] F) k :=
  LinearMap.mkContinuous
    { toFun := derivative E F k
      map_add' := by
        intro J K
        apply function_injective E (E →L[ℝ] F) k
        apply BoundedContinuousFunction.ext
        intro x
        simp only [function_derivative, function_add]
        have he : (function E F (k + 1) (J + K) : E → F) =
            fun y => function E F (k + 1) J y + function E F (k + 1) K y := by
          funext y
          exact function_add E F (k + 1) J K y
        rw [he]
        exact fderiv_fun_add (function_differentiable E F k J x)
          (function_differentiable E F k K x)
      map_smul' := by
        intro c J
        apply function_injective E (E →L[ℝ] F) k
        apply BoundedContinuousFunction.ext
        intro x
        simp only [function_derivative, function_smul, RingHom.id_apply]
        have he : (function E F (k + 1) (c • J) : E → F) =
            fun y => c • function E F (k + 1) J y := by
          funext y
          exact function_smul E F (k + 1) c J y
        rw [he]
        exact fderiv_fun_const_smul (function_differentiable E F k J x) c }
    1 (fun J => by
      change ‖derivative E F k J‖ ≤ 1 * ‖J‖
      simpa only [one_mul] using norm_derivative_le E F k J)

theorem norm_derivativeCLM_le_one (k : ℕ) : ‖derivativeCLM E F k‖ ≤ 1 := by
  refine (derivativeCLM E F k).opNorm_le_bound zero_le_one ?_
  intro J
  change ‖derivative E F k J‖ ≤ 1 * ‖J‖
  simpa only [one_mul] using norm_derivative_le E F k J

end ForcedComputation.BoundedSpatialJets

end

end OAI
