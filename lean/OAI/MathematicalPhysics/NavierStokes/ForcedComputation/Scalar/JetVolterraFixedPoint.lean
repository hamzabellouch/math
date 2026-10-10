import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetOperators
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Contracting

namespace OAI

/-! A short-time Volterra contraction on continuous curves of bounded spatial jets.
-/

noncomputable section
namespace ForcedComputation.JetVolterra

open scoped Topology

variable (A : Type*) [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem affine_contracting (a : A) (L : A →L[ℝ] A) (hL : ‖L‖ < 1) :
    ContractingWith ‖L‖₊ (fun u => a + L u) := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul ?_⟩
  · exact_mod_cast hL
  · intro u v
    simpa only [dist_add_left] using L.lipschitzWith.dist_le_mul u v

variable [CompleteSpace A]

/-- The unique solution of the short-time linear Volterra equation. -/
def solution (a : A) (L : A →L[ℝ] A) (hL : ‖L‖ < 1) : A :=
  ContractingWith.fixedPoint (fun u => a + L u) (affine_contracting A a L hL)

theorem solution_eq (a : A) (L : A →L[ℝ] A) (hL : ‖L‖ < 1) :
    solution A a L hL = a + L (solution A a L hL) :=
  (affine_contracting A a L hL).fixedPoint_isFixedPt.symm

theorem solution_unique (a : A) (L : A →L[ℝ] A) (hL : ‖L‖ < 1)
    (u : A) (hu : u = a + L u) : u = solution A a L hL :=
  (affine_contracting A a L hL).fixedPoint_unique hu.symm

theorem exists_unique (a : A) (L : A →L[ℝ] A) (hL : ‖L‖ < 1) :
    ∃! u : A, u = a + L u :=
  ⟨solution A a L hL, solution_eq A a L hL,
    fun u hu => solution_unique A a L hL u hu⟩

theorem norm_solution_le (a : A) (L : A →L[ℝ] A) (hL : ‖L‖ < 1) :
    ‖solution A a L hL‖ ≤ ‖a‖ / (1 - ‖L‖) := by
  have h := (affine_contracting A a L hL).dist_fixedPoint_le (0 : A)
  simpa only [solution, dist_zero_left, map_zero, add_zero, coe_nnnorm] using h

/-- Stability with respect to the inhomogeneous source, in the same path norm. -/
theorem solution_source_lipschitz (a b : A) (L : A →L[ℝ] A) (hL : ‖L‖ < 1) :
    ‖solution A a L hL - solution A b L hL‖ ≤ ‖a - b‖ / (1 - ‖L‖) := by
  have h := (affine_contracting A a L hL).dist_fixedPoint_fixedPoint_of_dist_le'
    (fun u => b + L u) (solution_eq A a L hL).symm (solution_eq A b L hL).symm
    (C := dist a b) (fun u => by simp only [dist_add_right, le_refl])
  simpa only [dist_eq_norm, coe_nnnorm] using h

variable (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]

/-- An intertwining bounded linear map carries the high-order solution to the lower one. -/
theorem solution_map (a : A) (L : A →L[ℝ] A) (hL : ‖L‖ < 1)
    (P : A →L[ℝ] D) (M : D →L[ℝ] D) (hM : ‖M‖ < 1)
    (hcomm : P.comp L = M.comp P) :
    P (solution A a L hL) = solution D (P a) M hM := by
  apply solution_unique D (P a) M hM
  calc
    P (solution A a L hL) = P (a + L (solution A a L hL)) :=
      congrArg P (solution_eq A a L hL)
    _ = P a + M (P (solution A a L hL)) := by
      rw [map_add]
      congr 1
      exact congrArg (fun Q : A →L[ℝ] D => Q (solution A a L hL)) hcomm

section Paths

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Continuous finite-order jet curves on a closed short-time interval. -/
def Path (k : ℕ) (T : ℝ) := C(Set.Icc (0 : ℝ) T, BoundedSpatialJets.Space E F k)

instance (k : ℕ) (T : ℝ) : NormedAddCommGroup (Path E F k T) :=
  inferInstanceAs (NormedAddCommGroup
    C(Set.Icc (0 : ℝ) T, BoundedSpatialJets.Space E F k))

instance (k : ℕ) (T : ℝ) : NormedSpace ℝ (Path E F k T) :=
  inferInstanceAs (NormedSpace ℝ C(Set.Icc (0 : ℝ) T, BoundedSpatialJets.Space E F k))

instance (k : ℕ) (T : ℝ) [CompleteSpace F] : CompleteSpace (Path E F k T) :=
  inferInstanceAs (CompleteSpace C(Set.Icc (0 : ℝ) T, BoundedSpatialJets.Space E F k))

def pathEquiv (k : ℕ) (T : ℝ) :
    Path E F k T ≃ₗᵢ[ℝ] C(Set.Icc (0 : ℝ) T, BoundedSpatialJets.Space E F k) :=
  LinearIsometryEquiv.refl ℝ _

instance (k : ℕ) (T : ℝ) : CoeFun (Path E F k T)
    (fun _ => Set.Icc (0 : ℝ) T → BoundedSpatialJets.Space E F k) :=
  ⟨fun u => pathEquiv E F k T u⟩

/-- Pointwise truncation of continuous jet curves. -/
def pathTruncate (k n : ℕ) (hkn : k ≤ n) (T : ℝ) :
    Path E F n T →L[ℝ] Path E F k T :=
  (pathEquiv E F k T).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((BoundedSpatialJets.truncateCLM E F k n hkn).compLeftContinuous ℝ
      (Set.Icc (0 : ℝ) T)).comp
        (pathEquiv E F n T).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem pathTruncate_apply (k n : ℕ) (hkn : k ≤ n) (T : ℝ)
    (u : Path E F n T) (t : Set.Icc (0 : ℝ) T) :
    pathTruncate E F k n hkn T u t = BoundedSpatialJets.truncate E F k n hkn (u t) := rfl

theorem norm_pathTruncate_le_one (k n : ℕ) (hkn : k ≤ n) (T : ℝ) :
    ‖pathTruncate E F k n hkn T‖ ≤ 1 := by
  refine (pathTruncate E F k n hkn T).opNorm_le_bound zero_le_one ?_
  intro u
  rw [one_mul]
  change ‖(pathEquiv E F k T) (pathTruncate E F k n hkn T u)‖ ≤ ‖u‖
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
  intro t
  exact (BoundedSpatialJets.norm_truncate_le E F k n hkn (u t)).trans
    ((pathEquiv E F n T u).norm_coe_le_norm t)

variable [CompleteSpace F]

/-- The abstract Volterra equation is uniquely solvable in the actual continuous jet-path space. -/
theorem exists_unique_path (k : ℕ) (T : ℝ) (a : Path E F k T)
    (L : Path E F k T →L[ℝ] Path E F k T) (hL : ‖L‖ < 1) :
    ∃! u : Path E F k T, u = a + L u := exists_unique _ a L hL

/-- Compatible integral operators give compatible solutions across finite spatial orders. -/
theorem solution_truncate (k n : ℕ) (hkn : k ≤ n) (T : ℝ) (a : Path E F n T)
    (L : Path E F n T →L[ℝ] Path E F n T) (hL : ‖L‖ < 1)
    (M : Path E F k T →L[ℝ] Path E F k T) (hM : ‖M‖ < 1)
    (hcomm : (pathTruncate E F k n hkn T).comp L =
      M.comp (pathTruncate E F k n hkn T)) :
    pathTruncate E F k n hkn T (solution _ a L hL) =
      solution _ (pathTruncate E F k n hkn T a) M hM :=
  solution_map _ _ a L hL (pathTruncate E F k n hkn T) M hM hcomm

end Paths
end ForcedComputation.JetVolterra

end

end OAI
