import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedDerivativeGraph
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Calculus.ContDiff.Comp

namespace OAI

/-! A Banach space of bounded continuous spatial jets of any finite order.

The ambient space is a finite product with the maximum of the uniform norms.
Compatibility of consecutive jets is imposed by closed derivative graphs, so
uniform convergence of every jet preserves the spatial derivatives.
-/

noncomputable section
namespace ForcedComputation.BoundedSpatialJets

open scoped Topology BoundedContinuousFunction

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Values of the spatial derivative of order `n`.
The type synonym fixes one normed-space structure throughout the jet family. -/
def Value (n : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F

instance (n : ℕ) : NormedAddCommGroup (Value E F n) :=
  inferInstanceAs (NormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F))

instance (n : ℕ) : NormedSpace ℝ (Value E F n) :=
  inferInstanceAs (NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F))

instance (n : ℕ) [CompleteSpace F] : CompleteSpace (Value E F n) :=
  inferInstanceAs (CompleteSpace (ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F))

/-- Split the first slot of a jet value, with the fixed normed-space structures. -/
def curryMap (n : ℕ) : Value E F (n + 1) ≃ₗᵢ[ℝ] (E →L[ℝ] Value E F n) := by
  convert! (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F) using 1

/-- A zero-order multilinear value is an ordinary value. -/
def valueMap : Value E F 0 ≃ₗᵢ[ℝ] F := by
  convert! (continuousMultilinearCurryFin0 ℝ E F) using 1

/-- Bounded continuous candidate jets through order `k`. -/
abbrev Family (k : ℕ) := (i : Fin (k + 1)) → (E →ᵇ Value E F i.val)

/-- The zeroth index, avoiding modular reduction of a variable-sized `Fin`. -/
abbrev firstIndex (k : ℕ) : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩

@[simp] theorem firstIndex_val (k : ℕ) : (firstIndex k).val = 0 := rfl

/-- Extract two consecutive jets, currying the higher jet as a derivative. -/
def consecutive (k : ℕ) (i : Fin k) :
    Family E F k →L[ℝ]
      ((E →ᵇ Value E F i.val) × (E →ᵇ (E →L[ℝ] Value E F i.val))) :=
  (ContinuousLinearMap.proj i.castSucc).prod
    ((((curryMap E F i.val).toContinuousLinearEquiv.toContinuousLinearMap).compLeftContinuousBounded E).comp (ContinuousLinearMap.proj i.succ))

@[simp] theorem consecutive_apply (k : ℕ) (i : Fin k) (J : Family E F k) :
    consecutive E F k i J =
      (J i.castSucc,
        ((curryMap E F i.val).toContinuousLinearEquiv.toContinuousLinearMap).compLeftContinuousBounded E (J i.succ)) := rfl

/-- Derivative compatibility is a closed linear condition on the finite family. -/
def compatible (k : ℕ) : ClosedSubmodule ℝ (Family E F k) :=
  ⨅ i : Fin k, (boundedDerivativeGraph E (Value E F i.val)).comap (consecutive E F k i)

@[simp] theorem mem_compatible (k : ℕ) (J : Family E F k) :
    J ∈ compatible E F k ↔
      ∀ i : Fin k, ∀ x, HasFDerivAt (J i.castSucc) ((curryMap E F i.val) (J i.succ x)) x := by
  simp only [compatible, ClosedSubmodule.mem_iInf, ClosedSubmodule.mem_comap,
    mem_boundedDerivativeGraph, consecutive_apply,
    ContinuousLinearMap.compLeftContinuousBounded_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]

/-- The Banach space of bounded continuous spatial jets through order `k`. -/
abbrev Space (k : ℕ) := compatible E F k

instance (k : ℕ) [CompleteSpace F] : CompleteSpace (Space E F k) := inferInstance

/-- Bounded linear extraction of any spatial jet. -/
def projection (k : ℕ) (i : Fin (k + 1)) :
    Space E F k →L[ℝ] (E →ᵇ Value E F i.val) :=
  (ContinuousLinearMap.proj i).comp (compatible E F k).toSubmodule.subtypeL

@[simp] theorem projection_apply (k : ℕ) (i : Fin (k + 1)) (J : Space E F k) :
    projection E F k i J = J.val i := rfl

theorem norm_projection_le_one (k : ℕ) (i : Fin (k + 1)) :
    ‖projection E F k i‖ ≤ 1 := by
  refine (projection E F k i).opNorm_le_bound zero_le_one ?_
  intro J
  change ‖J.val i‖ ≤ 1 * ‖J.val‖
  simpa only [one_mul] using norm_le_pi_norm J.val i

/-- Every consecutive pair in a compatible family is an actual derivative pair. -/
theorem hasFDerivAt (k : ℕ) (J : Space E F k) (i : Fin k) (x : E) :
    HasFDerivAt (J.val i.castSucc) ((curryMap E F i.val) (J.val i.succ x)) x :=
  (mem_compatible E F k J.val).mp J.property i x

/-- The Banach norm controls every spatial jet uniformly in the base point. -/
theorem norm_jet_le (k : ℕ) (J : Space E F k) (i : Fin (k + 1)) (x : E) :
    ‖J.val i x‖ ≤ ‖J‖ :=
  (J.val i).norm_coe_le_norm x |>.trans (norm_le_pi_norm J.val i)

/-- Each jet has the differentiability supplied by the remaining higher jets. -/
theorem jet_contDiff (k : ℕ) (J : Space E F k) (n m : ℕ) (h : n + m ≤ k) :
    ContDiff ℝ m (J.val ⟨n, by omega⟩) := by
  induction m generalizing n with
  | zero =>
      exact contDiff_zero.mpr (J.val ⟨n, by omega⟩).continuous
  | succ m ih =>
      let L := (curryMap E F n).toContinuousLinearEquiv.toContinuousLinearMap
      have hnext : n + 1 + m ≤ k := by omega
      have hd : ContDiff ℝ m (fun x => L (J.val ⟨n + 1, by omega⟩ x)) :=
        L.contDiff.comp (ih (n + 1) hnext)
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨_, hd, ?_⟩
      intro x
      exact hasFDerivAt E F k J ⟨n, by omega⟩ x

/-- The ordinary function represented by the zeroth jet. -/
def function (k : ℕ) (J : Space E F k) : E →ᵇ F :=
  (valueMap E F).toContinuousLinearEquiv.toContinuousLinearMap.compLeftContinuousBounded E
    (J.val (firstIndex k))

@[simp] theorem function_apply (k : ℕ) (J : Space E F k) (x : E) :
    function E F k J x = valueMap E F (J.val (firstIndex k) x) := rfl

theorem function_contDiff (k : ℕ) (J : Space E F k) :
    ContDiff ℝ k (function E F k J) :=
  (valueMap E F).toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp (jet_contDiff E F k J 0 k (by omega))

theorem norm_function_le (k : ℕ) (J : Space E F k) (x : E) :
    ‖function E F k J x‖ ≤ ‖J‖ := by
  rw [function_apply, (valueMap E F).norm_map]
  exact norm_jet_le E F k J (firstIndex k) x

/-- Bounded linear extraction of the represented function. -/
def functionMap (k : ℕ) : Space E F k →L[ℝ] (E →ᵇ F) :=
  ((valueMap E F).toContinuousLinearEquiv.toContinuousLinearMap.compLeftContinuousBounded E).comp
    (projection E F k (firstIndex k))

@[simp] theorem functionMap_apply (k : ℕ) (J : Space E F k) :
    functionMap E F k J = function E F k J := rfl

theorem norm_functionMap_le_one (k : ℕ) : ‖functionMap E F k‖ ≤ 1 := by
  refine (functionMap E F k).opNorm_le_bound zero_le_one ?_
  intro J
  rw [one_mul, functionMap_apply]
  exact (BoundedContinuousFunction.norm_le (norm_nonneg J)).mpr
    (norm_function_le E F k J)

/-- The supplied jets are the actual iterated spatial derivatives. -/
theorem iteratedFDeriv_function (k : ℕ) (J : Space E F k) (n : ℕ) (hn : n ≤ k) :
    iteratedFDeriv ℝ n (function E F k J) = J.val ⟨n, by omega⟩ := by
  induction n with
  | zero =>
      funext x
      rw [iteratedFDeriv_zero_eq_comp]
      change (valueMap E F).symm ((valueMap E F) (J.val (firstIndex k) x)) = _
      exact (valueMap E F).symm_apply_apply (J.val (firstIndex k) x)
  | succ n ih =>
      have hprev : n ≤ k := by omega
      rw [iteratedFDeriv_succ_eq_comp_left, ih hprev]
      funext x
      change (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => E) F).symm
          (fderiv ℝ (J.val ⟨n, by omega⟩) x) = _
      have hd := (hasFDerivAt E F k J ⟨n, by omega⟩ x).fderiv
      change fderiv ℝ (J.val ⟨n, by omega⟩) x =
        curryMap E F n (J.val ⟨n + 1, by omega⟩ x) at hd
      change (curryMap E F n).symm (fderiv ℝ (J.val ⟨n, by omega⟩) x) = _
      rw [hd]
      exact (curryMap E F n).symm_apply_apply (J.val ⟨n + 1, by omega⟩ x)

theorem norm_iteratedFDeriv_le (k : ℕ) (J : Space E F k) (n : ℕ) (hn : n ≤ k)
    (x : E) : ‖iteratedFDeriv ℝ n (function E F k J) x‖ ≤ ‖J‖ := by
  rw [iteratedFDeriv_function E F k J n hn]
  exact norm_jet_le E F k J ⟨n, by omega⟩ x

end ForcedComputation.BoundedSpatialJets

end

end OAI
