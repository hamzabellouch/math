import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CompactDetectorEvaluation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorForceProgram

namespace OAI

/-! A finite force program relative to an arbitrary effectively supplied
planar field.  The rational time prefix is selected before any evaluation;
all spatial and time derivatives are compiled by the local chain rule. -/

noncomputable section
namespace ForcedComputation.VelocityDetector.CompactProgram
open ShearFlows Filter
open scoped ContDiff Topology BigOperators

def components (V : ℝ → Plane → Plane) : PlanarComponents :=
  fun j y => V y.1 (horizontal y.2) j

theorem components_smooth {V : ℝ → Plane → Plane}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (j : Fin 2) :
    ContDiff ℝ ∞ (components V j) := by
  have hi : ContDiff ℝ ∞ (fun y : SpaceTime => (y.1, horizontal y.2)) := by
    simpa only [Function.comp_def, horizontalLinear_eq] using
      contDiff_fst.prodMk (horizontalLinear.contDiff.comp contDiff_snd)
  exact (contDiff_apply ℝ ℝ j).comp (hV.comp hi)

def sum (l : List DetectorExpr) : DetectorExpr :=
  l.foldr .add (.known (.const 0))

theorem sum_valid {l : List DetectorExpr} (hl : ∀ e ∈ l, e.Valid) : (sum l).Valid := by
  induction l with
  | nil => trivial
  | cons e l ih => exact ⟨hl e (by simp), ih (fun f hf => hl f (by simp [hf]))⟩

theorem sum_value (F : PlanarComponents) (l : List DetectorExpr) (y : SpaceTime) :
    (sum l).val F y = (l.map (fun e => e.val F y)).sum := by
  induction l with
  | nil => simp only [sum, List.foldr_nil, DetectorExpr.val, ClockedExpr.val,
      List.map_nil, List.sum_nil, Rat.cast_zero]
  | cons e l ih =>
    change e.val F y + (sum l).val F y = _
    simp only [List.map_cons, List.sum_cons, ih]

theorem sum_ofFn_valid {n : ℕ} (e : Fin n → DetectorExpr) (he : ∀ j, (e j).Valid) :
    (sum (List.ofFn e)).Valid :=
  sum_valid (fun f hf => by obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hf; exact he j)

theorem sum_ofFn_value (F : PlanarComponents) {n : ℕ} (e : Fin n → DetectorExpr)
    (y : SpaceTime) : (sum (List.ofFn e)).val F y = ∑ j, (e j).val F y := by
  rw [sum_value, List.map_ofFn, List.sum_ofFn]
  rfl

abbrev Vector := Fin 3 → DetectorExpr

def Valid (c : Vector) : Prop := ∀ j, (c j).Valid
def value (F : PlanarComponents) (c : Vector) : Velocity := fun y j => (c j).val F y
def diffWord (c : Vector) (α : List (Fin 4)) : Vector := fun j => (c j).diffWord α

theorem value_smooth {F : PlanarComponents} (hF : ∀ j, ContDiff ℝ ∞ (F j))
    {c : Vector} (hc : Valid c) : ContDiff ℝ ∞ (value F c) :=
  contDiff_pi.mpr (fun j => (c j).smooth hF (hc j))

theorem value_diffWord {F : PlanarComponents} (hF : ∀ j, ContDiff ℝ ∞ (F j))
    {c : Vector} (hc : Valid c) (α : List (Fin 4)) :
    value F (diffWord c α) = mixedDerivative (value F c) α := by
  induction α with
  | nil => rfl
  | cons k α ih =>
    funext y j
    rw [mixedDerivative, ← ih]
    have hd := fderiv_pi (fun i =>
      (((c i).diffWord α).smooth hF ((c i).valid_diffWord (hc i) α)).differentiable (by simp) y)
    change ((c j).diffWord (k :: α)).val F y =
      (fderiv ℝ (value F (diffWord c α)) y (spaceTimeDirection k)) j
    change fderiv ℝ (value F (diffWord c α)) y = _ at hd
    rw [hd]
    exact ((c j).diffWord α).val_diff hF ((c j).valid_diffWord (hc j) α) k y

def residualCode (c : Vector) : Vector := fun k =>
  .add (.add ((c k).diff 0)
    (.mul (.known (.const (-1)))
      (sum (List.ofFn (fun j : Fin 3 => (c k).diffWord [j.succ, j.succ])))))
    (sum (List.ofFn (fun j : Fin 3 => .mul (c j) ((c k).diff j.succ))))

theorem residualCode_valid {c : Vector} (hc : Valid c) : Valid (residualCode c) := by
  intro k
  exact ⟨⟨(c k).valid_diff (hc k) 0, trivial,
      sum_ofFn_valid _ (fun _ => (c k).valid_diffWord (hc k) _)⟩,
    sum_ofFn_valid _ (fun j => ⟨hc j, (c k).valid_diff (hc k) j.succ⟩)⟩

theorem residualCode_value {F : PlanarComponents} (hF : ∀ j, ContDiff ℝ ∞ (F j))
    {c : Vector} (hc : Valid c) : value F (residualCode c) = residual 1 (value F c) := by
  funext y k
  rw [residual_eq_force_add]
  change value F (residualCode c) y k = force 1 (value F c) y k + convectiveField (value F c) y k
  rw [force_eq_mixed (value_smooth hF hc),
    convectiveField_eq_mixed (value_smooth hF hc)]
  simp_rw [← value_diffWord hF hc]
  simp only [residualCode, value, DetectorExpr.val, ClockedExpr.val, sum_ofFn_value,
    diffWord, DetectorExpr.diffWord, Finset.sum_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Rat.cast_neg, Rat.cast_one, one_mul]
  ring

def driftTerm (C L n : ℕ) : Vector :=
  ![.mul (.known (.profile (phaseExpression C L n).diff)) (.input (phaseExpression C L n) [] 0),
    .mul (.known (.profile (phaseExpression C L n).diff)) (.input (phaseExpression C L n) [] 1),
    .known (.const 0)]

theorem driftTerm_valid (C L n : ℕ) : Valid (driftTerm C L n) := by
  intro j
  fin_cases j <;> trivial

theorem driftTerm_value (V : ℝ → Plane → Plane) (C L n : ℕ) (y : SpaceTime) :
    value (components V) (driftTerm C L n) y =
      triangularLift (fun x => detectorDriftTerm V C L n (y.1, x)) (fun _ => 0) y.2 := by
  rw [triangularLift_eq]
  ext j
  fin_cases j <;>
    simp [value, driftTerm, DetectorExpr.val, ClockedExpr.val, componentJet,
      ClockedExpr.scalarMixed, components, clockedPoint, phaseExpression_diff_val,
      phaseExpression_val, detectorDriftTerm, atHeight]

def driftPrefix (C L N : ℕ) : Vector := fun j =>
  sum (List.ofFn (fun n : Fin N => driftTerm C L n j))

theorem driftPrefix_valid (C L N : ℕ) : Valid (driftPrefix C L N) :=
  fun j => sum_ofFn_valid _ (fun n => driftTerm_valid C L n j)

theorem driftPrefix_value (V : ℝ → Plane → Plane) (C L N : ℕ) :
    value (components V) (driftPrefix C L N) =
      triangularVelocity (prefixDrift V C L N) (fun _ _ => 0) := by
  funext y
  have he : value (components V) (driftPrefix C L N) y =
      ∑ n : Fin N, value (components V) (driftTerm C L n) y := by
    ext j
    simpa only [value, driftPrefix, Finset.sum_apply] using
      sum_ofFn_value (components V) (fun n : Fin N => driftTerm C L n j) y
  rw [he]
  simp_rw [driftTerm_value]
  simp only [triangularVelocity, triangularLift, prefixDrift, map_sum, zero_smul, add_zero]

def sourcePrefix (C L N : ℕ) : Vector := fun j =>
  .known (verticalSourceExpression C L N j)

theorem sourcePrefix_valid (C L N : ℕ) : Valid (sourcePrefix C L N) :=
  verticalSourceExpression_valid C L N

theorem sourcePrefix_value (F : PlanarComponents) (C L N : ℕ) :
    value F (sourcePrefix C L N) = triangularVelocity (fun _ _ => 0) (prefixSource C L N) :=
  verticalSourceExpression_value C L N

def forcePrefix (C L N : ℕ) : Vector := fun j =>
  .add (residualCode (driftPrefix C L N) j) (sourcePrefix C L N j)

theorem forcePrefix_valid (C L N : ℕ) : Valid (forcePrefix C L N) :=
  fun j => ⟨residualCode_valid (driftPrefix_valid C L N) j, sourcePrefix_valid C L N j⟩

theorem forcePrefix_value {V : ℝ → Plane → Plane}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (C L N : ℕ) :
    value (components V) (forcePrefix C L N) =
      residual 1 (triangularVelocity (prefixDrift V C L N) (fun _ _ => 0)) +
        triangularVelocity (fun _ _ => 0) (prefixSource C L N) := by
  have he : value (components V) (forcePrefix C L N) =
      value (components V) (residualCode (driftPrefix C L N)) +
        value (components V) (sourcePrefix C L N) := rfl
  rw [he, residualCode_value (components_smooth hV) (driftPrefix_valid C L N),
    driftPrefix_value, sourcePrefix_value]

theorem forcePrefix_germ {V : ℝ → Plane → Plane}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (C L N : ℕ) (y : SpaceTime)
    (hN : y.1 + 1 ≤ (N : ℝ)) :
    detectorForce V C L =ᶠ[𝓝 y] value (components V) (forcePrefix C L N) := by
  have ha := detectorDrift_prefix_germ V C L N (y.1, horizontalLinear y.2) hN
  have hh := detectorSource_prefix_germ C L N (y.1, horizontalLinear y.2) hN
  have hz : Function.uncurry (fun _ : ℝ => fun _ : Plane => (0 : ℝ)) =ᶠ[
      𝓝 (y.1, horizontalLinear y.2)] Function.uncurry (fun _ : ℝ => fun _ : Plane => (0 : ℝ)) :=
    Filter.EventuallyEq.rfl
  have hav : Function.uncurry (fun _ : ℝ => fun _ : Plane => (0 : Plane)) =ᶠ[
      𝓝 (y.1, horizontalLinear y.2)] Function.uncurry (fun _ : ℝ => fun _ : Plane => (0 : Plane)) :=
    Filter.EventuallyEq.rfl
  rw [forcePrefix_value hV, detectorForce, triangularForce_eq_residual (detectorDrift_smooth hV C L)]
  exact (residual_eventuallyEq (triangularVelocity_congr_germ ha hz) 1).add
    (triangularVelocity_congr_germ hav hh)

def evaluateUnitForce {V : ℝ → Plane → Plane}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (o : PlanarJetOracle (components V))
    (C L : ℕ) (α : List (Fin 4)) (a : ℕ → RationalSpaceTime)
    (ε : ℚ) (hε : 0 < ε) : RationalVector := fun j =>
  let N := forcePrefixLength (a 0).1
  DetectorExpr.evaluate o (components_smooth hV) ((forcePrefix C L N j).diffWord α)
    ((forcePrefix C L N j).valid_diffWord (forcePrefix_valid C L N j) α) a ε hε

theorem evaluateUnitForce_spec {V : ℝ → Plane → Plane}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (o : PlanarJetOracle (components V))
    (C L : ℕ) (α : List (Fin 4)) (a : ℕ → RationalSpaceTime) {y : SpaceTime}
    (ha : IsFastName a y) (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative (detectorForce V C L) α y -
      rationalVector (evaluateUnitForce hV o C L α a ε hε)‖ ≤ (ε : ℝ) := by
  have ht : |y.1 - ((a 0).1 : ℝ)| ≤ 1 := by
    have h := (norm_fst_le (y - rationalPoint (a 0))).trans (ha 0)
    simpa only [Prod.fst_sub, rationalPoint, errorTolerance, pow_zero, inv_one,
      Real.norm_eq_abs] using h
  have hg := forcePrefix_germ hV C L (forcePrefixLength (a 0).1) y (forcePrefixLength_bound _ ht)
  rw [(mixedDerivative_eventuallyEq hg α).self_of_nhds,
    ← value_diffWord (components_smooth hV) (forcePrefix_valid C L _)]
  apply (pi_norm_le_iff_of_nonneg (Rat.cast_nonneg.mpr hε.le)).mpr
  intro j
  exact DetectorExpr.evaluate_spec o (components_smooth hV)
    ((forcePrefix C L _ j).valid_diffWord (forcePrefix_valid C L _ j) α) a ha ε hε

def unitForceBound {V : ℝ → Plane → Plane} (o : PlanarJetOracle (components V))
    (C L : ℕ) (α : List (Fin 4)) (T : ℚ) : ℚ :=
  ∑ j : Fin 3, ((forcePrefix C L (forcePrefixLength T) j).diffWord α).bound o (|T| + 2)

theorem unitForceBound_nonneg {V : ℝ → Plane → Plane} (o : PlanarJetOracle (components V))
    (C L : ℕ) (α : List (Fin 4)) (T : ℚ) : 0 ≤ unitForceBound o C L α T :=
  Finset.sum_nonneg (fun _ _ => DetectorExpr.bound_nonneg o _ _)

theorem unitForceBound_spec {V : ℝ → Plane → Plane}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (o : PlanarJetOracle (components V))
    (C L : ℕ) (α : List (Fin 4)) (T : ℚ) {y : SpaceTime}
    (ht : 0 ≤ y.1) (hT : y.1 ≤ (T : ℝ)) :
    ‖mixedDerivative (detectorForce V C L) α y‖ ≤ (unitForceBound o C L α T : ℝ) := by
  have hN : y.1 + 1 ≤ (forcePrefixLength T : ℝ) := by
    have hc : (T : ℝ) + 2 ≤ (forcePrefixLength T : ℝ) := by
      exact_mod_cast Nat.le_ceil (T + 2)
    linarith
  have hg := forcePrefix_germ hV C L (forcePrefixLength T) y hN
  rw [(mixedDerivative_eventuallyEq hg α).self_of_nhds,
    ← value_diffWord (components_smooth hV) (forcePrefix_valid C L _)]
  apply (pi_norm_le_iff_of_nonneg (Rat.cast_nonneg.mpr (unitForceBound_nonneg o C L α T))).mpr
  intro j
  have ht' : |y.1| ≤ |((|T| + 2 : ℚ) : ℝ)| := by
    rw [abs_of_nonneg ht, Rat.cast_add, Rat.cast_abs, Rat.cast_ofNat,
      abs_of_nonneg (by positivity)]
    exact hT.trans ((le_abs_self _).trans (by linarith))
  have hj := DetectorExpr.val_bound o
    ((forcePrefix C L (forcePrefixLength T) j).valid_diffWord
      (forcePrefix_valid C L (forcePrefixLength T) j) α) (|T| + 2) y ht'
  apply hj.trans
  exact_mod_cast Finset.single_le_sum
    (fun k _ => DetectorExpr.bound_nonneg o (|T| + 2)
      ((forcePrefix C L (forcePrefixLength T) k).diffWord α))
    (Finset.mem_univ j)

end ForcedComputation.VelocityDetector.CompactProgram

end

end OAI
