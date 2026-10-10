import OAI.Analysis.CircleDomains.Sobolev.LiftDifferentials

namespace OAI

/-!
# Intrinsic differentials and cutoff modifications of circle coordinates

The differential is computed in a genuine real quotient chart. Local
integer transition functions make it independent of the chosen lift.
The cutoff staircase descends to the circle and is smooth in the same
charts; no global real lift or extra topological input is required.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def circleRepresentative (t : UnitAddCircle) : ℝ := AddCircle.equivIco 1 0 t

def circleBranch {X : Type*} (f : X → UnitAddCircle) (a : ℝ) (x : X) : ℝ :=
  AddCircle.equivIco 1 a (f x)

@[simp] theorem coe_circleRepresentative (t : UnitAddCircle) :
    (circleRepresentative t : UnitAddCircle) = t := AddCircle.coe_equivIco

@[simp] theorem coe_circleBranch {X : Type*} (f : X → UnitAddCircle) (a : ℝ) (x : X) :
    (circleBranch f a x : UnitAddCircle) = f x := AddCircle.coe_equivIco

def circleCut {X : Type*} (f : X → UnitAddCircle) (x : X) : ℝ :=
  circleRepresentative (f x) - 1 / 2

theorem circleCut_ne {X : Type*} (f : X → UnitAddCircle) (x : X) :
    f x ≠ (circleCut f x : UnitAddCircle) := by
  intro heq
  let r := circleRepresentative (f x)
  let a := circleCut f x
  have hr : r ∈ Ico a (a + 1) := by dsimp [r, a, circleCut]; constructor <;> linarith
  have ha : a ∈ Ico a (a + 1) := ⟨le_rfl, by linarith⟩
  have h : (r : UnitAddCircle) = (a : UnitAddCircle) :=
    (coe_circleRepresentative (f x)).trans heq
  have h' := (AddCircle.coe_eq_coe_iff_of_mem_Ico hr ha).mp h
  dsimp [r, a, circleCut] at h'
  linarith

theorem smoothCircleAt_of_local_lift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → UnitAddCircle} {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ ∞ u x)
    (heq : (fun y => (u y : UnitAddCircle)) =ᶠ[𝓝 x] f) :
    ∀ a : ℝ, f x ≠ (a : UnitAddCircle) → ContDiffAt ℝ ∞ (circleBranch f a) x := by
  intro a ha
  have ha' : (u x : UnitAddCircle) ≠ (a : UnitAddCircle) := by
    have hx : (u x : UnitAddCircle) = f x := heq.self_of_nhds
    exact fun h => ha (hx.symm.trans h)
  have hmod : ¬ u x ≡ a [PMOD (1 : ℝ)] :=
    AddCommGroup.not_modEq_iff_ne_mod_zmultiples.mpr ha'
  have hconst := (eventuallyEq_toIcoDiv_nhds (by norm_num : (0 : ℝ) < 1) a hmod).comp_tendsto
    hu.continuousAt
  have hloc : circleBranch f a =ᶠ[𝓝 x]
      (fun y => u y - (toIcoDiv (by norm_num : (0 : ℝ) < 1) a (u x) : ℝ)) := by
    filter_upwards [heq, hconst] with y hy hc
    change toIcoDiv (by norm_num : (0 : ℝ) < 1) a (u y) =
      toIcoDiv (by norm_num : (0 : ℝ) < 1) a (u x) at hc
    dsimp only [circleBranch]
    rw [← hy]
    change toIcoMod (by norm_num : (0 : ℝ) < 1) a (u y) = _
    simp only [toIcoMod, hc, zsmul_eq_mul, mul_one]
  exact (hu.sub contDiffAt_const).congr_of_eventuallyEq hloc

theorem smoothCircleOn_iff_local_lifts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → UnitAddCircle} {U : Set E} :
    SmoothCircleOn f U ↔ ∀ x ∈ U, ∃ u : E → ℝ,
      ContDiffAt ℝ ∞ u x ∧ (fun y => (u y : UnitAddCircle)) =ᶠ[𝓝 x] f := by
  constructor
  · intro hf x hx
    exact ⟨circleBranch f (circleCut f x), hf x hx _ (circleCut_ne f x),
      Filter.Eventually.of_forall (coe_circleBranch f _)⟩
  · intro hf x hx
    obtain ⟨u, hu, heq⟩ := hf x hx
    exact smoothCircleAt_of_local_lift hu heq

theorem SmoothCircleOn.continuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → UnitAddCircle} {U : Set E} (hf : SmoothCircleOn f U) : ContinuousOn f U := by
  intro x hx
  obtain ⟨u, hu, heq⟩ := smoothCircleOn_iff_local_lifts.mp hf x hx
  exact (((AddCircle.continuous_mk' (1 : ℝ)).continuousAt.comp hu.continuousAt).congr
    heq).continuousWithinAt

def circleFDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → UnitAddCircle) (x : E) : E →L[ℝ] ℝ :=
  fderiv ℝ (circleBranch f (circleCut f x)) x

/-- The intrinsic differential equals that of every continuous local
lift, including lifts defined only near the point of differentiation. -/
theorem circleFDeriv_eq_lift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → UnitAddCircle} {u : E → ℝ} {x : E}
    (hf : ContinuousAt f x) (hu : ContinuousAt u x)
    (heq : (fun y => (u y : UnitAddCircle)) =ᶠ[𝓝 x] f) :
    circleFDeriv f x = fderiv ℝ u x := by
  have hc : ContinuousAt (circleBranch f (circleCut f x)) x :=
    continuous_subtype_val.continuousAt.comp
      ((AddCircle.continuousAt_equivIco _ _ (circleCut_ne f x)).comp hf)
  exact fderiv_lifts_eq hc hu (by
    filter_upwards [heq] with y hy
    exact (coe_circleBranch f _ y).trans hy.symm)

def circleGradient (f : (ℝ × ℝ) → UnitAddCircle) (x : ℝ × ℝ) : ℝ × ℝ :=
  (circleFDeriv f x (1, 0), circleFDeriv f x (0, 1))

theorem circleGradient_eq_lift
    {f : (ℝ × ℝ) → UnitAddCircle} {u : (ℝ × ℝ) → ℝ} {x : ℝ × ℝ}
    (hf : ContinuousAt f x) (hu : ContinuousAt u x)
    (heq : (fun y => (u y : UnitAddCircle)) =ᶠ[𝓝 x] f) :
    circleGradient f x = planarGradient u x := by
  simp only [circleGradient, circleFDeriv_eq_lift hf hu heq, planarGradient]

/-- A unit-additive real modification descends pointwise to the circle. -/
def circleCutoff {X : Type*} (f : X → UnitAddCircle) (χ : X → ℝ) (P : ℝ → ℝ)
    (x : X) : UnitAddCircle :=
  (cutoffStaircase (fun y => circleRepresentative (f y)) χ P x : UnitAddCircle)

theorem circleCutoff_eq_lift {X : Type*} (f : X → UnitAddCircle) (χ : X → ℝ)
    {P : ℝ → ℝ} (hP : ∀ r, P (r + 1) = P r + 1)
    {u : X → ℝ} {x : X} (hu : (u x : UnitAddCircle) = f x) :
    circleCutoff f χ P x = (cutoffStaircase u χ P x : UnitAddCircle) := by
  obtain ⟨m, hm⟩ := (addCircle_eq_iff_exists_int 1 (circleRepresentative (f x)) (u x)).mp
    ((coe_circleRepresentative (f x)).trans hu.symm)
  have hr : circleRepresentative (f x) = u x + (m : ℝ) := by simpa only [mul_one] using hm
  have hc : cutoffStaircase (fun y => circleRepresentative (f y)) χ P x =
      cutoffStaircase u χ P x + (m : ℝ) := by
    simp only [cutoffStaircase, hr, map_add_int_of_add_one hP]
    ring
  change (cutoffStaircase (fun y => circleRepresentative (f y)) χ P x : UnitAddCircle) = _
  rw [hc]
  apply (addCircle_eq_iff_exists_int 1 _ _).mpr
  exact ⟨m, by simp only [mul_one]⟩

theorem circleCutoff_eq_of_zero {X : Type*} (f : X → UnitAddCircle) (χ : X → ℝ)
    (P : ℝ → ℝ) {x : X} (hx : χ x = 0) : circleCutoff f χ P x = f x := by
  simp only [circleCutoff, cutoffStaircase, hx, zero_mul, add_zero, coe_circleRepresentative]

/-- The actual reciprocal-grid cutoff is smooth on every smooth circle
coordinate's domain, with the original additive transition functions. -/
theorem smoothCircleOn_reciprocal_cutoff
    {f : (ℝ × ℝ) → UnitAddCircle} {U : Set (ℝ × ℝ)}
    (hf : SmoothCircleOn f U) (χ : (ℝ × ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδh : δ < reciprocalGridStep N / 4) (θ : ℝ) :
    SmoothCircleOn (circleCutoff f χ (shiftedStaircase (reciprocalGridStep N) δ θ)) U := by
  have hP (r : ℝ) : shiftedStaircase (reciprocalGridStep N) δ θ (r + 1) =
      shiftedStaircase (reciprocalGridStep N) δ θ r + 1 := by
    simpa only [reciprocalGridStep, Nat.cast_succ] using
      shiftedStaircase_add_one (Nat.succ_pos N) δ θ r
  apply smoothCircleOn_iff_local_lifts.mpr
  intro x hx
  obtain ⟨u, hu, heq⟩ := smoothCircleOn_iff_local_lifts.mp hf x hx
  refine ⟨cutoffStaircase u χ (shiftedStaircase (reciprocalGridStep N) δ θ), ?_, ?_⟩
  · exact hu.add (hχ.contDiffAt.mul
      (((contDiff_shiftedStaircase (reciprocalGridStep_pos N) hδ hδh θ).contDiffAt.comp x hu).sub hu))
  · filter_upwards [heq] with y hy
    exact (circleCutoff_eq_lift f χ hP hy).symm

end CircleDomainRigidity.FiniteTransfer

end

end OAI
