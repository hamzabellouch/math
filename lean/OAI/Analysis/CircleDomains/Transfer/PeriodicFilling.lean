import OAI.Analysis.CircleDomains.Sobolev.CircleDifferential
import OAI.Analysis.CircleDomains.Selection.FinitePatching
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

namespace OAI

/-!
# Integer-translated fillings on the pulled-back circle cover

Section 2, Step 4, of the Koebe manuscript fills one sheet over each
filling disk and uses its integer translates on all other sheets. Here
the cover is the actual pullback of `ℝ → ℝ/ℤ` by the original circle
coordinate. The filled real function is the original height plus the
base correction `g - u` on each disk. Thus it has exactly the original
deck increments and projects to the circle map already constructed by
`CirclePatching`.

The differentials on every sheet are those of the selected real filling.
No additional lifting, period, or winding input is assumed.
-/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

/-- The literal pullback of the universal real cover by a circle map. -/
def CircleLiftCover {X : Type*} (f : X → UnitAddCircle) :=
  {p : X × ℝ // (p.2 : UnitAddCircle) = f p.1}

instance {X : Type*} [TopologicalSpace X] (f : X → UnitAddCircle) :
    TopologicalSpace (CircleLiftCover f) :=
  inferInstanceAs (TopologicalSpace {p : X × ℝ // (p.2 : UnitAddCircle) = f p.1})

def CircleLiftCover.base {X : Type*} {f : X → UnitAddCircle}
    (p : CircleLiftCover f) : X := p.1.1

def CircleLiftCover.height {X : Type*} {f : X → UnitAddCircle}
    (p : CircleLiftCover f) : ℝ := p.1.2

@[simp] theorem CircleLiftCover.height_projects {X : Type*} {f : X → UnitAddCircle}
    (p : CircleLiftCover f) : (p.height : UnitAddCircle) = f p.base := p.2

/-- Integer translations act on this pullback without changing the base. -/
def CircleLiftCover.translate {X : Type*} {f : X → UnitAddCircle}
    (m : ℤ) (p : CircleLiftCover f) : CircleLiftCover f :=
  ⟨(p.base, p.height + (m : ℝ)), ((addCircle_eq_iff_exists_int 1 _ _).mpr
    ⟨m, by simp only [mul_one]⟩).trans p.height_projects⟩

@[simp] theorem CircleLiftCover.base_translate {X : Type*} {f : X → UnitAddCircle}
    (m : ℤ) (p : CircleLiftCover f) : (p.translate m).base = p.base := rfl

@[simp] theorem CircleLiftCover.height_translate {X : Type*} {f : X → UnitAddCircle}
    (m : ℤ) (p : CircleLiftCover f) : (p.translate m).height = p.height + (m : ℝ) := rfl

@[simp] theorem CircleLiftCover.translate_zero {X : Type*} {f : X → UnitAddCircle}
    (p : CircleLiftCover f) : p.translate 0 = p := by
  apply Subtype.ext
  simp only [CircleLiftCover.translate, CircleLiftCover.base, CircleLiftCover.height,
    Int.cast_zero, add_zero]

theorem CircleLiftCover.translate_add {X : Type*} {f : X → UnitAddCircle}
    (m n : ℤ) (p : CircleLiftCover f) : (p.translate m).translate n = p.translate (m + n) := by
  apply Subtype.ext
  simp only [CircleLiftCover.translate, CircleLiftCover.base, CircleLiftCover.height,
    Int.cast_add, add_assoc]

theorem CircleLiftCover.continuous_base {X : Type*} [TopologicalSpace X]
    (f : X → UnitAddCircle) : Continuous (CircleLiftCover.base (f := f)) :=
  continuous_fst.comp continuous_subtype_val

theorem CircleLiftCover.continuous_height {X : Type*} [TopologicalSpace X]
    (f : X → UnitAddCircle) : Continuous (CircleLiftCover.height (f := f)) :=
  continuous_snd.comp continuous_subtype_val

theorem CircleLiftCover.continuous_translate {X : Type*} [TopologicalSpace X]
    (f : X → UnitAddCircle) (m : ℤ) :
    Continuous (fun p : CircleLiftCover f => p.translate m) := by
  apply Continuous.subtype_mk
  exact (CircleLiftCover.continuous_base f).prodMk
    ((CircleLiftCover.continuous_height f).add_const (m : ℝ))

/-- The actual cutoff sends the original pullback cover to the pullback
of the modified circle coordinate, over the identity of the base. -/
def CircleLiftCover.cutoffLift {X : Type*} {f : X → UnitAddCircle}
    (χ : X → ℝ) (P : ℝ → ℝ) (hP : ∀ r, P (r + 1) = P r + 1)
    (p : CircleLiftCover f) : CircleLiftCover (circleCutoff f χ P) :=
  ⟨(p.base, p.height + χ p.base * (P p.height - p.height)),
    (circleCutoff_eq_lift f χ hP (u := fun _ => p.height) p.height_projects).symm⟩

@[simp] theorem CircleLiftCover.base_cutoffLift {X : Type*} {f : X → UnitAddCircle}
    (χ : X → ℝ) (P : ℝ → ℝ) (hP : ∀ r, P (r + 1) = P r + 1)
    (p : CircleLiftCover f) : (p.cutoffLift χ P hP).base = p.base := rfl

theorem CircleLiftCover.cutoffLift_translate {X : Type*} {f : X → UnitAddCircle}
    (χ : X → ℝ) (P : ℝ → ℝ) (hP : ∀ r, P (r + 1) = P r + 1)
    (p : CircleLiftCover f) (m : ℤ) :
    (p.translate m).cutoffLift χ P hP = (p.cutoffLift χ P hP).translate m := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change p.height + (m : ℝ) + χ p.base *
        (P (p.height + (m : ℝ)) - (p.height + (m : ℝ))) =
      p.height + χ p.base * (P p.height - p.height) + (m : ℝ)
    rw [map_add_int_of_add_one hP]
    ring

theorem CircleLiftCover.continuous_cutoffLift {X : Type*} [TopologicalSpace X]
    {f : X → UnitAddCircle} (χ : X → ℝ) (P : ℝ → ℝ)
    (hP : ∀ r, P (r + 1) = P r + 1) (hχ : Continuous χ) (hPc : Continuous P) :
    Continuous (fun p : CircleLiftCover f => p.cutoffLift χ P hP) := by
  apply Continuous.subtype_mk
  exact (CircleLiftCover.continuous_base f).prodMk ((CircleLiftCover.continuous_height f).add
    ((hχ.comp (CircleLiftCover.continuous_base f)).mul
      ((hPc.comp (CircleLiftCover.continuous_height f)).sub (CircleLiftCover.continuous_height f))))

/-- The change on a selected base disk; it is zero off the disks. -/
def fillingCorrection {X I : Type*} (D : I → Set X) (u g : I → X → ℝ) : X → ℝ :=
  patchOpenRegions D (fun i x => g i x - u i x) (fun _ => 0)

/-- Fill on one sheet and translate on every other sheet. -/
def periodicFilledValue {X I : Type*} (f : X → UnitAddCircle)
    (D : I → Set X) (u g : I → X → ℝ) (p : CircleLiftCover f) : ℝ :=
  p.height + fillingCorrection D u g p.base

/-- Every integer deck increment, in particular the positive period one,
is retained by the actual filling formula. -/
theorem periodicFilledValue_translate {X I : Type*} (f : X → UnitAddCircle)
    (D : I → Set X) (u g : I → X → ℝ) (p : CircleLiftCover f) (m : ℤ) :
    periodicFilledValue f D u g (p.translate m) =
      periodicFilledValue f D u g p + (m : ℝ) := by
  simp only [periodicFilledValue, CircleLiftCover.height_translate,
    CircleLiftCover.base_translate]
  ring

/-- Cutoff followed by filling retains the original cover's deck action,
not just the action on a separately chosen cover of the modified map. -/
theorem periodicCutoffFilledValue_translate {X I : Type*} (f : X → UnitAddCircle)
    (χ : X → ℝ) (P : ℝ → ℝ) (hP : ∀ r, P (r + 1) = P r + 1)
    (D : I → Set X) (u g : I → X → ℝ) (p : CircleLiftCover f) (m : ℤ) :
    periodicFilledValue (circleCutoff f χ P) D u g ((p.translate m).cutoffLift χ P hP) =
      periodicFilledValue (circleCutoff f χ P) D u g (p.cutoffLift χ P hP) + (m : ℝ) := by
  rw [CircleLiftCover.cutoffLift_translate, periodicFilledValue_translate]

theorem periodicFilledValue_inside {X I : Type*} (f : X → UnitAddCircle)
    (D : I → Set X) (u g : I → X → ℝ) (hdisj : Pairwise (Disjoint on D))
    {i : I} {p : CircleLiftCover f} (hp : p.base ∈ D i) :
    periodicFilledValue f D u g p = g i p.base + (p.height - u i p.base) := by
  rw [periodicFilledValue, fillingCorrection,
    patchOpenRegions_eq_of_mem D _ _ hdisj hp]
  ring

theorem periodicFilledValue_outside {X I : Type*} (f : X → UnitAddCircle)
    (D : I → Set X) (u g : I → X → ℝ) {p : CircleLiftCover f}
    (hp : ∀ i, p.base ∉ D i) : periodicFilledValue f D u g p = p.height := by
  rw [periodicFilledValue, fillingCorrection,
    patchOpenRegions_eq_of_notMem D _ _ hp, add_zero]

/-- Each sheet differs from the selected filling by an actual integer. -/
theorem periodicFilledValue_inside_integer {X I : Type*} (f : X → UnitAddCircle)
    (D : I → Set X) (u g : I → X → ℝ) (hdisj : Pairwise (Disjoint on D))
    (hu : ∀ i x, x ∈ D i → (u i x : UnitAddCircle) = f x)
    {i : I} {p : CircleLiftCover f} (hp : p.base ∈ D i) :
    ∃ m : ℤ, periodicFilledValue f D u g p = g i p.base + (m : ℝ) := by
  obtain ⟨m, hm⟩ := (addCircle_eq_iff_exists_int 1 p.height (u i p.base)).mp
    (p.height_projects.trans (hu i p.base hp).symm)
  refine ⟨m, ?_⟩
  rw [periodicFilledValue_inside f D u g hdisj hp]
  linarith [hm]

/-- The deck-compatible real filling projects to precisely the already
constructed circle patch. -/
theorem periodicFilledValue_projects {X I : Type*} (f : X → UnitAddCircle)
    (D : I → Set X) (u g : I → X → ℝ) (hdisj : Pairwise (Disjoint on D))
    (hu : ∀ i x, x ∈ D i → (u i x : UnitAddCircle) = f x)
    (p : CircleLiftCover f) :
    (periodicFilledValue f D u g p : UnitAddCircle) =
      patchOpenRegions D (fun i x => (g i x : UnitAddCircle)) f p.base := by
  by_cases hp : ∃ i, p.base ∈ D i
  · obtain ⟨i, hi⟩ := hp
    rw [patchOpenRegions_eq_of_mem D _ _ hdisj hi]
    obtain ⟨m, hm⟩ := periodicFilledValue_inside_integer f D u g hdisj hu hi
    apply (addCircle_eq_iff_exists_int 1 _ _).mpr
    exact ⟨m, by simpa only [mul_one] using hm⟩
  · rw [periodicFilledValue_outside f D u g (not_exists.mp hp),
      patchOpenRegions_eq_of_notMem D _ _ (not_exists.mp hp)]
    exact p.height_projects

/-- The complete cutoff-and-filling formula projects to the actual
circle patch, using the original local branches as input. -/
theorem periodicCutoffFilledValue_projects {X I : Type*} (f : X → UnitAddCircle)
    (χ : X → ℝ) (P : ℝ → ℝ) (hP : ∀ r, P (r + 1) = P r + 1)
    (D : I → Set X) (u g : I → X → ℝ) (hdisj : Pairwise (Disjoint on D))
    (hu : ∀ i x, x ∈ D i → (u i x : UnitAddCircle) = f x) (p : CircleLiftCover f) :
    (periodicFilledValue (circleCutoff f χ P) D
      (fun i => cutoffStaircase (u i) χ P) g (p.cutoffLift χ P hP) : UnitAddCircle) =
      patchOpenRegions D (fun i x => (g i x : UnitAddCircle)) (circleCutoff f χ P) p.base := by
  apply periodicFilledValue_projects _ _ _ _ hdisj
  intro i x hx
  exact (circleCutoff_eq_lift f χ hP (hu i x hx)).symm

/-- Boundary collar agreement makes the base correction globally smooth.
Only the local real branches on the disks are needed. -/
theorem contDiff_fillingCorrection
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
    (D : I → Set E) (hD : ∀ i, IsOpen (D i)) (hdisj : Pairwise (Disjoint on D))
    (u g : I → E → ℝ) (hu : ∀ i, ContDiffOn ℝ ∞ (u i) (D i))
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (D i))
    (hagree : ∀ i x, x ∈ frontier (D i) → g i =ᶠ[𝓝 x] u i) :
    ContDiff ℝ ∞ (fillingCorrection D u g) := by
  rw [← contDiffOn_univ]
  apply contDiffOn_patchOpenRegions D _ _ hD hdisj
  · intro x _ _
    exact contDiffAt_const
  · intro i x hx
    exact ((hg i).sub (hu i)).contDiffAt ((hD i).mem_nhds hx.2)
  · intro i x hx
    exact (hagree i x hx.2).mono (fun y hy => sub_eq_zero.mpr hy)

/-- A branch on any other sheet has the selected real filling's derivative. -/
theorem eventually_filledBranch_eq_add_int
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : I → Set E) (hD : ∀ i, IsOpen (D i)) (hdisj : Pairwise (Disjoint on D))
    (u g : I → E → ℝ) {v : E → ℝ} {i : I} {x : E} (hx : x ∈ D i)
    (hv : ContinuousAt v x) (hu : ContinuousAt (u i) x)
    (hproj : (fun y => (v y : UnitAddCircle)) =ᶠ[𝓝 x] fun y => (u i y : UnitAddCircle)) :
    ∃ m : ℤ, (fun y => v y + fillingCorrection D u g y) =ᶠ[𝓝 x]
      fun y => g i y + (m : ℝ) := by
  obtain ⟨m, hm⟩ := eventually_lifts_differ_by_integer hv hu hproj
  refine ⟨m, ?_⟩
  filter_upwards [hm, (hD i).mem_nhds hx] with y hy hyD
  rw [fillingCorrection, patchOpenRegions_eq_of_mem D _ _ hdisj hyD, hy]
  ring

theorem fderiv_filledBranch_inside
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : I → Set E) (hD : ∀ i, IsOpen (D i)) (hdisj : Pairwise (Disjoint on D))
    (u g : I → E → ℝ) {v : E → ℝ} {i : I} {x : E} (hx : x ∈ D i)
    (hv : ContinuousAt v x) (hu : ContinuousAt (u i) x)
    (hproj : (fun y => (v y : UnitAddCircle)) =ᶠ[𝓝 x] fun y => (u i y : UnitAddCircle)) :
    fderiv ℝ (fun y => v y + fillingCorrection D u g y) x = fderiv ℝ (g i) x := by
  obtain ⟨m, hm⟩ := eventually_filledBranch_eq_add_int D hD hdisj u g hx hv hu hproj
  rw [hm.fderiv_eq (𝕜 := ℝ), fderiv_add_const]

theorem planarGradient_filledBranch_inside
    {I : Type*} (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on D)) (u g : I → (ℝ × ℝ) → ℝ)
    {v : (ℝ × ℝ) → ℝ} {i : I} {x : ℝ × ℝ} (hx : x ∈ D i)
    (hv : ContinuousAt v x) (hu : ContinuousAt (u i) x)
    (hproj : (fun y => (v y : UnitAddCircle)) =ᶠ[𝓝 x] fun y => (u i y : UnitAddCircle)) :
    planarGradient (fun y => v y + fillingCorrection D u g y) x = planarGradient (g i) x := by
  simp only [planarGradient, fderiv_filledBranch_inside D hD hdisj u g hx hv hu hproj]

/-- Rank-one wedge identities are unchanged on arbitrary lifted sheets. -/
theorem wedge_filledBranches_inside
    {I : Type*} (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on D)) (u g u' g' : I → (ℝ × ℝ) → ℝ)
    {v w : (ℝ × ℝ) → ℝ} {i : I} {x : ℝ × ℝ} (hx : x ∈ D i)
    (hv : ContinuousAt v x) (hw : ContinuousAt w x)
    (hu : ContinuousAt (u i) x) (hu' : ContinuousAt (u' i) x)
    (hvproj : (fun y => (v y : UnitAddCircle)) =ᶠ[𝓝 x] fun y => (u i y : UnitAddCircle))
    (hwproj : (fun y => (w y : UnitAddCircle)) =ᶠ[𝓝 x] fun y => (u' i y : UnitAddCircle)) :
    planarWedge (planarGradient (fun y => v y + fillingCorrection D u g y) x)
      (planarGradient (fun y => w y + fillingCorrection D u' g' y) x) =
        planarWedge (planarGradient (g i) x) (planarGradient (g' i) x) := by
  rw [planarGradient_filledBranch_inside D hD hdisj u g hx hv hu hvproj,
    planarGradient_filledBranch_inside D hD hdisj u' g' hx hw hu' hwproj]

/-- Endpoint increments on lifted circuits retain their original deck
number, including zero for a closed lift and one for a positive lift. -/
theorem periodicFilledValue_circuit_increment {X I : Type*} (f : X → UnitAddCircle)
    (D : I → Set X) (u g : I → X → ℝ)
    (γ : unitInterval → CircleLiftCover f) (m : ℤ)
    (hγ : γ 1 = (γ 0).translate m) :
    periodicFilledValue f D u g (γ 1) - periodicFilledValue f D u g (γ 0) = (m : ℝ) := by
  rw [hγ, periodicFilledValue_translate]
  ring

/-- The real difference of two continuous lifts is locally constant. -/
theorem isLocallyConstant_real_lift_difference
    {X : Type*} [TopologicalSpace X] {u v : X → ℝ}
    (hu : Continuous u) (hv : Continuous v)
    (hproj : ∀ x, (u x : UnitAddCircle) = (v x : UnitAddCircle)) :
    IsLocallyConstant (fun x => u x - v x) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  obtain ⟨m, hm⟩ := eventually_lifts_differ_by_integer (x := x) hu.continuousAt hv.continuousAt
    (Filter.Eventually.of_forall hproj)
  have hmx := hm.self_of_nhds
  exact hm.mono (fun y hy => by linarith)

/-- Endpoint differences of continuous real lifts of one path agree. -/
theorem real_lift_path_increment_eq (u v : C(unitInterval, ℝ))
    (hproj : ∀ t, (u t : UnitAddCircle) = (v t : UnitAddCircle)) :
    u 1 - u 0 = v 1 - v 0 := by
  have h := IsLocallyConstant.apply_eq_of_preconnectedSpace
    (isLocallyConstant_real_lift_difference u.continuous v.continuous hproj) (1 : unitInterval) 0
  linarith

/-- Canonical lift, used only to make the path increment independent of
the choice of real branch. -/
def realCirclePathLift (γ : C(unitInterval, UnitAddCircle)) : C(unitInterval, ℝ) :=
  (AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath γ (circleRepresentative (γ 0))
    (coe_circleRepresentative (γ 0)).symm

theorem realCirclePathLift_projects (γ : C(unitInterval, UnitAddCircle)) (t : unitInterval) :
    (realCirclePathLift γ t : UnitAddCircle) = γ t :=
  congrFun ((AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath_lifts γ
    (circleRepresentative (γ 0)) (coe_circleRepresentative (γ 0)).symm) t

/-- Winding measured in turns; on a loop it is an integer. -/
def circlePathIncrement (γ : C(unitInterval, UnitAddCircle)) : ℝ :=
  realCirclePathLift γ 1 - realCirclePathLift γ 0

theorem circlePathIncrement_eq_lift (γ : C(unitInterval, UnitAddCircle))
    (u : C(unitInterval, ℝ)) (hu : ∀ t, (u t : UnitAddCircle) = γ t) :
    circlePathIncrement γ = u 1 - u 0 := by
  apply real_lift_path_increment_eq
  intro t
  exact (realCirclePathLift_projects γ t).trans (hu t).symm

theorem circlePathIncrement_integer (γ : C(unitInterval, UnitAddCircle))
    (hloop : γ 1 = γ 0) : ∃ m : ℤ, circlePathIncrement γ = (m : ℝ) := by
  have heq : (realCirclePathLift γ 1 : UnitAddCircle) =
      (realCirclePathLift γ 0 : UnitAddCircle) :=
    (realCirclePathLift_projects γ 1).trans (hloop.trans (realCirclePathLift_projects γ 0).symm)
  obtain ⟨m, hm⟩ := (addCircle_eq_iff_exists_int 1 _ _).mp heq
  refine ⟨m, ?_⟩
  dsimp [circlePathIncrement]
  linarith

/-- A circuit carrying a single-valued real branch has zero winding. -/
theorem circlePathIncrement_zero_of_closed_lift (γ : C(unitInterval, UnitAddCircle))
    (u : C(unitInterval, ℝ)) (hu : ∀ t, (u t : UnitAddCircle) = γ t)
    (hclosed : u 1 = u 0) : circlePathIncrement γ = 0 := by
  rw [circlePathIncrement_eq_lift γ u hu, hclosed, sub_self]

/-- In particular, every nonsingular terminal circuit admitting the
existing real branch on its collar has period zero. -/
theorem circlePathIncrement_zero_of_branch
    {X : Type*} [TopologicalSpace X] (c : C(unitInterval, X)) (hc : c 1 = c 0)
    {O : Set X} (u : X → ℝ) (hu : ContinuousOn u O) (hO : ∀ t, c t ∈ O)
    (γ : C(unitInterval, UnitAddCircle)) (hproj : ∀ t, (u (c t) : UnitAddCircle) = γ t) :
    circlePathIncrement γ = 0 := by
  let v : C(unitInterval, ℝ) := ⟨u ∘ c, hu.comp_continuous c.continuous hO⟩
  apply circlePathIncrement_zero_of_closed_lift γ v hproj
  exact congrArg u hc

/-- For a continuously differentiable parametrized lift, the path
increment is the integral of its differential. This identifies the deck
calculation with the period appearing in the manuscript. -/
theorem circlePathIncrement_eq_integral_deriv (γ : C(unitInterval, UnitAddCircle))
    (u : ℝ → ℝ) (hu : ContDiffOn ℝ 1 u (uIcc (0 : ℝ) 1))
    (hproj : ∀ t : unitInterval, (u t : UnitAddCircle) = γ t) :
    circlePathIncrement γ = ∫ t in (0 : ℝ)..1, deriv u t := by
  let v : C(unitInterval, ℝ) := ⟨fun t => u t,
    hu.continuousOn.comp_continuous continuous_subtype_val
      (fun t => by simpa only [uIcc_of_le zero_le_one] using t.property)⟩
  rw [intervalIntegral.integral_deriv_of_contDiffOn_uIcc hu]
  exact circlePathIncrement_eq_lift γ v hproj

/-- A lifted circuit ending on sheet `m` projects to a genuine closed
circuit of the patched circle map with winding `m`. The continuous real
lift is constructed from the original height and the base correction. -/
theorem exists_filled_circle_circuit_with_increment
    {X I : Type*} [TopologicalSpace X]
    (f : X → UnitAddCircle) (D : I → Set X) (u g : I → X → ℝ)
    (hdisj : Pairwise (Disjoint on D))
    (hu : ∀ i x, x ∈ D i → (u i x : UnitAddCircle) = f x)
    (hcorr : Continuous (fillingCorrection D u g))
    (c : C(unitInterval, CircleLiftCover f)) (m : ℤ)
    (hc : c 1 = (c 0).translate m) :
    ∃ γ : C(unitInterval, UnitAddCircle),
      (∀ t, γ t = patchOpenRegions D (fun i x => (g i x : UnitAddCircle)) f (c t).base) ∧
      γ 1 = γ 0 ∧ circlePathIncrement γ = (m : ℝ) := by
  let v : C(unitInterval, ℝ) :=
    ⟨fun t => periodicFilledValue f D u g (c t),
      ((CircleLiftCover.continuous_height f).comp c.continuous).add
        (hcorr.comp ((CircleLiftCover.continuous_base f).comp c.continuous))⟩
  let γ : C(unitInterval, UnitAddCircle) :=
    ⟨fun t => (v t : UnitAddCircle), (AddCircle.continuous_mk' (1 : ℝ)).comp v.continuous⟩
  have hv : v 1 - v 0 = (m : ℝ) := periodicFilledValue_circuit_increment f D u g c m hc
  refine ⟨γ, fun t => periodicFilledValue_projects f D u g hdisj hu (c t), ?_, ?_⟩
  · apply (addCircle_eq_iff_exists_int 1 _ _).mpr
    exact ⟨m, by linarith⟩
  · rw [circlePathIncrement_eq_lift γ v (fun _ => rfl)]
    exact hv

/-- The same winding statement for the full staircase cutoff followed by
the filling, starting with a circuit on the original pullback cover. -/
theorem exists_cutoff_filled_circle_circuit_with_increment
    {X I : Type*} [TopologicalSpace X]
    (f : X → UnitAddCircle) (χ : X → ℝ) (P : ℝ → ℝ)
    (hP : ∀ r, P (r + 1) = P r + 1) (hχ : Continuous χ) (hPc : Continuous P)
    (D : I → Set X) (u g : I → X → ℝ) (hdisj : Pairwise (Disjoint on D))
    (hu : ∀ i x, x ∈ D i → (u i x : UnitAddCircle) = f x)
    (hcorr : Continuous (fillingCorrection D (fun i => cutoffStaircase (u i) χ P) g))
    (c : C(unitInterval, CircleLiftCover f)) (m : ℤ)
    (hc : c 1 = (c 0).translate m) :
    ∃ γ : C(unitInterval, UnitAddCircle),
      (∀ t, γ t = patchOpenRegions D (fun i x => (g i x : UnitAddCircle))
        (circleCutoff f χ P) (c t).base) ∧
      γ 1 = γ 0 ∧ circlePathIncrement γ = (m : ℝ) := by
  let c' : C(unitInterval, CircleLiftCover (circleCutoff f χ P)) :=
    ⟨fun t => (c t).cutoffLift χ P hP,
      (CircleLiftCover.continuous_cutoffLift χ P hP hχ hPc).comp c.continuous⟩
  have hend : c' 1 = (c' 0).translate m := by
    change (c 1).cutoffLift χ P hP = ((c 0).cutoffLift χ P hP).translate m
    rw [hc, CircleLiftCover.cutoffLift_translate]
  exact exists_filled_circle_circuit_with_increment (circleCutoff f χ P) D
    (fun i => cutoffStaircase (u i) χ P) g hdisj
    (fun i x hx => (circleCutoff_eq_lift f χ hP (hu i x hx)).symm) hcorr c' m hend

end CircleDomainRigidity.FiniteTransfer

end

end OAI
