import OAI.Analysis.CircleDomains.Topology.JordanExteriors
import OAI.Analysis.CircleDomains.Modulus.GridIncidence
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible

namespace OAI

/-!
# Real lifts of circle coordinates near filling disks

The quotient `ℝ → ℝ/ℤ` is a covering map in Mathlib. Its lifting theorem
therefore gives actual continuous real branches on simply connected open
sets. Smoothness is expressed in the ordinary real quotient charts
`AddCircle.equivIco`; a continuous lift is locally one of these charts plus
an integer, so the lift is smooth. No external lifting axiom is used.
-/

open Set Filter Function Metric
open scoped Topology ContDiff

namespace CircleDomainRigidity.FiniteTransfer

/-- Smoothness in every real quotient chart whose cut point is absent.
This uses the actual `ℝ/ℤ` charts, without requiring a separate manifold
instance for `AddCircle`. -/
def SmoothCircleOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → UnitAddCircle) (U : Set E) : Prop :=
  ∀ x ∈ U, ∀ a : ℝ, f x ≠ (a : UnitAddCircle) →
    ContDiffAt ℝ ∞ (fun y => (AddCircle.equivIco (1 : ℝ) a (f y) : ℝ)) x

/-- Ordinary smooth real coordinates project to smooth circle
coordinates in the explicit quotient-chart definition. -/
theorem smoothCircleOn_coe
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u U) :
    SmoothCircleOn (fun x => (u x : UnitAddCircle)) U := by
  intro x hx a ha
  have hux := hu.contDiffAt (hU.mem_nhds hx)
  have hmod : ¬ u x ≡ a [PMOD (1 : ℝ)] := AddCommGroup.not_modEq_iff_ne_mod_zmultiples.mpr ha
  have hconst := (eventuallyEq_toIcoDiv_nhds (by norm_num : (0 : ℝ) < 1) a hmod).comp_tendsto
    hux.continuousAt
  have heq : (fun y => (AddCircle.equivIco (1 : ℝ) a (u y : UnitAddCircle) : ℝ))
      =ᶠ[𝓝 x] (fun y => u y - (toIcoDiv (by norm_num : (0 : ℝ) < 1) a (u x) : ℝ)) := by
    filter_upwards [hconst] with y hy
    change toIcoDiv (by norm_num : (0 : ℝ) < 1) a (u y) =
      toIcoDiv (by norm_num : (0 : ℝ) < 1) a (u x) at hy
    change toIcoMod (by norm_num : (0 : ℝ) < 1) a (u y) = _
    simp only [toIcoMod, hy, zsmul_eq_mul, mul_one]
  exact (hux.sub contDiffAt_const).congr_of_eventuallyEq heq

theorem exists_continuous_circle_lift
    {X : Type*} [TopologicalSpace X] {U : Set X}
    [SimplyConnectedSpace U] [LocallyPathConnectedSpace U]
    (f : X → UnitAddCircle) (hf : ContinuousOn f U)
    {x₀ : X} (hx₀ : x₀ ∈ U) (r₀ : ℝ) (hr₀ : (r₀ : UnitAddCircle) = f x₀) :
    ∃ u : X → ℝ, ContinuousOn u U ∧ u x₀ = r₀ ∧
      ∀ x ∈ U, (u x : UnitAddCircle) = f x := by
  classical
  let f' : C(U, UnitAddCircle) := ⟨fun x => f x, hf.domRestrict⟩
  obtain ⟨g, ⟨hg₀, hg⟩, _⟩ :=
    (AddCircle.isCoveringMap_coe (1 : ℝ)).existsUnique_continuousMap_lifts
      f' ⟨x₀, hx₀⟩ r₀ hr₀
  let u : X → ℝ := fun x => if hx : x ∈ U then g ⟨x, hx⟩ else 0
  refine ⟨u, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert g.continuous using 1
    funext x
    change u x = g x
    simp only [u, dite_eq_left x.property]
  · simpa only [u, dite_eq_left hx₀] using hg₀
  · intro x hx
    have h := congrFun hg (⟨x, hx⟩ : U)
    change (g ⟨x, hx⟩ : UnitAddCircle) = f x at h
    simpa only [u, dite_eq_left hx] using h

/-- Smooth circle charts automatically make any continuous real lift
smooth, by local injectivity of the quotient on an interval of length one. -/
theorem contDiffOn_circle_lift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {f : E → UnitAddCircle} {u : E → ℝ}
    (hu : ContinuousOn u U) (hlift : ∀ x ∈ U, (u x : UnitAddCircle) = f x)
    (hf : SmoothCircleOn f U) : ContDiffOn ℝ ∞ u U := by
  intro x hx
  let a := u x - 1 / 2
  have hux : u x ∈ Ioo a (a + 1) := by dsimp [a]; constructor <;> linarith
  have hcut : f x ≠ (a : UnitAddCircle) := by
    rw [← hlift x hx]
    intro heq
    have ha : a ∈ Ico a (a + 1) := ⟨le_rfl, by linarith⟩
    have heq' := (AddCircle.coe_eq_coe_iff_of_mem_Ico (Ioo_subset_Ico_self hux) ha).mp heq
    dsimp [a] at heq'
    linarith
  have hsmooth := hf x hx a hcut
  have hloc : u =ᶠ[𝓝 x] (fun y => (AddCircle.equivIco (1 : ℝ) a (f y) : ℝ)) := by
    have hnear : ∀ᶠ y in 𝓝 x, u y ∈ Ioo a (a + 1) :=
      (hu.continuousAt (hU.mem_nhds hx)).eventually (isOpen_Ioo.mem_nhds hux)
    filter_upwards [hnear, hU.mem_nhds hx] with y hy hyU
    rw [← hlift y hyU, AddCircle.equivIco_coe_eq (Ioo_subset_Ico_self hy)]
  exact (hsmooth.congr_of_eventuallyEq hloc).contDiffWithinAt

theorem exists_smooth_circle_lift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} [SimplyConnectedSpace U] [LocallyPathConnectedSpace U]
    (hU : IsOpen U) (f : E → UnitAddCircle) (hf : ContinuousOn f U)
    (hfs : SmoothCircleOn f U) {x₀ : E} (hx₀ : x₀ ∈ U)
    (r₀ : ℝ) (hr₀ : (r₀ : UnitAddCircle) = f x₀) :
    ∃ u : E → ℝ, ContDiffOn ℝ ∞ u U ∧ u x₀ = r₀ ∧
      ∀ x ∈ U, (u x : UnitAddCircle) = f x := by
  obtain ⟨u, hu, hu₀, hlift⟩ := exists_continuous_circle_lift f hf hx₀ r₀ hr₀
  exact ⟨u, contDiffOn_circle_lift hU hu hlift hfs, hu₀, hlift⟩

theorem isSimplyConnected_homeomorph_ball (H : ℂ ≃ₜ ℂ) {r : ℝ} (hr : 0 < r) :
    IsSimplyConnected (H '' ball (0 : ℂ) r) := by
  let : ContractibleSpace (ball (0 : ℂ) r) :=
    (convex_ball (0 : ℂ) r).contractibleSpace (nonempty_ball.mpr hr)
  exact H.isSimplyConnected_image.mpr
    (show SimplyConnectedSpace (ball (0 : ℂ) r) from inferInstance)

/-- The entire closed filling disk has one slightly larger simply
connected neighborhood avoiding the singular set. The real branch is
smooth on this whole neighborhood, hence on all sufficiently small collars. -/
theorem exists_smooth_circle_lift_near_jordan_disk
    (H : ℂ ≃ₜ ℂ) {S : Set ℂ} (hS : IsClosed S)
    (havoid : Disjoint (closure (jordanInterior H)) S)
    (f : ℂ → UnitAddCircle) (hf : ContinuousOn f Sᶜ) (hfs : SmoothCircleOn f Sᶜ) :
    ∃ (V : Set ℂ) (u : ℂ → ℝ), IsOpen V ∧ closure (jordanInterior H) ⊆ V ∧
      V ⊆ Sᶜ ∧ ContDiffOn ℝ ∞ u V ∧ ∀ x ∈ V, (u x : UnitAddCircle) = f x := by
  classical
  have hsub : closure (jordanInterior H) ⊆ Sᶜ :=
    fun x hx => Set.disjoint_left.mp havoid hx
  have hp : Pairwise (Disjoint on fun _ : Unit => closure (jordanInterior H)) := by
    intro i j hij
    exact (hij (Subsingleton.elim _ _)).elim
  obtain ⟨r, hr, hrsub, _⟩ := exists_disjoint_jordan_enlargements (fun _ : Unit => H)
    hp (fun _ => Sᶜ) (fun _ => hS.isOpen_compl) (fun _ => hsub)
  let V := H '' ball (0 : ℂ) (r ())
  have hVo : IsOpen V := H.isOpenMap _ isOpen_ball
  have hDV : closure (jordanInterior H) ⊆ V := by
    rw [closure_jordanInterior]
    exact image_mono (closedBall_subset_ball (hr ()))
  have hVS : V ⊆ Sᶜ :=
    (image_mono ball_subset_closedBall).trans (hrsub ())
  let : SimplyConnectedSpace V := isSimplyConnected_homeomorph_ball H (by linarith [hr ()])
  let : LocallyPathConnectedSpace V := hVo.locallyPathConnectedSpace
  have hx : H 0 ∈ V := ⟨0, mem_ball_self (by linarith [hr ()]), rfl⟩
  obtain ⟨r₀, _, hr₀⟩ := AddCircle.eq_coe_Ico (f (H 0))
  obtain ⟨u, hu, _, hlift⟩ := exists_smooth_circle_lift hVo f (hf.mono hVS)
    (fun x hx a ha => hfs x (hVS hx) a ha) hx r₀ hr₀
  exact ⟨V, u, hVo, hDV, hVS, hu, hlift⟩

/-- The finite coordinate family has a common open branch neighborhood
around each closed filling disk. -/
theorem exists_simultaneous_smooth_circle_lifts
    {I L : Type*} [Fintype L]
    (H : I → ℂ ≃ₜ ℂ) (S : L → Set ℂ) (hS : ∀ l, IsClosed (S l))
    (havoid : ∀ i l, Disjoint (closure (jordanInterior (H i))) (S l))
    (f : L → ℂ → UnitAddCircle)
    (hf : ∀ l, ContinuousOn (f l) (S l)ᶜ) (hfs : ∀ l, SmoothCircleOn (f l) (S l)ᶜ) :
    ∃ (O : I → Set ℂ) (u : I → L → ℂ → ℝ),
      (∀ i, IsOpen (O i) ∧ closure (jordanInterior (H i)) ⊆ O i) ∧
      ∀ i l, O i ⊆ (S l)ᶜ ∧ ContDiffOn ℝ ∞ (u i l) (O i) ∧
        ∀ x ∈ O i, (u i l x : UnitAddCircle) = f l x := by
  classical
  choose V u hVo hDV hVS hu hlift using fun i l =>
    exists_smooth_circle_lift_near_jordan_disk (H i) (hS l) (havoid i l) (f l) (hf l) (hfs l)
  let O : I → Set ℂ := fun i => ⋂ l, V i l
  refine ⟨O, u, ?_, ?_⟩
  · intro i
    exact ⟨isOpen_iInter_of_finite (hVo i), subset_iInter (hDV i)⟩
  · intro i l
    have hOV : O i ⊆ V i l := iInter_subset (V i) l
    exact ⟨hOV.trans (hVS i l), (hu i l).mono hOV, fun x hx => hlift i l x (hOV hx)⟩

/-- Closed quotient singularities pull back to exactly the obstacle
used in the physical lifting theorem. -/
theorem exists_smooth_circle_lift_of_projected_avoidance
    {X : Type*} [TopologicalSpace X] (q : ℂ → X) (hq : Continuous q)
    (H : ℂ ≃ₜ ℂ) {S : Set X} (hS : IsClosed S)
    (havoid : Disjoint (q '' closure (jordanInterior H)) S)
    (f : ℂ → UnitAddCircle) (hf : ContinuousOn f (q ⁻¹' S)ᶜ)
    (hfs : SmoothCircleOn f (q ⁻¹' S)ᶜ) :
    ∃ (V : Set ℂ) (u : ℂ → ℝ), IsOpen V ∧ closure (jordanInterior H) ⊆ V ∧
      V ⊆ q ⁻¹' Sᶜ ∧ ContDiffOn ℝ ∞ u V ∧ ∀ x ∈ V, (u x : UnitAddCircle) = f x := by
  apply exists_smooth_circle_lift_near_jordan_disk H (hS.preimage hq) _ f hf hfs
  exact Set.disjoint_left.mpr fun x hx hxS =>
    Set.disjoint_left.mp havoid ⟨x, hx, rfl⟩ hxS

end CircleDomainRigidity.FiniteTransfer

end OAI
