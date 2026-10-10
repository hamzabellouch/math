import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.JAction

namespace OAI

section
section
section
section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
open scoped Manifold ContDiff
noncomputable section
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
namespace TamingCompatibility.FormSmoothness

variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {k : ℕ} {n : WithTop ℕ∞}

local instance : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :=
  FiniteDimensional.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ))
    ContinuousMultilinearMap.toMultilinearMap_injective

local instance : FiniteDimensional ℝ (E [⋀^Fin k]→L[ℝ] ℝ) :=
  FiniteDimensional.of_injective (ContinuousAlternatingMap.toContinuousMultilinearMapLinear)
    ContinuousAlternatingMap.toContinuousMultilinearMap_injective

omit [FiniteDimensional ℝ E] in

lemma contDiffOn_of_linear_embedding {f : D → E} {s : Set D}
    (L : E →L[ℝ] F) (hL : Function.Injective L)
    (h : ContDiffOn ℝ n (fun x => L (f x)) s) : ContDiffOn ℝ n f s := by
  let R := L.toLinearMap.leftInverse.toContinuousLinearMap
  have hr : ∀ x, R (L x) = x :=
    LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hL)
  simpa only [Function.comp_def, hr] using R.contDiff.comp_contDiffOn h

omit [FiniteDimensional ℝ F] in

lemma ContDiffOn.compAlternating {α : D → F [⋀^Fin k]→L[ℝ] ℝ}
    {A : D → E →L[ℝ] F} {s : Set D}
    (hα : ContDiffOn ℝ n α s) (hA : ContDiffOn ℝ n A s) :
    ContDiffOn ℝ n (fun x => (α x).compContinuousLinearMap (A x)) s := by
  apply contDiffOn_of_linear_embedding
    (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ)
    ContinuousAlternatingMap.toContinuousMultilinearMap_injective
  let P : ContinuousMultilinearMap ℝ (fun _ : Fin k => E →L[ℝ] F)
      ((ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
      (fun _ : Fin k => E) (fun _ => F) ℝ
  have hPc : ContDiff ℝ n P :=
    ContinuousMultilinearMap.contDiff (𝕜 := ℝ) (ι := Fin k)
      (E := fun _ => E →L[ℝ] F) (F :=
      (ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) P
  have hP := hPc.comp_contDiffOn (contDiffOn_pi.mpr (fun _ => hA))
  have hC : ContDiff ℝ n (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ :
      (F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin k => F) ℝ) :=
    ContinuousLinearMap.contDiff _
  exact hP.clm_apply (hC.comp_contDiffOn hα)

omit [FiniteDimensional ℝ F] in

lemma contDiff_compAlternating :
    ContDiff ℝ n (fun p : (F [⋀^Fin k]→L[ℝ] ℝ) × (E →L[ℝ] F) =>
      p.1.compContinuousLinearMap p.2) := by
  rw [← contDiffOn_univ]
  exact ContDiffOn.compAlternating contDiffOn_fst contDiffOn_snd

omit [FiniteDimensional ℝ F] in
lemma ContDiffAt.compAlternating {α : D → F [⋀^Fin k]→L[ℝ] ℝ}
    {A : D → E →L[ℝ] F} {x : D}
    (hα : ContDiffAt ℝ n α x) (hA : ContDiffAt ℝ n A x) :
    ContDiffAt ℝ n (fun y => (α y).compContinuousLinearMap (A y)) x :=
  contDiff_compAlternating.contDiffAt.comp x (hα.prodMk hA)

end TamingCompatibility.FormSmoothness

namespace TamingCompatibility.ManifoldForms

open TamingCompatibility.FormSmoothness

abbrev Space := EuclideanSpace ℝ (Fin 4)
abbrev Model := 𝓘(ℝ, Space)

abbrev Form (X : Type*) [TopologicalSpace X] [ChartedSpace Space X] (k : ℕ) :=
  (x : X) → (TangentSpace Model x) [⋀^Fin k]→L[ℝ] ℝ

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] {k : ℕ}

def pullback (α : Form X k) (f : Space → X) : Space → Space [⋀^Fin k]→L[ℝ] ℝ :=
  fun y => (α (f y)).compContinuousLinearMap (mfderiv Model Model f y)

def Smooth (α : Form X k) : Prop :=
  ∀ (f : Space → X) (U : Set Space), IsOpen U →
    ContMDiffOn Model Model ∞ f U → ContDiffOn ℝ ∞ (pullback α f) U

def Closed (α : Form X k) : Prop :=
  ∀ (f : Space → X) (U : Set Space), IsOpen U →
    ContMDiffOn Model Model ∞ f U → ∀ y ∈ U,
      extDerivWithin (pullback α f) U y = 0

def exteriorDerivative (α : Form X k) : Form X (k + 1) :=
  fun x => extDeriv (pullback α (extChartAt Model x).symm) (extChartAt Model x x)

lemma extDerivWithin_eq_of_mem {α : Space → Space [⋀^Fin k]→L[ℝ] ℝ}
    {U : Set Space} {y : Space} (hU : IsOpen U) (hy : y ∈ U) :
    extDerivWithin α U y = extDeriv α y := by
  unfold extDerivWithin extDeriv
  rw [fderivWithin_of_mem_nhds (hU.mem_nhds hy)]

omit [IsManifold Model ∞ X] in
lemma pullback_comp (α : Form X k) {f : Space → X} {g : Space → Space} {y : Space}
    (hf : MDifferentiableAt Model Model f (g y))
    (hg : DifferentiableAt ℝ g y) :
    pullback α (f ∘ g) y = (pullback α f (g y)).compContinuousLinearMap (fderiv ℝ g y) := by
  unfold pullback
  rw [mfderiv_comp y hf hg.mdifferentiableAt, mfderiv_eq_fderiv]
  ext v
  rfl

omit [IsManifold Model ∞ X] in
lemma pullback_congr_eventually (α : Form X k) {f g : Space → X} {y : Space}
    (hfg : f =ᶠ[𝓝 y] g) : pullback α f =ᶠ[𝓝 y] pullback α g := by
  filter_upwards [hfg.eventuallyEq_nhds] with z hz
  have hv := hz.self_of_nhds
  unfold pullback
  rw [hz.mfderiv_eq, hv]
  ext vectors
  rfl

lemma smooth_chart (α : Form X k) (hα : Smooth α) (x : X) :
    ContDiffOn ℝ ∞ (pullback α (extChartAt Model x).symm) (extChartAt Model x).target :=
  hα _ _ (isOpen_extChartAt_target x) (contMDiffOn_extChartAt_symm x)

theorem smooth_of_charts {α : Form X k}
    (hα : ∀ x, ContDiffOn ℝ ∞ (pullback α (extChartAt Model x).symm)
      (extChartAt Model x).target) : Smooth α := by
  intro f U hU hf y hy
  let p := f y
  let e := extChartAt Model p
  let g : Space → Space := e ∘ f
  let β := pullback α e.symm
  have hfy : ContMDiffAt Model Model ∞ f y := (hf y hy).contMDiffAt (hU.mem_nhds hy)
  have hgy : ContMDiffAt Model Model ∞ g y :=
    (contMDiffAt_extChartAt (I := Model) (x := p)).comp y hfy
  have hegy : g y ∈ e.target := e.map_source (mem_extChartAt_source p)
  have hβ : ContDiffAt ℝ ∞ β (g y) :=
    ((hα p) (g y) hegy).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hegy)
  have hgf : e.symm ∘ g =ᶠ[𝓝 y] f := by
    have hs : ∀ᶠ z in 𝓝 y, f z ∈ e.source :=
      hfy.continuousAt.eventually (extChartAt_source_mem_nhds p)
    filter_upwards [hs] with z hz
    exact e.left_inv hz
  have hpb : (fun z => (β (g z)).compContinuousLinearMap (fderiv ℝ g z)) =ᶠ[𝓝 y]
      pullback α f := by
    have hs : ∀ᶠ z in 𝓝 y, f z ∈ e.source :=
      hfy.continuousAt.eventually (extChartAt_source_mem_nhds p)
    filter_upwards [hs, hU.mem_nhds hy, pullback_congr_eventually α hgf] with z hz hzU hpz
    have hgz : ContMDiffAt Model Model ∞ g z :=
      (contMDiffAt_extChartAt' (I := Model) (by simpa only [e, extChartAt_source] using hz)).comp z
        ((hf z hzU).contMDiffAt (hU.mem_nhds hzU))
    have hez : ContMDiffAt Model Model ∞ e.symm (g z) :=
      ((contMDiffOn_extChartAt_symm p) (g z) (e.map_source hz)).contMDiffAt
        ((isOpen_extChartAt_target p).mem_nhds (e.map_source hz))
    rw [← pullback_comp α (hez.mdifferentiableAt (by simp))
      ((contMDiffAt_iff_contDiffAt.mp hgz).differentiableAt (by simp))]
    exact hpz
  have hg : ContDiffAt ℝ ∞ g y := contMDiffAt_iff_contDiffAt.mp hgy
  have hdg : ContDiffAt ℝ ∞ (fderiv ℝ g) y := hg.fderiv_right (by simp)
  exact (((hβ.comp y hg).compAlternating hdg).congr_of_eventuallyEq hpb.symm).contDiffWithinAt

theorem pullback_exteriorDerivative (α : Form X k) (hα : Smooth α)
    {f : Space → X} {U : Set Space} (hU : IsOpen U)
    (hf : ContMDiffOn Model Model ∞ f U) {y : Space} (hy : y ∈ U) :
    pullback (exteriorDerivative α) f y = extDerivWithin (pullback α f) U y := by
  let p := f y
  let e := extChartAt Model p
  let g : Space → Space := e ∘ f
  let β := pullback α e.symm
  have hfy : ContMDiffAt Model Model ∞ f y := (hf y hy).contMDiffAt (hU.mem_nhds hy)
  have hgy : ContMDiffAt Model Model ∞ g y :=
    (contMDiffAt_extChartAt (I := Model) (x := p)).comp y hfy
  have hegy : g y ∈ e.target := e.map_source (mem_extChartAt_source p)
  have hβ : ContDiffAt ℝ ∞ β (g y) :=
    ((smooth_chart α hα p) (g y) hegy).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hegy)
  have hgf : e.symm ∘ g =ᶠ[𝓝 y] f := by
    have hs : ∀ᶠ z in 𝓝 y, f z ∈ e.source :=
      hfy.continuousAt.eventually (extChartAt_source_mem_nhds p)
    filter_upwards [hs] with z hz
    exact e.left_inv hz
  have hpb : (fun z => (β (g z)).compContinuousLinearMap (fderiv ℝ g z)) =ᶠ[𝓝 y]
      pullback α f := by
    have hs : ∀ᶠ z in 𝓝 y, f z ∈ e.source :=
      hfy.continuousAt.eventually (extChartAt_source_mem_nhds p)
    filter_upwards [hs, hU.mem_nhds hy, pullback_congr_eventually α hgf] with z hz hzU hpz
    have hgz : ContMDiffAt Model Model ∞ g z :=
      (contMDiffAt_extChartAt' (I := Model) (by simpa only [e, extChartAt_source] using hz)).comp z
        ((hf z hzU).contMDiffAt (hU.mem_nhds hzU))
    have hez : ContMDiffAt Model Model ∞ e.symm (g z) :=
      ((contMDiffOn_extChartAt_symm p) (g z) (e.map_source hz)).contMDiffAt
        ((isOpen_extChartAt_target p).mem_nhds (e.map_source hz))
    rw [← pullback_comp α (hez.mdifferentiableAt (by simp))
      ((contMDiffAt_iff_contDiffAt.mp hgz).differentiableAt (by simp))]
    exact hpz
  have hdg : fderiv ℝ g y = mfderiv Model Model f y := by
    rw [← mfderiv_eq_fderiv]
    have he : MDifferentiableAt Model Model (extChartAt Model p) p :=
      (contMDiffAt_extChartAt (n := ∞) (I := Model) (x := p)).mdifferentiableAt (by simp)
    change mfderiv Model Model ((extChartAt Model p) ∘ f) y = _
    rw [mfderiv_comp y he (hfy.mdifferentiableAt (by simp))]
    ext v
    change mfderiv Model Model (extChartAt Model p) p (mfderiv Model Model f y v) = _
    rw [mfderiv_extChartAt_self]
    rfl
  rw [extDerivWithin_eq_of_mem hU hy, ← hpb.extDeriv_eq,
    extDeriv_pullback (hβ.differentiableAt (by simp))
      (contMDiffAt_iff_contDiffAt.mp hgy) (by
        simp only [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.mpr le_top), hdg]
  rfl

theorem Smooth.exteriorDerivative {α : Form X k} (hα : Smooth α) :
    Smooth (exteriorDerivative α) := by
  intro f U hU hf
  have hd : ContDiffOn ℝ ∞ (extDerivWithin (pullback α f) U) U := by
    exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ Space ℝ).contDiff.comp_contDiffOn
      ((contDiffOn_infty_iff_fderivWithin hU.uniqueDiffOn).mp (hα f U hU hf)).2
  apply hd.congr
  intro y hy
  exact pullback_exteriorDerivative α hα hU hf hy

theorem closed_iff_exteriorDerivative_eq_zero {α : Form X k} (hα : Smooth α) :
    Closed α ↔ exteriorDerivative α = 0 := by
  constructor
  · intro h
    funext x
    have hz := h (extChartAt Model x).symm (extChartAt Model x).target
      (isOpen_extChartAt_target x) (contMDiffOn_extChartAt_symm x)
      (extChartAt Model x x) ((extChartAt Model x).map_source (mem_extChartAt_source x))
    rwa [extDerivWithin_eq_of_mem (isOpen_extChartAt_target x)
      ((extChartAt Model x).map_source (mem_extChartAt_source x))] at hz
  · intro h f U hU hf y hy
    rw [← pullback_exteriorDerivative α hα hU hf hy, h]
    ext v
    rfl

theorem exteriorDerivative_square {α : Form X k} (hα : Smooth α) :
    exteriorDerivative (exteriorDerivative α) = 0 := by
  funext x
  let e := extChartAt Model x
  let z := e x
  have hz : z ∈ e.target := e.map_source (mem_extChartAt_source x)
  have heq : pullback (exteriorDerivative α) e.symm =ᶠ[𝓝 z]
      extDeriv (pullback α e.symm) := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with y hy
    rw [pullback_exteriorDerivative α hα (isOpen_extChartAt_target x)
      (contMDiffOn_extChartAt_symm x) hy,
      extDerivWithin_eq_of_mem (isOpen_extChartAt_target x) hy]
  change extDeriv (pullback (exteriorDerivative α) e.symm) z = 0
  rw [heq.extDeriv_eq]
  apply extDeriv_extDeriv_apply
    (((smooth_chart α hα x) z hz).contDiffAt ((isOpen_extChartAt_target x).mem_nhds hz))
  simp only [minSmoothness_of_isRCLikeNormedField]
  exact WithTop.coe_le_coe.mpr le_top

lemma Smooth.closed_exteriorDerivative {α : Form X k} (hα : Smooth α) :
    Closed (ManifoldForms.exteriorDerivative α) :=
  (closed_iff_exteriorDerivative_eq_zero hα.exteriorDerivative).mpr (exteriorDerivative_square hα)

omit [IsManifold Model ∞ X] in
lemma pullback_add (α β : Form X k) (f : Space → X) :
    pullback (α + β) f = pullback α f + pullback β f := rfl

omit [IsManifold Model ∞ X] in
lemma pullback_smul (c : ℝ) (α : Form X k) (f : Space → X) :
    pullback (c • α) f = c • pullback α f := rfl

omit [IsManifold Model ∞ X] in
lemma Smooth.zero : Smooth (0 : Form X k) := by
  intro f U hU hf
  change ContDiffOn ℝ ∞ (fun _ : Space => (0 : Space [⋀^Fin k]→L[ℝ] ℝ)) U
  exact contDiffOn_const

omit [IsManifold Model ∞ X] in
lemma Smooth.add {α β : Form X k} (hα : Smooth α) (hβ : Smooth β) :
    Smooth (α + β) := by
  intro f U hU hf
  rw [pullback_add]
  exact (hα f U hU hf).add (hβ f U hU hf)

omit [IsManifold Model ∞ X] in
lemma Smooth.smul (c : ℝ) {α : Form X k} (hα : Smooth α) : Smooth (c • α) := by
  intro f U hU hf
  rw [pullback_smul]
  exact (hα f U hU hf).const_smul c

lemma exteriorDerivative_add {α β : Form X k} (hα : Smooth α) (hβ : Smooth β) :
    exteriorDerivative (α + β) = exteriorDerivative α + exteriorDerivative β := by
  funext x
  unfold exteriorDerivative
  rw [pullback_add]
  apply extDeriv_add
  · exact (((smooth_chart α hα x) _
      ((extChartAt Model x).map_source (mem_extChartAt_source x))).contDiffAt
      (extChartAt_target_mem_nhds x)).differentiableAt (by simp)
  · exact (((smooth_chart β hβ x) _
      ((extChartAt Model x).map_source (mem_extChartAt_source x))).contDiffAt
      (extChartAt_target_mem_nhds x)).differentiableAt (by simp)

omit [IsManifold Model ∞ X] in
lemma exteriorDerivative_smul (c : ℝ) (α : Form X k) :
    exteriorDerivative (c • α) = c • exteriorDerivative α := by
  funext x
  unfold exteriorDerivative
  rw [pullback_smul, extDeriv_smul]
  rfl

def smoothForms (X : Type*) [TopologicalSpace X] [ChartedSpace Space X] (k : ℕ) :
    Submodule ℝ (Form X k) where
  carrier := {α | Smooth α}
  zero_mem' := Smooth.zero
  add_mem' := Smooth.add
  smul_mem' := Smooth.smul

def d : smoothForms X k →ₗ[ℝ] smoothForms X (k + 1) where
  toFun α := ⟨exteriorDerivative α.1, α.2.exteriorDerivative⟩
  map_add' α β := Subtype.ext (exteriorDerivative_add α.2 β.2)
  map_smul' c α := Subtype.ext (exteriorDerivative_smul c α.1)

lemma d_square (α : smoothForms X k) : d (d α) = 0 :=
  Subtype.ext (exteriorDerivative_square α.2)

def closedForms (X : Type*) [TopologicalSpace X] [ChartedSpace Space X]
    [IsManifold Model ∞ X] (k : ℕ) : Submodule ℝ (smoothForms X k) :=
  LinearMap.ker d

lemma mem_closedForms_iff (α : smoothForms X k) : α ∈ closedForms X k ↔ Closed α.1 := by
  show d α = 0 ↔ _
  rw [closed_iff_exteriorDerivative_eq_zero α.2]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

lemma d_mem_closedForms (α : smoothForms X k) : d α ∈ closedForms X (k + 1) := d_square α

end TamingCompatibility.ManifoldForms

noncomputable section
open scoped Manifold ContDiff Topology
open Bundle Filter Set

end
end
end
end
end
end
end
end
end
end

end OAI
