import Mathlib

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.Conjugacy
open Filter Set
open scoped Topology Manifold ContDiff
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem nondegenerate_local_conjugate
    (e : E → F) (ei : F → E) (g : E → E) (f : F → F) (x : E)
    (he : DifferentiableAt ℝ e x) (hei : DifferentiableAt ℝ ei (e x))
    (hf : DifferentiableAt ℝ f (e x))
    (hleft : ∀ᶠ z in 𝓝 x, ei (e z) = z)
    (hright : ∀ᶠ z in 𝓝 (e x), e (ei z) = z)
    (hfix : f (e x) = e x)
    (hconj : ∀ᶠ z in 𝓝 x, g z = ei (f (e z)))
    (hnd : Function.Bijective (fderiv ℝ f (e x) - ContinuousLinearMap.id ℝ F)) :
    Function.Bijective (fderiv ℝ g x - ContinuousLinearMap.id ℝ E) := by
  let A := fderiv ℝ e x
  let B := fderiv ℝ ei (e x)
  let D := fderiv ℝ f (e x)
  have hba : B.comp A = ContinuousLinearMap.id ℝ E :=
    ((hei.hasFDerivAt.comp x he.hasFDerivAt).congr_of_eventuallyEq (Filter.EventuallyEq.symm hleft)).unique
      (hasFDerivAt_id x)
  have hinv : ei (e x) = x := hleft.self_of_nhds
  have hde : HasFDerivAt e A (ei (e x)) := by rw [hinv]; exact he.hasFDerivAt
  have hab : A.comp B = ContinuousLinearMap.id ℝ F :=
    ((hde.comp (e x) hei.hasFDerivAt).congr_of_eventuallyEq (Filter.EventuallyEq.symm hright)).unique
      (hasFDerivAt_id (e x))
  have hb : Function.Bijective B := by
    constructor
    · intro u v h
      have hh := congrArg A h
      simpa only [← ContinuousLinearMap.comp_apply, hab, ContinuousLinearMap.id_apply] using hh
    · intro u
      exact ⟨A u, congrArg (fun T : E →L[ℝ] E => T u) hba⟩
  have ha : Function.Bijective A := by
    constructor
    · intro u v h
      have hh := congrArg B h
      simpa only [← ContinuousLinearMap.comp_apply, hba, ContinuousLinearMap.id_apply] using hh
    · intro u
      exact ⟨B u, congrArg (fun T : F →L[ℝ] F => T u) hab⟩
  have hbi : HasFDerivAt ei B (f (e x)) := by rw [hfix]; exact hei.hasFDerivAt
  have hg : fderiv ℝ g x = B.comp (D.comp A) :=
    ((hbi.comp x (hf.hasFDerivAt.comp x he.hasFDerivAt)).congr_of_eventuallyEq hconj).fderiv
  have heq : fderiv ℝ g x - ContinuousLinearMap.id ℝ E =
      B.comp ((D - ContinuousLinearMap.id ℝ F).comp A) := by
    rw [hg]
    ext v
    have hh := congrArg (fun T : E →L[ℝ] E => T v) hba
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hh
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_sub, hh]
  rw [heq]
  exact hb.comp (hnd.comp ha)

variable {M N H G : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [TopologicalSpace H] [TopologicalSpace G]
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F G)
  [ChartedSpace H M] [ChartedSpace G N]

def NondegenerateAt (g : M → M) (x : M) : Prop :=
  let c := extChartAt I x
  Function.Bijective (fderiv ℝ (c ∘ g ∘ c.symm) (c x) - ContinuousLinearMap.id ℝ E)

def coordinateChart [I.Boundaryless] (x : M) : OpenPartialHomeomorph M E := {
  toPartialEquiv := extChartAt I x
  continuousOn_toFun := continuousOn_extChartAt x
  continuousOn_invFun := continuousOn_extChartAt_symm x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x }

lemma coordinate_mem [I.Boundaryless] (x : M) : x ∈ (coordinateChart I x).source :=
  mem_extChartAt_source x

lemma coordinate_smooth [I.Boundaryless] [IsManifold I ∞ M] (x : M) :
    ContMDiffAt I 𝓘(ℝ,E) ∞ (coordinateChart I x) x ∧
    ContMDiffAt 𝓘(ℝ,E) I ∞ (coordinateChart I x).symm (coordinateChart I x x) := by
  exact ⟨contMDiffAt_extChartAt,
    (contMDiffOn_extChartAt_symm x _ (mem_extChartAt_target x)).contMDiffAt
      (extChartAt_target_mem_nhds x)⟩

 theorem nondegenerate_manifold_conjugate [I.Boundaryless] [J.Boundaryless]
    [IsManifold I ∞ M] [IsManifold J ∞ N]
    (e : OpenPartialHomeomorph M N)
    (he : ContMDiffOn I J ∞ e e.source)
    (hei : ContMDiffOn J I ∞ e.symm e.target)
    (g : M → M) (f : N → N) (x : M) (hx : x ∈ e.source)
    (hf : ContMDiffAt J J ∞ f (e x)) (hfix : f (e x) = e x)
    (hconj : ∀ᶠ z in 𝓝 x, g z = e.symm (f (e z)))
    (hnd : NondegenerateAt J f (e x)) : NondegenerateAt I g x := by
  let c := coordinateChart I x
  let a := coordinateChart J (e x)
  let u := c.symm.trans (e.trans a)
  have hc : x ∈ c.source := coordinate_mem I x
  have ha : e x ∈ a.source := coordinate_mem J (e x)
  have hcu : c.symm (c x) = x := c.left_inv hc
  have hau : a.symm (a (e x)) = e x := a.left_inv ha
  have hu : c x ∈ u.source := by
    change c x ∈ c.target ∧ c.symm (c x) ∈ (e.trans a).source
    rw [hcu]
    exact ⟨c.map_source hc,hx,ha⟩
  have hux : u (c x) = a (e x) := by change a (e (c.symm (c x))) = _; rw [hcu]
  have hes := (he x hx).contMDiffAt (e.open_source.mem_nhds hx)
  have heis := (hei (e x) (e.map_source hx)).contMDiffAt
    (e.open_target.mem_nhds (e.map_source hx))
  have hcsm := coordinate_smooth I x
  have hasm := coordinate_smooth J (e x)
  have hec : ContMDiffAt 𝓘(ℝ,E) J ∞ (e ∘ c.symm) (c x) := by
    apply ContMDiffAt.comp _ _ hcsm.2
    rw [hcu]
    exact hes
  have huis : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ u (c x) := by
    change ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ (a ∘ e ∘ c.symm) (c x)
    apply ContMDiffAt.comp _ _ hec
    change ContMDiffAt J 𝓘(ℝ,F) ∞ a (e (c.symm (c x)))
    rw [hcu]
    exact hasm.1
  have heia : ContMDiffAt 𝓘(ℝ,F) I ∞ (e.symm ∘ a.symm) (a (e x)) := by
    apply ContMDiffAt.comp _ _ hasm.2
    rw [hau]
    exact heis
  have hui : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ u.symm (u (c x)) := by
    rw [hux]
    change ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ (c ∘ e.symm ∘ a.symm) (a (e x))
    apply ContMDiffAt.comp _ _ heia
    change ContMDiffAt I 𝓘(ℝ,E) ∞ c (e.symm (a.symm (a (e x))))
    rw [hau,e.left_inv hx]
    exact hcsm.1
  let f₁ := a ∘ f ∘ a.symm
  let g₁ := c ∘ g ∘ c.symm
  have hfa : ContMDiffAt 𝓘(ℝ,F) J ∞ (f ∘ a.symm) (a (e x)) := by
    apply ContMDiffAt.comp _ _ hasm.2
    rw [hau]
    exact hf
  have hf₁ : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F) ∞ f₁ (u (c x)) := by
    rw [hux]
    apply ContMDiffAt.comp _ _ hfa
    change ContMDiffAt J 𝓘(ℝ,F) ∞ a (f (a.symm (a (e x))))
    rw [hau,hfix]
    exact hasm.1
  have hfix₁ : f₁ (u (c x)) = u (c x) := by
    rw [hux]
    change a (f (a.symm (a (e x)))) = _
    rw [hau,hfix]
  have hleft : ∀ᶠ z in 𝓝 (c x), u.symm (u z) = z := by
    filter_upwards [u.open_source.mem_nhds hu] with z hz
    exact u.left_inv hz
  have hright : ∀ᶠ z in 𝓝 (u (c x)), u (u.symm z) = z := by
    filter_upwards [u.open_target.mem_nhds (u.map_source hu)] with z hz
    exact u.right_inv hz
  have hpre : ∀ᶠ z in 𝓝 (c x), e (c.symm z) ∈ a.source :=
    hec.continuousAt (by simpa only [Function.comp_apply,hcu] using a.open_source.mem_nhds ha)
  have hfec : ContinuousAt (f ∘ e ∘ c.symm) (c x) := by
    apply ContinuousAt.comp _ hec.continuousAt
    change ContinuousAt f (e (c.symm (c x)))
    rw [hcu]
    exact hf.continuousAt
  have hpost : ∀ᶠ z in 𝓝 (c x), f (e (c.symm z)) ∈ a.source :=
    hfec (by simpa only [Function.comp_apply,hcu,hfix] using a.open_source.mem_nhds ha)
  have hgj : ∀ᶠ z in 𝓝 (c x), g (c.symm z) = e.symm (f (e (c.symm z))) := by
    have hn : {z | g z = e.symm (f (e z))} ∈ 𝓝 (c.symm (c x)) := by
      rw [hcu]
      exact hconj
    exact (show ContinuousAt c.symm (c x) from hcsm.2.continuousAt) hn
  have hconj₁ : ∀ᶠ z in 𝓝 (c x), g₁ z = u.symm (f₁ (u z)) := by
    filter_upwards [hpre,hpost,hgj] with z hz hz' hzg
    change c (g (c.symm z)) =
      c (e.symm (a.symm (a (f (a.symm (a (e (c.symm z))))))))
    rw [a.left_inv hz, a.left_inv hz', hzg]
  have hnd₁ : Function.Bijective
      (fderiv ℝ f₁ (u (c x)) - ContinuousLinearMap.id ℝ F) := by
    rw [hux]
    exact hnd
  exact nondegenerate_local_conjugate u u.symm g₁ f₁ (c x)
    ((contMDiffAt_iff_contDiffAt.mp huis).differentiableAt (by simp))
    ((contMDiffAt_iff_contDiffAt.mp hui).differentiableAt (by simp))
    ((contMDiffAt_iff_contDiffAt.mp hf₁).differentiableAt (by simp))
    hleft hright hfix₁ hconj₁ hnd₁

end
end MorseArnold.Conjugacy

end

end OAI
