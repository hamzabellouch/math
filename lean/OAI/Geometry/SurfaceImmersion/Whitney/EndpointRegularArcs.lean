import OAI.Geometry.SurfaceImmersion.Whitney.RegularPathEndpointPieces
import OAI.Geometry.SurfaceImmersion.Whitney.FiniteRegularPathSmooth
import OAI.Geometry.SurfaceImmersion.Whitney.PathCornerNeighborhood

namespace OAI

/-! Genuine smooth compact arcs at both ends of the finite source path,
with unchanged interior germs for later attachment. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q}

lemma affine_arc_smooth_regular (A : SmoothCompactArc planeModel M) {a b : ℝ} (ha : a ≠ 0) :
    ContMDiffOn 𝓘(ℝ) planeModel ∞ (fun u : ℝ => A.curve (a*u+b))
      ((fun u : ℝ => a*u+b) ⁻¹' A.domain) ∧
      ∀ u, a*u+b ∈ A.domain → Function.Injective
        (mfderiv 𝓘(ℝ) planeModel (fun v : ℝ => A.curve (a*v+b)) u) := by
  have hparam : ContDiff ℝ ∞ (fun u : ℝ => a*u+b) := by fun_prop
  refine ⟨A.smooth.comp hparam.contMDiff.contMDiffOn (fun _ hu => hu),?_⟩
  intro u hu
  change Function.Injective (mfderiv 𝓘(ℝ) planeModel (A.curve ∘ fun v : ℝ => a*v+b) u)
  rw [mfderiv_comp u ((A.smooth.contMDiffAt (A.domain_open.mem_nhds hu)).mdifferentiableAt (by simp))
    (hparam.contMDiff.mdifferentiable (by simp) u)]
  exact (A.regular _ hu).comp (affine_parameter_regular ha u)

theorem first_regular_arc (hγ : FiniteRegularPath planeModel γ) (hi : Function.Injective γ)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ (P : SmoothCompactArc planeModel M) (r : ℝ),
      0 < r ∧ r < η ∧ P.start = 0 ∧ P.finish = r ∧
      (∀ u ∈ Icc 0 r, P.curve u = γ.extend u) ∧ P.curve P.start = p ∧
      P.curve =ᶠ[𝓝 P.finish] γ.extend := by
  obtain ⟨A,a,b,r₀,hr₀,ha,hpiece⟩ := hγ.cover.some.first_regular_piece hi
  let r := min (r₀/2) (η/2)
  have hr : 0 < r := lt_min (half_pos hr₀) (half_pos hη)
  have hrr₀ : r < r₀ := (min_le_left _ _).trans_lt (half_lt_self hr₀)
  have hrη : r < η := (min_le_right _ _).trans_lt (half_lt_self hη)
  let U := (fun u : ℝ => a*u+b) ⁻¹' A.domain
  have hU : IsOpen U := A.domain_open.preimage (by fun_prop)
  have hmatch : ∀ u ∈ Icc 0 r, A.curve (a*u+b) = γ.extend u :=
    fun u hu => (hpiece u ⟨hu.1,hu.2.trans hrr₀.le⟩).2.symm
  have hsub : Icc 0 r ⊆ U := fun u hu => (hpiece u ⟨hu.1,hu.2.trans hrr₀.le⟩).1
  have hd := affine_arc_smooth_regular A (b := b) ha
  have hinj : InjOn (fun u : ℝ => A.curve (a*u+b)) (Icc 0 r) := by
    intro u hu v hv he
    apply embeddedPath_extend_injOn γ hi ⟨hu.1,hu.2.trans (hrη.le.trans hη1)⟩
      ⟨hv.1,hv.2.trans (hrη.le.trans hη1)⟩
    rwa [← hmatch u hu,← hmatch v hv]
  let P : SmoothCompactArc planeModel M :=
    ⟨fun u => A.curve (a*u+b),0,r,hr,U,hU,hsub,hd.1,fun u hu => hd.2 u hu,hinj⟩
  refine ⟨P,r,hr,hrη,rfl,rfl,hmatch,?_,?_⟩
  · change A.curve (a*0+b) = p
    rw [hmatch 0 ⟨le_rfl,hr.le⟩]
    exact γ.extend_zero
  · filter_upwards [Ioo_mem_nhds hr hrr₀] with u hu
    exact (hpiece u ⟨hu.1.le,hu.2.le⟩).2.symm

theorem last_regular_arc (hγ : FiniteRegularPath planeModel γ) (hi : Function.Injective γ)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ (P : SmoothCompactArc planeModel M) (l : ℝ),
      1-η < l ∧ l < 1 ∧ P.start = l ∧ P.finish = 1 ∧
      (∀ u ∈ Icc l 1, P.curve u = γ.extend u) ∧ P.curve P.finish = q ∧
      P.curve =ᶠ[𝓝 P.start] γ.extend := by
  obtain ⟨A,a,b,l₀,hl₀,ha,hpiece⟩ := hγ.cover.some.last_regular_piece hi
  let d := min ((1-l₀)/2) (η/2)
  let l := 1-d
  have hdpos : 0 < d := lt_min (half_pos (sub_pos.mpr hl₀)) (half_pos hη)
  have hdl : d < 1-l₀ := (min_le_left _ _).trans_lt (half_lt_self (sub_pos.mpr hl₀))
  have hdη : d < η := (min_le_right _ _).trans_lt (half_lt_self hη)
  have hll₀ : l₀ < l := by dsimp only [l]; linarith
  have hl1 : l < 1 := by dsimp only [l]; linarith
  have hηl : 1-η < l := by dsimp only [l]; linarith
  have hl0 : 0 < l := lt_of_le_of_lt (sub_nonneg.mpr hη1) hηl
  let U := (fun u : ℝ => a*u+b) ⁻¹' A.domain
  have hU : IsOpen U := A.domain_open.preimage (by fun_prop)
  have hmatch : ∀ u ∈ Icc l 1, A.curve (a*u+b) = γ.extend u :=
    fun u hu => (hpiece u ⟨hll₀.le.trans hu.1,hu.2⟩).2.symm
  have hsub : Icc l 1 ⊆ U := fun u hu => (hpiece u ⟨hll₀.le.trans hu.1,hu.2⟩).1
  have hdata := affine_arc_smooth_regular A (b := b) ha
  have hinj : InjOn (fun u : ℝ => A.curve (a*u+b)) (Icc l 1) := by
    intro u hu v hv he
    apply embeddedPath_extend_injOn γ hi ⟨hl0.le.trans hu.1,hu.2⟩ ⟨hl0.le.trans hv.1,hv.2⟩
    rwa [← hmatch u hu,← hmatch v hv]
  let P : SmoothCompactArc planeModel M :=
    ⟨fun u => A.curve (a*u+b),l,1,hl1,U,hU,hsub,hdata.1,fun u hu => hdata.2 u hu,hinj⟩
  refine ⟨P,l,hηl,hl1,rfl,rfl,hmatch,?_,?_⟩
  · change A.curve (a*1+b) = q
    rw [hmatch 1 ⟨hl1.le,le_rfl⟩]
    exact γ.extend_one
  · filter_upwards [Ioo_mem_nhds hll₀ hl1] with u hu
    exact (hpiece u ⟨hu.1.le,hu.2.le⟩).2.symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
