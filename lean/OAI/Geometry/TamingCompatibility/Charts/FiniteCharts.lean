import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ContDiffLinearEmbedding

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility.ManifoldLocalization
open Set Function
open scoped Topology Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]

structure FiniteCharts (X : Type*) [TopologicalSpace X] [ChartedSpace Space X]
    [IsManifold Model ∞ X] where
  centers : Finset X
  partition : SmoothPartitionOfUnity centers Model X
  subordinate : partition.IsSubordinate (fun p => (extChartAt Model p.val).source)

theorem finiteCharts_nonempty : Nonempty (FiniteCharts X) := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun p : X => (chartAt Space p).source)
    (fun p => (chartAt Space p).open_source)
    (fun x _ => mem_iUnion_of_mem x (mem_chart_source Space x))
  have hc : (univ : Set X) ⊆ ⋃ p : s, (chartAt Space p.val).source := by
    intro x hx
    obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion_of_mem ⟨p,hp⟩ hxp
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate Model isClosed_univ
    (fun p : s => (chartAt Space p.val).source)
    (fun p => (chartAt Space p.val).open_source) hc
  refine ⟨⟨s,ρ,?_⟩⟩
  simpa only [extChartAt_source] using hρ

noncomputable def finiteCharts : FiniteCharts X := Classical.choice finiteCharts_nonempty

variable (A : FiniteCharts X)

omit [T2Space X] [CompactSpace X] in
lemma partition_sum (x : X) : ∑ p : A.centers, A.partition p x = 1 := by
  simpa only [finsum_eq_sum_of_fintype] using A.partition.sum_eq_one (mem_univ x)

def coordinateSupport (p : A.centers) : Set Space :=
  (extChartAt Model p.val) '' tsupport (A.partition p)

omit [T2Space X] in
lemma coordinateSupport_compact (p : A.centers) : IsCompact (coordinateSupport A p) := by
  apply (isClosed_tsupport _).isCompact.image_of_continuousOn
  exact (continuousOn_extChartAt p.val).mono (A.subordinate p)

omit [T2Space X] [CompactSpace X] in
lemma coordinateSupport_subset (p : A.centers) :
    coordinateSupport A p ⊆ (extChartAt Model p.val).target := by
  rintro y ⟨x,hx,rfl⟩
  exact (extChartAt Model p.val).map_source (A.subordinate p hx)

section Extension
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma smooth_indicator_of_compact {U K : Set E} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (hz : ∀ x ∈ U, x ∉ K → f x = 0) :
    ContDiff ℝ ∞ (U.indicator f) ∧ HasCompactSupport (U.indicator f) := by
  have hs : support (U.indicator f) ⊆ K := by
    intro x hx
    by_contra h
    by_cases hu : x ∈ U
    · exact hx (by rw [indicator_of_mem hu]; exact hz x hu h)
    · exact hx (indicator_of_notMem hu f)
  refine ⟨?_, HasCompactSupport.of_support_subset_isCompact hK hs⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hu : x ∈ U
  · apply ((hf x hu).contDiffAt (hU.mem_nhds hu)).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hu] with y hy
    exact indicator_of_mem hy f
  · have hx : x ∉ K := fun h => hu (hKU h)
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact notMem_support.mp (fun h => hy (hs h))
end Extension

def localizedFunction {k : ℕ} (p : A.centers) (α : ManifoldForms.Form X k) :
    Space → Space [⋀^Fin k]→L[ℝ] ℝ :=
  (extChartAt Model p.val).target.indicator (fun y =>
    A.partition p ((extChartAt Model p.val).symm y) •
      ManifoldForms.pullback α (extChartAt Model p.val).symm y)

omit [T2Space X] in
lemma localizedFunction_smooth_compact {k : ℕ} (p : A.centers)
    (α : ManifoldForms.Form X k) (hα : ManifoldForms.Smooth α) :
    ContDiff ℝ ∞ (localizedFunction A p α) ∧ HasCompactSupport (localizedFunction A p α) := by
  apply smooth_indicator_of_compact (isOpen_extChartAt_target p.val)
    (coordinateSupport_compact A p) (coordinateSupport_subset A p)
  · have hρ : ContDiffOn ℝ ∞
        (fun y => A.partition p ((extChartAt Model p.val).symm y))
        (extChartAt Model p.val).target := by
      exact (A.partition p).contMDiff.comp_contMDiffOn
        (contMDiffOn_extChartAt_symm p.val) |>.contDiffOn
    exact hρ.smul (ManifoldForms.smooth_chart α hα p.val)
  · intro y hy hK
    have hz : (extChartAt Model p.val).symm y ∉ tsupport (A.partition p) := by
      intro h
      apply hK
      exact ⟨(extChartAt Model p.val).symm y,h,(extChartAt Model p.val).right_inv hy⟩
    rw [image_eq_zero_of_notMem_tsupport hz, zero_smul]

def localizedSchwartz {k : ℕ} (p : A.centers)
    (α : ManifoldForms.Form X k) (hα : ManifoldForms.Smooth α) :
    𝓢(Space,Space [⋀^Fin k]→L[ℝ] ℝ) :=
  (localizedFunction_smooth_compact A p α hα).2.toSchwartzMap
    (localizedFunction_smooth_compact A p α hα).1

omit [T2Space X] [CompactSpace X] in
lemma localizedFunction_add {k : ℕ} (p : A.centers) (α β : ManifoldForms.Form X k) :
    localizedFunction A p (α + β) = localizedFunction A p α + localizedFunction A p β := by
  funext y
  unfold localizedFunction
  rw [ManifoldForms.pullback_add]
  by_cases hy : y ∈ (extChartAt Model p.val).target
  · simp only [indicator_of_mem hy, Pi.add_apply, smul_add]
  · simp only [indicator_of_notMem hy, Pi.add_apply, add_zero]

omit [T2Space X] [CompactSpace X] in
lemma localizedFunction_smul {k : ℕ} (p : A.centers) (c : ℝ) (α : ManifoldForms.Form X k) :
    localizedFunction A p (c • α) = c • localizedFunction A p α := by
  funext y
  unfold localizedFunction
  rw [ManifoldForms.pullback_smul]
  by_cases hy : y ∈ (extChartAt Model p.val).target
  · simp only [indicator_of_mem hy, Pi.smul_apply]
    exact smul_comm _ _ _
  · simp only [indicator_of_notMem hy, Pi.smul_apply, smul_zero]

omit [T2Space X] [CompactSpace X] in
lemma localizedFunction_zero {k : ℕ} (p : A.centers) :
    localizedFunction A p (0 : ManifoldForms.Form X k) = 0 := by
  simpa only [zero_smul] using localizedFunction_smul A p 0 (0 : ManifoldForms.Form X k)

omit [T2Space X] [CompactSpace X] in

lemma eq_zero_of_localizedFunction_eq_zero {k : ℕ} (α : ManifoldForms.Form X k)
    (h : ∀ p : A.centers, localizedFunction A p α = 0) : α = 0 := by
  classical
  funext x
  have hn : (∑ p : A.centers, A.partition p x) ≠ 0 := by
    rw [partition_sum A x]
    exact one_ne_zero
  obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hx : x ∈ (extChartAt Model p.val).source :=
    A.subordinate p (subset_tsupport _ hp)
  let e := extChartAt Model p.val
  have hy : e x ∈ e.target := e.map_source hx
  have hz := congrFun (h p) (e x)
  change e.target.indicator (fun y => A.partition p (e.symm y) •
    ManifoldForms.pullback α e.symm y) (e x) = 0 at hz
  rw [indicator_of_mem hy, e.left_inv hx] at hz
  have ha : ManifoldForms.pullback α e.symm (e x) = 0 :=
    (smul_eq_zero.mp hz).resolve_left hp
  have hsurj : Function.Surjective (mfderiv Model Model e.symm (e x)) := by
    have hi := (isInvertible_mfderivWithin_extChartAt_symm (I := Model) hy).surjective
    simpa only [ModelWithCorners.Boundaryless.range_eq_univ, mfderivWithin_univ] using hi
  ext v
  choose w hw using fun i : Fin k => hsurj (v i)
  have he := congrArg (fun q : Space [⋀^Fin k]→L[ℝ] ℝ => q w) ha
  change α (e.symm (e x)) (fun i => mfderiv Model Model e.symm (e x) (w i)) = 0 at he
  simp only [hw] at he
  change α (e.symm (e x)) v = 0 at he
  rw [e.left_inv hx] at he
  exact he

end TamingCompatibility.ManifoldLocalization

end

end OAI
