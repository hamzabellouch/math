import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ContDiffLinearEmbedding

namespace OAI


noncomputable section
namespace TamingCompatibility.ManifoldForms
open FormSmoothness Set
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] {k : ℕ}

def chartLift (p : X) (β : Space → Space [⋀^Fin k]→L[ℝ] ℝ) : Form X k := by
  classical
  exact fun x => if x ∈ (extChartAt Model p).source then
    (β (extChartAt Model p x)).compContinuousLinearMap (mfderiv Model Model (extChartAt Model p) x)
  else 0

def liftSupport (p : X) (β : Space → Space [⋀^Fin k]→L[ℝ] ℝ) : Set X :=
  (extChartAt Model p).symm '' tsupport β

omit [IsManifold Model ∞ X] [T2Space X] in
lemma liftSupport_subset (p : X) {β : Space → Space [⋀^Fin k]→L[ℝ] ℝ}
    (hβ : tsupport β ⊆ (extChartAt Model p).target) :
    liftSupport p β ⊆ (extChartAt Model p).source := by
  rintro _ ⟨z,hz,rfl⟩
  exact (extChartAt Model p).map_target (hβ hz)

omit [IsManifold Model ∞ X] [T2Space X] in
lemma liftSupport_compact (p : X) {β : Space → Space [⋀^Fin k]→L[ℝ] ℝ}
    (hc : HasCompactSupport β) (hβ : tsupport β ⊆ (extChartAt Model p).target) :
    IsCompact (liftSupport p β) :=
  hc.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono hβ)

omit [IsManifold Model ∞ X] [T2Space X] in
lemma chartLift_zero_off (p : X) (β : Space → Space [⋀^Fin k]→L[ℝ] ℝ)
    {x : X} (hx : x ∉ liftSupport p β) : chartLift p β x = 0 := by
  unfold chartLift
  split_ifs with hs
  · have hz : extChartAt Model p x ∉ tsupport β := by
      intro hz
      exact hx ⟨_,hz,(extChartAt Model p).left_inv hs⟩
    rw [image_eq_zero_of_notMem_tsupport hz]
    rfl
  · rfl

omit [T2Space X] in
lemma pullback_chartLift (p : X) (β : Space → Space [⋀^Fin k]→L[ℝ] ℝ)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    pullback (chartLift p β) (extChartAt Model p).symm z = β z := by
  classical
  have hs := (extChartAt Model p).map_target hz
  simp only [pullback,chartLift,ite_eq_left hs,(extChartAt Model p).right_inv hz]
  have hi := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := Model) hz
  simp only [Model,modelWithCornersSelf_coe,Set.range_id,mfderivWithin_univ] at hi
  change (β z).compContinuousLinearMap
    (mfderiv Model Model (extChartAt Model p) ((extChartAt Model p).symm z) ∘L
      mfderiv Model Model (extChartAt Model p).symm z) = _
  erw [hi]
  rfl

lemma chartLift_smooth (p : X) {β : Space → Space [⋀^Fin k]→L[ℝ] ℝ}
    (hs : ContDiff ℝ ∞ β) (hc : HasCompactSupport β)
    (hβ : tsupport β ⊆ (extChartAt Model p).target) : Smooth (chartLift p β) := by
  intro f U hU hf y hy
  have hfy := (hf y hy).contMDiffAt (hU.mem_nhds hy)
  by_cases hk : f y ∈ liftSupport p β
  · have hsrc := liftSupport_subset p hβ hk
    let g : Space → Space := (extChartAt Model p) ∘ f
    have hgy : ContMDiffAt Model Model ∞ g y :=
      (contMDiffAt_extChartAt' (I := Model) (by simpa only [extChartAt_source] using hsrc)).comp y hfy
    have hg : ContDiffAt ℝ ∞ g y := contMDiffAt_iff_contDiffAt.mp hgy
    have he : pullback (chartLift p β) f =ᶠ[𝓝 y]
        fun z => (β (g z)).compContinuousLinearMap (fderiv ℝ g z) := by
      have hne := hfy.continuousAt.eventually ((isOpen_extChartAt_source p).mem_nhds hsrc)
      filter_upwards [hne,hU.mem_nhds hy] with z hz hzU
      change f z ∈ (extChartAt Model p).source at hz
      have hfz := ((hf z hzU).contMDiffAt (hU.mem_nhds hzU)).mdifferentiableAt (by simp)
      have hez := (contMDiffAt_extChartAt' (I := Model) (n := ∞)
        (by simpa only [extChartAt_source] using hz)).mdifferentiableAt (by simp)
      simp only [pullback,chartLift,ite_eq_left hz]
      change (β (g z)).compContinuousLinearMap
        (mfderiv Model Model (extChartAt Model p) (f z) ∘L mfderiv Model Model f z) = _
      erw [← mfderiv_comp z hez hfz,mfderiv_eq_fderiv]
      rfl
    exact (((hs.contDiffAt.comp y hg).compAlternating
      (hg.fderiv_right (by simp))).congr_of_eventuallyEq he).contDiffWithinAt
  · have hne := hfy.continuousAt.eventually
      ((liftSupport_compact p hc hβ).isClosed.isOpen_compl.mem_nhds hk)
    have he : pullback (chartLift p β) f =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [hne] with z hz
      unfold pullback
      rw [chartLift_zero_off p β hz]
      rfl
    exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt

end TamingCompatibility.ManifoldForms

end

end OAI
