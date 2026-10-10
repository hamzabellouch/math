import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ContDiffLinearEmbedding

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X]

def scalarChartLift (p : X) (f : Space → ℝ) : X → ℝ := by
  classical
  exact fun x => if x ∈ (extChartAt Model p).source then f (extChartAt Model p x) else 0

def scalarLiftSupport (p : X) (f : Space → ℝ) : Set X :=
  (extChartAt Model p).symm '' tsupport f

omit [IsManifold Model ∞ X] [T2Space X] in
lemma scalarLiftSupport_subset (p : X) {f : Space → ℝ}
    (hf : tsupport f ⊆ (extChartAt Model p).target) :
    scalarLiftSupport p f ⊆ (extChartAt Model p).source := by
  rintro _ ⟨z,hz,rfl⟩
  exact (extChartAt Model p).map_target (hf hz)

omit [IsManifold Model ∞ X] [T2Space X] in
lemma scalarLiftSupport_compact (p : X) {f : Space → ℝ}
    (hc : HasCompactSupport f) (hf : tsupport f ⊆ (extChartAt Model p).target) :
    IsCompact (scalarLiftSupport p f) :=
  hc.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono hf)

omit [IsManifold Model ∞ X] [T2Space X] in
lemma scalarChartLift_zero_off (p : X) (f : Space → ℝ)
    {x : X} (hx : x ∉ scalarLiftSupport p f) : scalarChartLift p f x = 0 := by
  unfold scalarChartLift
  split_ifs with hs
  · exact image_eq_zero_of_notMem_tsupport (fun hz => hx ⟨_,hz,(extChartAt Model p).left_inv hs⟩)
  · rfl

omit [IsManifold Model ∞ X] [T2Space X] in
lemma scalarChartLift_apply_inverse (p : X) (f : Space → ℝ)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    scalarChartLift p f ((extChartAt Model p).symm z) = f z := by
  classical
  simp only [scalarChartLift,ite_eq_left ((extChartAt Model p).map_target hz),
    (extChartAt Model p).right_inv hz]

lemma scalarChartLift_smooth (p : X) {f : Space → ℝ}
    (hs : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hf : tsupport f ⊆ (extChartAt Model p).target) :
    ContMDiff Model 𝓘(ℝ,ℝ) ∞ (scalarChartLift p f) := by
  intro x
  by_cases hk : x ∈ scalarLiftSupport p f
  · have hsrc := scalarLiftSupport_subset p hf hk
    have he : scalarChartLift p f =ᶠ[𝓝 x] fun y => f (extChartAt Model p y) := by
      filter_upwards [(isOpen_extChartAt_source p).mem_nhds hsrc] with y hy
      simp only [scalarChartLift,ite_eq_left hy]
    have hchart := contMDiffAt_extChartAt' (I := Model) (n := ∞)
      (by simpa only [extChartAt_source] using hsrc)
    exact ((contMDiff_iff_contDiff.mpr hs).contMDiffAt.comp x hchart).congr_of_eventuallyEq he
  · have he : scalarChartLift p f =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(scalarLiftSupport_compact p hc hf).isClosed.isOpen_compl.mem_nhds hk] with y hy
      exact scalarChartLift_zero_off p f hy
    exact contMDiffAt_const.congr_of_eventuallyEq he

omit [IsManifold Model ∞ X] in
lemma scalarChartLift_tsupport (p : X) {f : Space → ℝ}
    (hc : HasCompactSupport f) (hf : tsupport f ⊆ (extChartAt Model p).target) :
    tsupport (scalarChartLift p f) ⊆ scalarLiftSupport p f := by
  apply closure_minimal _ (scalarLiftSupport_compact p hc hf).isClosed
  intro x hx
  by_contra h
  exact hx (scalarChartLift_zero_off p f h)

omit [IsManifold Model ∞ X] [T2Space X] in

lemma scalarChartLift_fderiv (p : X) (f : Space → ℝ) {z : Space}
    (hz : z ∈ (extChartAt Model p).target) :
    fderiv ℝ (scalarChartLift p f ∘ (extChartAt Model p).symm) z = fderiv ℝ f z := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz] with w hw
  exact scalarChartLift_apply_inverse p f hw

end TamingCompatibility.ManifoldForms

end
end

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X]

def vectorChartLift (p : X) (f : Space → Space) : X → Space := by
  classical
  exact fun x => if x ∈ (extChartAt Model p).source then f (extChartAt Model p x) else 0

def vectorLiftSupport (p : X) (f : Space → Space) : Set X :=
  (extChartAt Model p).symm '' tsupport f

omit [IsManifold Model ∞ X] [T2Space X] in
lemma vectorLiftSupport_subset (p : X) {f : Space → Space}
    (hf : tsupport f ⊆ (extChartAt Model p).target) :
    vectorLiftSupport p f ⊆ (extChartAt Model p).source := by
  rintro _ ⟨z,hz,rfl⟩
  exact (extChartAt Model p).map_target (hf hz)

omit [IsManifold Model ∞ X] [T2Space X] in
lemma vectorLiftSupport_compact (p : X) {f : Space → Space}
    (hc : HasCompactSupport f) (hf : tsupport f ⊆ (extChartAt Model p).target) :
    IsCompact (vectorLiftSupport p f) :=
  hc.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono hf)

omit [IsManifold Model ∞ X] [T2Space X] in
lemma vectorChartLift_zero_off (p : X) (f : Space → Space)
    {x : X} (hx : x ∉ vectorLiftSupport p f) : vectorChartLift p f x = 0 := by
  unfold vectorChartLift
  split_ifs with hs
  · exact image_eq_zero_of_notMem_tsupport (fun hz => hx ⟨_,hz,(extChartAt Model p).left_inv hs⟩)
  · rfl

omit [IsManifold Model ∞ X] [T2Space X] in
lemma vectorChartLift_apply_inverse (p : X) (f : Space → Space)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    vectorChartLift p f ((extChartAt Model p).symm z) = f z := by
  classical
  simp only [vectorChartLift,ite_eq_left ((extChartAt Model p).map_target hz),
    (extChartAt Model p).right_inv hz]

lemma vectorChartLift_smooth (p : X) {f : Space → Space}
    (hs : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hf : tsupport f ⊆ (extChartAt Model p).target) :
    ContMDiff Model Model ∞ (vectorChartLift p f) := by
  intro x
  by_cases hk : x ∈ vectorLiftSupport p f
  · have hsrc := vectorLiftSupport_subset p hf hk
    have he : vectorChartLift p f =ᶠ[𝓝 x] fun y => f (extChartAt Model p y) := by
      filter_upwards [(isOpen_extChartAt_source p).mem_nhds hsrc] with y hy
      simp only [vectorChartLift,ite_eq_left hy]
    have hchart := contMDiffAt_extChartAt' (I := Model) (n := ∞)
      (by simpa only [extChartAt_source] using hsrc)
    exact ((contMDiff_iff_contDiff.mpr hs).contMDiffAt.comp x hchart).congr_of_eventuallyEq he
  · have he : vectorChartLift p f =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(vectorLiftSupport_compact p hc hf).isClosed.isOpen_compl.mem_nhds hk] with y hy
      exact vectorChartLift_zero_off p f hy
    exact contMDiffAt_const.congr_of_eventuallyEq he

end TamingCompatibility.ManifoldForms

end
end

end
end

end OAI
