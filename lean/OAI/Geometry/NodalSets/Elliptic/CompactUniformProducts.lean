import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.UniformSpace.CompactConvergence

namespace OAI

namespace Yau.Analysis
open Set Filter
open scoped Topology
noncomputable section

theorem compact_uniform_mul {X : Type*} [TopologicalSpace X] [T2Space X]
    (Q : Set X) (hQ : IsCompact Q) (F G : ℕ → X → ℝ) (f g : X → ℝ)
    (hF : ∀ j, Continuous (F j)) (hG : ∀ j, Continuous (G j))
    (hf : Continuous f) (hg : Continuous g)
    (hFc : TendstoUniformlyOn F f atTop Q) (hGc : TendstoUniformlyOn G g atTop Q) :
    TendstoUniformlyOn (fun j x ↦ F j x*G j x) (fun x ↦ f x*g x) atTop Q := by
  let := isCompact_iff_compactSpace.mp hQ
  have h1 := (hf.continuousOn.tendsto_domRestrict_iff_tendstoUniformlyOn
    (fun j ↦ (hF j).continuousOn)).mpr hFc
  have h2 := (hg.continuousOn.tendsto_domRestrict_iff_tendstoUniformlyOn
    (fun j ↦ (hG j).continuousOn)).mpr hGc
  exact ((hf.mul hg).continuousOn.tendsto_domRestrict_iff_tendstoUniformlyOn
    (fun j ↦ ((hF j).mul (hG j)).continuousOn)).mp (h1.mul h2)

theorem finite_uniform_sum {X I : Type*} (S : Finset I) (Q : Set X)
    (F : I → ℕ → X → ℝ) (f : I → X → ℝ)
    (h : ∀ i ∈ S, TendstoUniformlyOn (F i) (f i) atTop Q) :
    TendstoUniformlyOn (fun j x ↦ ∑ i ∈ S, F i j x) (fun x ↦ ∑ i ∈ S, f i x) atTop Q := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using ((by intro s hs; exact Eventually.of_forall (fun _ _ _ ↦ refl_mem_uniformity hs)) :
      TendstoUniformlyOn (fun _ : ℕ ↦ fun _ : X ↦ (0:ℝ)) (fun _ ↦ 0) atTop Q)
  | @insert i S hi ih =>
    simpa only [Finset.sum_insert hi,Pi.add_def] using
      (h i (Finset.mem_insert_self i S)).add (ih (fun k hk ↦ h k (Finset.mem_insert_of_mem hk)))

end
end Yau.Analysis

end OAI
