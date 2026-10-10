import OAI.Geometry.SurfaceImmersion.Geometry.CriticalSetClosed
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

/-! Uniform first-jet stability of regular zero sets on compact domains.
This allows the finite pair-patch construction to preserve earlier patches. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
local instance zeroJetNormed : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance zeroJetSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance

def regularZeroJets : Set (F × (E →L[ℝ] F)) :=
  {z | z.1 ≠ 0 ∨ Function.Surjective z.2}

lemma regularZeroJets_open : IsOpen (regularZeroJets (E := E) (F := F)) :=
  (isOpen_compl_singleton.preimage continuous_fst).union
    (surjective_clm_open.preimage continuous_snd)

theorem compact_regular_zero_stability {f : E → F} (hf : ContDiff ℝ ∞ f)
    {K : Set E} (hK : IsCompact K)
    (hreg : ∀ x ∈ K, f x = 0 → Function.Surjective (fderiv ℝ f x)) :
    ∃ ε > 0, ∀ g : E → F,
      (∀ x ∈ K, ‖g x-f x‖ < ε) →
      (∀ x ∈ K, ‖fderiv ℝ g x-fderiv ℝ f x‖ < ε) →
      ∀ x ∈ K, g x = 0 → Function.Surjective (fderiv ℝ g x) := by
  let J : E → F × (E →L[ℝ] F) := fun x => (f x,fderiv ℝ f x)
  have hJ : Continuous J := hf.continuous.prodMk (hf.continuous_fderiv (by simp))
  have hsub : J '' K ⊆ regularZeroJets := by
    rintro z ⟨x,hx,rfl⟩
    by_cases h : f x = 0
    · exact Or.inr (hreg x hx h)
    · exact Or.inl h
  obtain ⟨ε,hε,hεsub⟩ := (hK.image hJ).exists_thickening_subset_open regularZeroJets_open hsub
  refine ⟨ε,hε,?_⟩
  intro g hv hd x hx hgx
  have hdist : dist (g x,fderiv ℝ g x) (J x) < ε := by
    rw [Prod.dist_eq]
    exact max_lt (by simpa only [J,dist_eq_norm] using hv x hx)
      (by simpa only [J,dist_eq_norm] using hd x hx)
  have hm : (g x,fderiv ℝ g x) ∈ thickening ε (J '' K) :=
    mem_thickening_iff.mpr ⟨J x,⟨x,hx,rfl⟩,hdist⟩
  rcases hεsub hm with h | h
  · exact False.elim (h hgx)
  · exact h

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
