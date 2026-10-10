import OAI.Analysis.BernoulliCone.ClosedGermExtension

namespace OAI

universe uE uG

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold
namespace Bernoulli.LocalExtension
variable {E : Type uE} {G : Type uG} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
lemma exists_cutoff {K D:Set E} (hK:IsCompact K) (hD:IsOpen D) (hKD:K⊆D) :
    ∃φ:E→ℝ,ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ⊆D ∧
      (∀ᶠ x in 𝓝ˢ K,φ x=1) := by
  obtain ⟨δ,hδ,hδD⟩:=hK.exists_thickening_subset_open hD hKD
  have hki:K⊆interior (Metric.cthickening (δ/2) K):=
    (Metric.self_subset_thickening (half_pos hδ) _).trans
      (Metric.thickening_subset_interior_cthickening _ _)
  obtain ⟨φ,hφ1,hφ0,hφb⟩:=exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,E)) (n:=⊤) hK.isClosed hki
  refine ⟨φ,φ.contMDiff.contDiff,HasCompactSupport.intro hK.cthickening hφ0,?_,hφ1⟩
  have hs:tsupport (φ:E→ℝ)⊆Metric.cthickening (δ/2) K:=by
    apply closure_minimal _ Metric.isClosed_cthickening
    intro x hx
    by_contra hn
    exact hx (hφ0 x hn)
  exact hs.trans ((Metric.cthickening_subset_thickening' hδ (by linarith) _).trans hδD)

/-- A compact part of a genuinely smooth open domain admits a global smooth
representative. This permits use of global calculus only after verifying the
actual local hypotheses. -/
lemma exists_contDiff_extension {n:ℕ∞} {F:E→G} {K D:Set E}
    (hK:IsCompact K) (hD:IsOpen D) (hKD:K⊆D) (hF:ContDiffOn ℝ n F D) :
    ∃B:E→G,ContDiff ℝ n B ∧ B =ᶠ[𝓝ˢ K] F := by
  obtain ⟨φ,hφ,hφc,hφD,hφ1⟩:=exists_cutoff hK hD hKD
  refine ⟨fun x=>φ x • F x,?_,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx:x∈D
    · exact (hφ.of_le (m:=n) (by exact_mod_cast (le_top : n≤⊤))).contDiffAt.smul (hF.contDiffAt (hD.mem_nhds hx))
    · have hxt:x∉tsupport φ:=fun h=>hx (hφD h)
      apply (contDiffAt_const (c:=(0:G))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxt] with y hy
      simp [hy]
  · filter_upwards [hφ1] with x hx
    simp [hx]
end Bernoulli.LocalExtension

end
end

end OAI
