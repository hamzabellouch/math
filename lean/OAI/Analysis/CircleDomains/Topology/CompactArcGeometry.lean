import OAI.Analysis.CircleDomains.Topology.CompactArcReduction

namespace OAI

/-! Compact simple-arc families approach their common terminal point
uniformly and stay uniformly away from it on every earlier time interval. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric

lemma compact_arcs_uniform_terminal
    (K : Set C(PathTime, Sphere)) (hK : IsCompact K) (b : Sphere)
    (hend : ∀ α ∈ K, α ⊤ = b) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ α ∈ K, ∀ t : PathTime, dist t ⊤ < δ → dist (α t) b < ε := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : K × PathTime → Sphere := fun p => p.1.val p.2
  have hF : Continuous F := continuous_eval.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hF) ε hε
  refine ⟨δ, hδ, fun α hα t ht => ?_⟩
  have hdist : dist ((⟨α, hα⟩ : K), t) ((⟨α, hα⟩ : K), ⊤) < δ := by
    simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using ht
  simpa only [F, hend α hα] using hd hdist

lemma compact_arcs_initial_avoidance
    (K : Set C(PathTime, Sphere)) (hK : IsCompact K) (b : Sphere)
    (hinj : ∀ α ∈ K, Injective α) (hend : ∀ α ∈ K, α ⊤ = b)
    (c : PathTime) (hc : c < ⊤) :
    ∃ δ > 0, ∀ α ∈ K, ∀ t ≤ c, δ ≤ dist (α t) b := by
  let A : Set Sphere := (fun p : C(PathTime, Sphere) × PathTime => p.1 p.2) '' (K ×ˢ Iic c)
  have hA : IsCompact A := (hK.prod isClosed_Iic.isCompact).image continuous_eval
  have hb : b ∉ A := by
    rintro ⟨⟨α, t⟩, ⟨hα, ht⟩, he⟩
    have he' : t = ⊤ := hinj α hα (he.trans (hend α hα).symm)
    exact (not_le_of_gt hc) (he' ▸ ht)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hA.isClosed.isOpen_compl b hb
  refine ⟨δ, hδ, fun α hα t ht => ?_⟩
  by_contra! hn
  have hm : α t ∈ A := ⟨(α, t), ⟨hα, ht⟩, rfl⟩
  exact hball (show α t ∈ ball b δ from hn) hm

end CircleDomainRigidity

end

end OAI
