import OAI.Analysis.CircleDomains.Selection.CountableTagAssembly
import OAI.Analysis.CircleDomains.Topology.EmbeddedPathTags
import OAI.Analysis.CircleDomains.Topology.AffineIntervalImages

namespace OAI

/-! A continuous path assembled from countably many open pieces receives
the transported tags of each piece. Disjointness prevents interference. -/

open Set Function
open scoped Classical

noncomputable section

namespace CircleDomainRigidity

variable {ι X : Type*} [Encodable ι] [MetricSpace X]

def concatenatedTaggedPath (γ : C(PathTime, X)) (a b : ι → PathTime)
    (Γ : ι → TaggedPath X) : TaggedPath X :=
  (γ, assembleTags (fun i k => embeddedTag (a i) (b i) ((Γ i).2 k)))

theorem tagRules_concatenated (H : ℕ → Set (UnitAddCircle × X))
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (γ : C(PathTime, X)) (a b : ι → PathTime) (hab : ∀ i, a i < b i)
    (Γ : ι → TaggedPath X)
    (hmatch : ∀ i t, t ∈ Ioo (⊥ : PathTime) ⊤ →
      γ (affinePathTime (a i) (b i) t) = (Γ i).1 t)
    (hΓ : ∀ i, TagRules H N (Γ i)) :
    TagRules H N (concatenatedTaggedPath γ a b Γ) := by
  apply tagRules_assemble
  intro i k
  exact embeddedTag_rules H N (hab i) (Γ i).1 γ (hmatch i) ((Γ i).2 k)
    (hΓ i k).1 (hΓ i k).2.1 (hΓ i k).2.2

theorem residualTimes_embedded_piece (B : Set X)
    (γ : C(PathTime, X)) {a b : PathTime} (hab : a < b) (Γ : TaggedPath X)
    (hmatch : ∀ t ∈ Ioo (⊥ : PathTime) ⊤, γ (affinePathTime a b t) = Γ.1 t)
    {t : PathTime} (ht : t ∈ Ioo a b) :
    t ∈ residualTimes B (γ, fun k => embeddedTag a b (Γ.2 k)) ↔
      rescalePathTime a b t ∈ residualTimes B Γ := by
  have hti := rescalePathTime_mem_Ioo hab ht
  have he := affine_rescalePathTime hab ⟨ht.1.le, ht.2.le⟩
  have hv : γ t = Γ.1 (rescalePathTime a b t) := by simpa only [he] using hmatch _ hti
  constructor
  · rintro ⟨hdust, htags⟩
    refine ⟨hv ▸ hdust, fun k => ?_⟩
    by_contra h
    push Not at h
    have himage : t ∈ Ioo (tagLeft (embeddedTag a b (Γ.2 k)))
        (tagRight (embeddedTag a b (Γ.2 k))) := by
      rw [embeddedTag_interval hab]
      exact ⟨rescalePathTime a b t, h, he⟩
    exact (htags k).elim (not_le_of_gt himage.1) (not_le_of_gt himage.2)
  · rintro ⟨hdust, htags⟩
    refine ⟨hv.symm ▸ hdust, fun k => ?_⟩
    by_contra h
    push Not at h
    have himage : t ∈ affinePathTime a b '' Ioo (tagLeft (Γ.2 k)) (tagRight (Γ.2 k)) := by
      rwa [← embeddedTag_interval hab]
    obtain ⟨s, hs, hsval⟩ := himage
    have hst : s = rescalePathTime a b t := (affinePathTime_strictMono hab).injective
      (hsval.trans he.symm)
    subst s
    exact (htags k).elim (not_le_of_gt hs.1) (not_le_of_gt hs.2)

theorem residualTimes_concatenated_piece (B : Set X)
    (γ : C(PathTime, X)) (a b : ι → PathTime) (hab : ∀ i, a i < b i)
    (hdis : Pairwise (Disjoint on (fun i => Ioo (a i) (b i))))
    (Γ : ι → TaggedPath X)
    (hmatch : ∀ i t, t ∈ Ioo (⊥ : PathTime) ⊤ →
      γ (affinePathTime (a i) (b i) t) = (Γ i).1 t)
    (i : ι) {t : PathTime} (ht : t ∈ Ioo (a i) (b i)) :
    t ∈ residualTimes B (concatenatedTaggedPath γ a b Γ) ↔
      rescalePathTime (a i) (b i) t ∈ residualTimes B (Γ i) := by
  exact (residualTimes_assemble_on_piece B γ _ (fun i => Ioo (a i) (b i)) hdis
    (fun i k => embeddedTag_interval_subset (hab i) ((Γ i).2 k)) i ht).trans
      (residualTimes_embedded_piece B γ (hab i) (Γ i) (hmatch i) ht)

end CircleDomainRigidity

end

end OAI
