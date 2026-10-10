import OAI.Geometry.SurfaceImmersion.Whitney.CornerBridgeEmbedding

namespace OAI

/-! The concrete trace invariant used while joining the ordered smooth
bridges: old path points plus only the bridges already inserted. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} (γ : Path p q) {T : ι → ℝ} {O : Set M}

def resolvedPrefixImage (B : ∀ i, LocalCornerBridge γ (T i) O) (J : Set ι) (a : ℝ) : Set M :=
  γ.extend '' Icc 0 a ∪ ⋃ i ∈ J, (B i).arc.curve '' Icc (B i).arc.start (B i).arc.finish

variable {γ}

lemma resolvedPrefixImage_mono (B : ∀ i, LocalCornerBridge γ (T i) O)
    {J K : Set ι} (hJK : J ⊆ K) {a b : ℝ} (hab : a ≤ b) :
    resolvedPrefixImage γ B J a ⊆ resolvedPrefixImage γ B K b := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl (image_mono (Icc_subset_Icc_right hab) hx)
  · obtain ⟨i,hi,hx⟩ := mem_iUnion₂.mp hx
    exact Or.inr (mem_iUnion₂.mpr ⟨i,hJK hi,hx⟩)

lemma resolvedPrefixImage_avoids_future (B : ∀ i, LocalCornerBridge γ (T i) O)
    (hi : Function.Injective γ) {J : Set ι} {a : ℝ} (ha : a ≤ 1)
    (hJ : ∀ i ∈ J, (B i).right ≤ a)
    (hsep : ∀ i, ∀ s ∈ Icc (B i).arc.start (B i).arc.finish,
      ∀ u ∈ Ico (0:ℝ) (B i).left ∪ Ioc (B i).right 1,
        (B i).arc.curve s ≠ γ.extend u) :
    ∀ x ∈ resolvedPrefixImage γ B J a, ∀ u ∈ Ioc a 1, x ≠ γ.extend u := by
  intro x hx u hu he
  rcases hx with hx | hx
  · obtain ⟨v,hv,hvx⟩ := hx
    have h := embeddedPath_extend_injOn γ hi ⟨hv.1,hv.2.trans ha⟩
      ⟨hv.1.trans (hv.2.trans hu.1.le),hu.2⟩ (hvx.trans he)
    exact (not_le_of_gt hu.1) (h ▸ hv.2)
  · obtain ⟨i,hiJ,s,hs,hsx⟩ := mem_iUnion₂.mp hx
    exact hsep i s hs u (Or.inr ⟨(hJ i hiJ).trans_lt hu.1,hu.2⟩) (hsx.trans he)

lemma resolvedPrefixImage_avoids_bridge (B : ∀ i, LocalCornerBridge γ (T i) O)
    {J : Set ι} {k : ι} (hk : k ∉ J)
    (hsep : ∀ i, ∀ s ∈ Icc (B i).arc.start (B i).arc.finish,
      ∀ u ∈ Ico (0:ℝ) (B i).left ∪ Ioc (B i).right 1,
        (B i).arc.curve s ≠ γ.extend u)
    (hdis : Pairwise (fun i j => Disjoint
      ((B i).arc.curve '' Icc (B i).arc.start (B i).arc.finish)
      ((B j).arc.curve '' Icc (B j).arc.start (B j).arc.finish))) :
    ∀ x ∈ resolvedPrefixImage γ B J (B k).left,
      ∀ t ∈ Ioc (B k).arc.start (B k).arc.finish, x ≠ (B k).arc.curve t := by
  intro x hx t ht he
  rcases hx with hx | hx
  · obtain ⟨u,hu,hux⟩ := hx
    by_cases hul : u < (B k).left
    · exact hsep k t ⟨ht.1.le,ht.2⟩ u (Or.inl ⟨hu.1,hul⟩) (hux.trans he).symm
    · have hul' : u = (B k).left := le_antisymm hu.2 (le_of_not_gt hul)
      subst u
      have hstart : (B k).arc.curve (B k).arc.start = γ.extend (B k).left :=
        (B k).left_germ.eq_of_nhds.trans (by rw [Function.comp_apply,(B k).left_value])
      have het : (B k).arc.start = t := (B k).arc.injective
        (left_mem_Icc.mpr (B k).arc.start_lt_finish.le) ⟨ht.1.le,ht.2⟩
        (hstart.trans (hux.trans he))
      exact ht.1.ne het
  · obtain ⟨i,hiJ,s,hs,hsx⟩ := mem_iUnion₂.mp hx
    have hik : i ≠ k := fun he => hk (he ▸ hiJ)
    have hxI : x ∈ (B i).arc.curve '' Icc (B i).arc.start (B i).arc.finish := ⟨s,hs,hsx⟩
    have hxK : x ∈ (B k).arc.curve '' Icc (B k).arc.start (B k).arc.finish :=
      ⟨t,⟨ht.1.le,ht.2⟩,he.symm⟩
    exact disjoint_left.mp (hdis hik) hxI hxK

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
