import OAI.Geometry.SurfaceImmersion.Geometry.ResolvedPrefixImage
import OAI.Geometry.SurfaceImmersion.Whitney.SmoothArcTail

namespace OAI

/-! The two actual induction steps: add a prepared bridge, or add the
unchanged regular segment before the next bridge. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {T : ι → ℝ} {O : Set M}

 theorem append_resolved_bridge (B : ∀ i, LocalCornerBridge γ (T i) O)
    {J : Set ι} {k : ι} (hk : k ∉ J)
    (hsep : ∀ i, ∀ s ∈ Icc (B i).arc.start (B i).arc.finish,
      ∀ u ∈ Ico (0:ℝ) (B i).left ∪ Ioc (B i).right 1,
        (B i).arc.curve s ≠ γ.extend u)
    (hdis : Pairwise (fun i j => Disjoint
      ((B i).arc.curve '' Icc (B i).arc.start (B i).arc.finish)
      ((B j).arc.curve '' Icc (B j).arc.start (B j).arc.finish)))
    (P : SmoothArcTail γ.extend (B k).left)
    (hP : P.arc.curve '' Icc P.arc.start P.arc.finish ⊆ resolvedPrefixImage γ B J (B k).left) :
    ∃ R : SmoothArcTail γ.extend (B k).right,
      R.arc.curve '' Icc R.arc.start R.arc.finish ⊆ resolvedPrefixImage γ B (insert k J) (B k).right ∧
      R.arc.curve R.arc.start = P.arc.curve P.arc.start := by
  have hcross : ∀ s ∈ Icc P.arc.start P.arc.finish,
      ∀ t ∈ Ioc (B k).arc.start (B k).arc.finish, P.arc.curve s ≠ (B k).arc.curve t := by
    intro s hs t ht
    exact resolvedPrefixImage_avoids_bridge B hk hsep hdis _
      (hP (mem_image_of_mem P.arc.curve hs)) t ht
  obtain ⟨R,hRi,hRs,_⟩ := P.append (B k).arc (B k).leftParameter (B k).rightParameter
    (B k).left_smooth (B k).right_smooth (B k).left_forward (B k).right_forward
    (B k).left_value (B k).right_value (B k).left_germ (B k).right_germ hcross
  refine ⟨R,?_,hRs⟩
  rw [hRi]
  apply union_subset
  · exact hP.trans (resolvedPrefixImage_mono B (subset_insert k J) ((B k).left_lt.trans (B k).lt_right).le)
  · intro x hx
    exact Or.inr (mem_iUnion₂.mpr ⟨k,mem_insert k J,hx⟩)

theorem append_resolved_segment (B : ∀ i, LocalCornerBridge γ (T i) O)
    (hi : Function.Injective γ) {J : Set ι} {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hJ : ∀ i ∈ J, (B i).right ≤ a)
    (hsep : ∀ i, ∀ s ∈ Icc (B i).arc.start (B i).arc.finish,
      ∀ u ∈ Ico (0:ℝ) (B i).left ∪ Ioc (B i).right 1,
        (B i).arc.curve s ≠ γ.extend u)
    (P : SmoothArcTail γ.extend a)
    (hP : P.arc.curve '' Icc P.arc.start P.arc.finish ⊆ resolvedPrefixImage γ B J a)
    (Q : SmoothCompactArc planeModel M) (hQs : Q.start = a) (hQf : Q.finish = b)
    (hQc : Q.curve = γ.extend) :
    ∃ R : SmoothArcTail γ.extend b,
      R.arc.curve '' Icc R.arc.start R.arc.finish ⊆ resolvedPrefixImage γ B J b ∧
      R.arc.curve R.arc.start = P.arc.curve P.arc.start := by
  have hcross : ∀ s ∈ Icc P.arc.start P.arc.finish, ∀ t ∈ Ioc Q.start Q.finish,
      P.arc.curve s ≠ Q.curve t := by
    intro s hs t ht
    rw [hQs,hQf] at ht
    rw [hQc]
    exact resolvedPrefixImage_avoids_future B hi (hab.le.trans hb) hJ hsep _
      (hP (mem_image_of_mem P.arc.curve hs)) t ⟨ht.1,ht.2.trans hb⟩
  have hgL : Q.curve =ᶠ[𝓝 Q.start] γ.extend ∘ id := by rw [hQc]; rfl
  have hgR : Q.curve =ᶠ[𝓝 Q.finish] γ.extend ∘ id := by rw [hQc]; rfl
  obtain ⟨R,hRi,hRs,_⟩ := P.append Q id id contDiff_id contDiff_id
    (by simp) (by simp) hQs hQf hgL hgR hcross
  refine ⟨R,?_,hRs⟩
  rw [hRi]
  apply union_subset
  · exact hP.trans (resolvedPrefixImage_mono B (Subset.refl _) hab.le)
  · intro x hx
    rw [hQc,hQs,hQf] at hx
    exact Or.inl (image_mono (Icc_subset_Icc ha le_rfl) hx)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
