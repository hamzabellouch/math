import OAI.Geometry.SurfaceImmersion.Correction.InitialSmoothTail
import OAI.Geometry.SurfaceImmersion.Geometry.ResolvedPrefixAppend
import OAI.Geometry.SurfaceImmersion.Geometry.OrderedNodeIntervals

namespace OAI

/-! Finite induction assembles the actual ordered bridges and unchanged
regular segments, preserving embeddedness and the initial endpoint. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {n : ℕ} {O : Set M}

theorem smooth_ordered_prefix (hγ : FiniteRegularPath planeModel γ)
    (hi : Function.Injective γ) (T : Fin (n+1) → ℝ) (hT : StrictMono T)
    (hTi : ∀ i, T i ∈ Ioo (0:ℝ) 1)
    (B : ∀ i, LocalCornerBridge γ (T i) O)
    (horder : ∀ i j, i < j → (B i).right < (B j).left)
    (hsep : ∀ i, ∀ s ∈ Icc (B i).arc.start (B i).arc.finish,
      ∀ u ∈ Ico (0:ℝ) (B i).left ∪ Ioc (B i).right 1,
        (B i).arc.curve s ≠ γ.extend u)
    (hdis : Pairwise (fun i j => Disjoint
      ((B i).arc.curve '' Icc (B i).arc.start (B i).arc.finish)
      ((B j).arc.curve '' Icc (B j).arc.start (B j).arc.finish)))
    (hreg : ∀ t ∈ Ioo (0:ℝ) 1, t ∉ range T →
      ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t)) :
    ∀ j : Fin (n+1), ∃ P : SmoothArcTail γ.extend (B j).right,
      P.arc.curve P.arc.start = p ∧
      P.arc.curve '' Icc P.arc.start P.arc.finish ⊆
        resolvedPrefixImage γ B {i | i ≤ j} (B j).right := by
  intro j
  induction j using Fin.induction with
  | zero =>
    have hpre : ∀ t ∈ Ioo (0:ℝ) (T 0),
        ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
        Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t) := by
      intro t ht
      exact hreg t ⟨ht.1,ht.2.trans (hTi 0).2⟩ (not_mem_range_before_first T hT ht.2)
    obtain ⟨P,hPs,hPi⟩ := initial_smooth_tail_until hγ hi (B 0).left_pos (B 0).left_lt (hTi 0).2.le hpre
    have hp : P.arc.curve '' Icc P.arc.start P.arc.finish ⊆
        resolvedPrefixImage γ B ∅ (B 0).left := by
      intro x hx
      exact Or.inl (hPi ▸ hx)
    obtain ⟨R,hRi,hRs⟩ := append_resolved_bridge B (notMem_empty 0) hsep hdis P hp
    have hJ : insert (0 : Fin (n+1)) (∅ : Set (Fin (n+1))) = {i | i ≤ 0} := by
      ext i
      simp
    refine ⟨R,hRs.trans hPs,?_⟩
    simpa only [hJ] using hRi
  | succ i ih =>
    obtain ⟨P,hPs,hPi⟩ := ih
    have hik : i.castSucc < i.succ := Fin.castSucc_lt_succ
    have hgap := horder i.castSucc i.succ hik
    have hbetween : ∀ t ∈ Ioo (T i.castSucc) (T i.succ),
        ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
        Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t) := by
      intro t ht
      exact hreg t ⟨(hTi i.castSucc).1.trans ht.1,ht.2.trans (hTi i.succ).2⟩
        (not_mem_range_between_successive T hT (by rfl) ht.1 ht.2)
    obtain ⟨Q,hQs,hQf,hQc⟩ := original_regular_segment hi isOpen_Ioo
      (fun _ ht => ⟨(hTi i.castSucc).1.trans ht.1,ht.2.trans (hTi i.succ).2⟩)
      hbetween hgap (fun u hu =>
        ⟨(B i.castSucc).lt_right.trans_le hu.1,hu.2.trans_lt (B i.succ).left_lt⟩)
    have hJ : ∀ k ∈ {k : Fin (n+1) | k ≤ i.castSucc}, (B k).right ≤ (B i.castSucc).right := by
      intro k hk
      change k ≤ i.castSucc at hk
      rcases lt_or_eq_of_le hk with hk | rfl
      · exact (horder k i.castSucc hk).le.trans ((B i.castSucc).left_lt.trans (B i.castSucc).lt_right).le
      · exact le_rfl
    obtain ⟨P',hP'i,hP's⟩ := append_resolved_segment B hi (B i.castSucc).rightPoint.property.1
      hgap (B i.succ).leftPoint.property.2 hJ hsep P hPi Q hQs hQf hQc
    have hk : i.succ ∉ {k : Fin (n+1) | k ≤ i.castSucc} := by
      change ¬ i.succ ≤ i.castSucc
      exact not_le_of_gt Fin.castSucc_lt_succ
    obtain ⟨R,hRi,hRs⟩ := append_resolved_bridge B hk hsep hdis P' hP'i
    have hJ' : insert i.succ {k : Fin (n+1) | k ≤ i.castSucc} = {k | k ≤ i.succ} := by
      ext k
      simp only [mem_insert_iff,mem_ofPred_eq,Fin.le_castSucc_iff]
      exact le_iff_eq_or_lt.symm
    refine ⟨R,hRs.trans (hP's.trans hPs),?_⟩
    simpa only [hJ'] using hRi

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
