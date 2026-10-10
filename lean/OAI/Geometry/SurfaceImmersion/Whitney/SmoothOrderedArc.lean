import OAI.Geometry.SurfaceImmersion.Correction.SmoothOrderedPrefix
import OAI.Geometry.SurfaceImmersion.Correction.FinishSmoothTail

namespace OAI

/-! Finishing the finite ordered construction gives one smooth embedded
source arc, with the prescribed original endpoints. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {n : ℕ} {O : Set M}

theorem smooth_ordered_arc (hγ : FiniteRegularPath planeModel γ)
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
    ∃ R : SmoothCompactArc planeModel M,
      R.curve R.start = p ∧ R.curve R.finish = q ∧
      R.curve '' Icc R.start R.finish ⊆ range γ ∪
        ⋃ i, (B i).arc.curve '' Icc (B i).arc.start (B i).arc.finish := by
  obtain ⟨P,hPs,hPi⟩ := smooth_ordered_prefix hγ hi T hT hTi B horder hsep hdis hreg (Fin.last n)
  have hJ : ∀ i ∈ {i : Fin (n+1) | i ≤ Fin.last n},
      (B i).right ≤ (B (Fin.last n)).right := by
    intro i hiJ
    change i ≤ Fin.last n at hiJ
    rcases lt_or_eq_of_le hiJ with hiJ | rfl
    · exact (horder i (Fin.last n) hiJ).le.trans
        ((B (Fin.last n)).left_lt.trans (B (Fin.last n)).lt_right).le
    · exact le_rfl
  have hafter : ∀ t ∈ Ioo (T (Fin.last n)) 1,
      ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t) := by
    intro t ht
    exact hreg t ⟨(hTi (Fin.last n)).1.trans ht.1,ht.2⟩
      (not_mem_range_after_last T hT ht.1)
  obtain ⟨R,hRs,hRf,hRi⟩ := finish_smooth_tail hγ hi B
    ((B (Fin.last n)).left_pos.trans (B (Fin.last n)).left_lt |>.trans (B (Fin.last n)).lt_right)
    (B (Fin.last n)).right_lt_one (B (Fin.last n)).lt_right (hTi (Fin.last n)).1.le
    hJ hsep hafter P hPi
  refine ⟨R,hRs.trans hPs,hRf,?_⟩
  intro x hx
  rcases hRi hx with hx | hx
  · obtain ⟨u,hu,rfl⟩ := hx
    exact Or.inl ⟨⟨u,hu⟩,(Path.extend_apply γ hu).symm⟩
  · obtain ⟨i,_,hx⟩ := mem_iUnion₂.mp hx
    exact Or.inr (mem_iUnion.mpr ⟨i,hx⟩)

theorem smooth_regular_path (hγ : FiniteRegularPath planeModel γ) (hi : Function.Injective γ)
    (hreg : ∀ t ∈ Ioo (0:ℝ) 1,
      ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t)) :
    ∃ R : SmoothCompactArc planeModel M,
      R.curve R.start = p ∧ R.curve R.finish = q ∧ R.curve '' Icc R.start R.finish ⊆ range γ := by
  let T : Fin 0 → ℝ := Fin.elim0
  let B : ∀ i : Fin 0, LocalCornerBridge γ (T i) (univ : Set M) := fun i => Fin.elim0 i
  obtain ⟨P,hPs,hPi⟩ := initial_smooth_tail_until hγ hi (d := 1/2) (D := 3/4)
    (by norm_num) (by norm_num) (by norm_num)
    (fun t ht => hreg t ⟨ht.1,by linarith [ht.2]⟩)
  have hPimage : P.arc.curve '' Icc P.arc.start P.arc.finish ⊆ resolvedPrefixImage γ B ∅ (1/2) := by
    intro x hx
    exact Or.inl (hPi ▸ hx)
  obtain ⟨R,hRs,hRf,hRi⟩ := finish_smooth_tail hγ hi B (a := 1/2) (A := 0)
    (by norm_num) (by norm_num) (by norm_num) le_rfl
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) hreg P hPimage
  refine ⟨R,hRs.trans hPs,hRf,?_⟩
  intro x hx
  rcases hRi hx with hx | hx
  · obtain ⟨u,hu,rfl⟩ := hx
    exact ⟨⟨u,hu⟩,(Path.extend_apply γ hu).symm⟩
  · obtain ⟨i,_,_⟩ := mem_iUnion₂.mp hx
    exact Fin.elim0 i

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
