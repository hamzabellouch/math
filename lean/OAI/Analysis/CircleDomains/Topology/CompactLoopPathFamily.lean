import OAI.Analysis.CircleDomains.Topology.PathLoopErasure
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Mathlib.Topology.MetricSpace.Equicontinuity

namespace OAI

/-! A compact nonempty family of paths, stable under loop deletion.
It keeps the original image, endpoints and every uniform continuity bound. -/
open Set Function Filter Topology Metric
open scoped Topology UniformConvergence unitInterval
noncomputable section
namespace CircleDomainRigidity
variable {X : Type*} [MetricSpace X]

def loopPathFamily (f : C(unitInterval, X)) : Set C(unitInterval, X) :=
  {g | g 0 = f 0 ∧ g 1 = f 1 ∧ range g ⊆ range f ∧
    ∀ ε δ : ℝ, (∀ s t : unitInterval, dist s t ≤ δ → dist (f s) (f t) ≤ ε) →
      ∀ s t : unitInterval, dist s t ≤ δ → dist (g s) (g t) ≤ ε}

lemma mem_loopPathFamily_self (f : C(unitInterval, X)) : f ∈ loopPathFamily f :=
  ⟨rfl, rfl, Subset.rfl, fun _ _ h => h⟩

lemma isClosed_loopPathFamily (f : C(unitInterval, X)) : IsClosed (loopPathFamily f) := by
  have hc : IsClosed {g : C(unitInterval, X) | range g ⊆ range f} := by
    simp only [range_subset_iff]
    simp only [ofPred_forall]
    exact isClosed_iInter fun t => (isCompact_range f.continuous).isClosed.preimage
      (continuous_eval_const t)
  have hm : IsClosed {g : C(unitInterval, X) |
      ∀ ε δ : ℝ, (∀ s t : unitInterval, dist s t ≤ δ → dist (f s) (f t) ≤ ε) →
        ∀ s t : unitInterval, dist s t ≤ δ → dist (g s) (g t) ≤ ε} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun ε => isClosed_iInter fun δ => isClosed_iInter fun _ =>
      isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun _ =>
        isClosed_le ((continuous_eval_const s).dist (continuous_eval_const t)) continuous_const
  exact (isClosed_eq (continuous_eval_const 0) continuous_const).inter
    ((isClosed_eq (continuous_eval_const 1) continuous_const).inter (hc.inter hm))

lemma equicontinuous_loopPathFamily (f : C(unitInterval, X)) :
    Equicontinuous (fun g : loopPathFamily f => ((g : C(unitInterval, X)) : unitInterval → X)) := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) (ε / 2) (by linarith)
  refine ⟨δ / 2, by linarith, ?_⟩
  intro y hy g
  have hh := g.property.2.2.2 (ε / 2) (δ / 2)
    (fun s t hst => (hmod (lt_of_le_of_lt hst (by linarith))).le) x y
    (by simpa only [dist_comm] using hy.le)
  exact hh.trans_lt (by linarith)

lemma isCompact_loopPathFamily [CompleteSpace X] (f : C(unitInterval, X)) : IsCompact (loopPathFamily f) := by
  have hcover : ⋃₀ {K : Set unitInterval | IsCompact K} = univ := by
    exact eq_univ_of_forall fun z => mem_sUnion.mpr ⟨{z}, isCompact_singleton, mem_singleton z⟩
  let : T2Space (unitInterval →ᵤ[{K : Set unitInterval | IsCompact K}] X) :=
    UniformOnFun.t2Space_of_covering hcover
  have he : IsClosedEmbedding
      (UniformOnFun.ofFun {K : Set unitInterval | IsCompact K} ∘
        (fun g : C(unitInterval, X) => (g : unitInterval → X))) :=
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
  have hc := ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (fun K hK => hK) he (fun K _ => (equicontinuous_loopPathFamily f).equicontinuousOn K)
    (fun _ _ z _ => ⟨range f, isCompact_range f.continuous, fun g hg =>
      hg.2.2.1 (mem_range_self z)⟩)
  rwa [(isClosed_loopPathFamily f).closure_eq] at hc

lemma erasePathLoop_mem (f g : C(unitInterval, X)) (hg : g ∈ loopPathFamily f)
    {a b : unitInterval} (hab : a ≤ b) (heq : g a = g b) :
    erasePathLoop g a b hab heq ∈ loopPathFamily f := by
  refine ⟨(erasePathLoop_of_le g hab heq bot_le).trans hg.1,
    (erasePathLoop_of_ge g hab heq le_top).trans hg.2.1, ?_, ?_⟩
  · rintro z ⟨t, rfl⟩
    by_cases ht : t ≤ b
    · change (Iic b).piecewise (fun t => g (min t a)) g t ∈ range f
      simpa only [Set.piecewise, mem_Iic, ht, ↓reduceIte] using hg.2.2.1 (mem_range_self (min t a))
    · change (Iic b).piecewise (fun t => g (min t a)) g t ∈ range f
      simpa only [Set.piecewise, mem_Iic, ht, ↓reduceIte] using hg.2.2.1 (mem_range_self t)
  · intro ε δ hmod s t hst
    have hε : 0 ≤ ε := by
      have hh := hmod s s
      by_cases hδ : 0 ≤ δ
      · simpa using hh (by simpa using hδ)
      · exact False.elim (hδ (dist_nonneg.trans hst))
    wlog horder : s ≤ t generalizing s t
    · simpa only [dist_comm] using this t s (by simpa only [dist_comm] using hst) (le_of_not_ge horder)
    rcases erasePathLoop_pair g hab heq horder with hsame | ⟨u, hu, v, hv, hsu, htv⟩
    · simpa only [hsame, dist_self] using hε
    · rw [hsu, htv]
      exact hg.2.2.2 ε δ hmod u v ((unitInterval_dist_le_of_mem_Icc hu hv).trans hst)

end CircleDomainRigidity

end

end OAI
