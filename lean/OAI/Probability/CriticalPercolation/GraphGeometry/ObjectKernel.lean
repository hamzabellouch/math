import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.ClusterObject
import OAI.Probability.CriticalPercolation.ProductMeasure.Associated
import OAI.Probability.CriticalPercolation.ProductMeasure.ExpectMulReal

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open ClusterDeletion FiniteProduct FiniteMarkov
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

noncomputable def objectKernel (w : E → Prop → ℝ) (S : Set V)
    (C D : ClusterObject V E) : ℝ :=
  distribution w (fun ω => G.clusterObject (G.eraseVertices ω C.1) S) D

lemma step_objectKernel (w : E → Prop → ℝ) (S : Set V) (f : ClusterObject V E → ℝ)
    (C : ClusterObject V E) :
    step (G.objectKernel w S) f C =
      expect w (fun ω => f (G.clusterObject (G.eraseVertices ω C.1) S)) := by
  exact (expect_comp w _ f).symm

omit [Fintype V] in
lemma objectKernel_nonneg (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    (S : Set V) (C D : ClusterObject V E) : 0 ≤ G.objectKernel w S C D :=
  distribution_nonneg hp _ D

lemma objectKernel_mass (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (C : ClusterObject V E) : ∑ D, G.objectKernel w S C D = 1 :=
  distribution_mass w hw _

lemma objectKernel_antitone (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    (S : Set V) (f : ClusterObject V E → ℝ) (hf : Monotone f) :
    Antitone (step (G.objectKernel w S) f) := by
  intro C D hCD
  simp only [G.step_objectKernel]
  apply expect_mono hp
  intro ω
  exact hf (G.clusterObject_mono (G.eraseVertices_antitone hCD.1 ω) S)

lemma objectKernel_associated (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hp : ∀ e b, 0 ≤ w e b) (S : Set V) (C : ClusterObject V E) :
    Associated (G.objectKernel w S C) := by
  intro f g hf hg
  change step (G.objectKernel w S) f C * step (G.objectKernel w S) g C ≤
    step (G.objectKernel w S) (fun D => f D * g D) C
  simp only [G.step_objectKernel]
  apply expect_mul_ge_real w hw hp
  · intro ω ω' hω
    exact hf (G.clusterObject_mono (G.eraseVertices_mono hω C.1) S)
  · intro ω ω' hω
    exact hg (G.clusterObject_mono (G.eraseVertices_mono hω C.1) S)

omit [Fintype V] [Fintype E] in
lemma clusterObject_empty (S : Set V) : G.clusterObject ∅ S = (S, ∅) := by
  apply Prod.ext
  · change roots (G.openGraph ∅) S = S
    have he : G.openGraph ∅ = ⊥ := by simp [openGraph]
    rw [he]
    ext v
    simp [roots, SimpleGraph.reachable_bot]
  · exact Set.empty_inter _

omit [Fintype V] in
lemma objectKernel_minorization (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    (S : Set V) (C : ClusterObject V E) :
    density w (fun _ => False) ≤ G.objectKernel w S C (S, ∅) := by
  have h := Finset.single_le_sum (f := fun ω : E → Prop =>
    density w ω * (if G.clusterObject (G.eraseVertices ω C.1) S = (S, ∅) then 1 else 0))
    (s := Finset.univ) (a := fun _ => False)
    (fun ω _ => mul_nonneg (density_nonneg hp ω) (by split_ifs <;> norm_num)) (Finset.mem_univ _)
  have he : G.eraseVertices ∅ C.1 = ∅ := Set.empty_sdiff _
  simpa only [objectKernel, distribution, expect, show (fun _ : E => False) = (∅ : Set E) from rfl,
    he, G.clusterObject_empty, ite_eq_left rfl, ite_true, mul_one] using h

end CriticalPercolation.BondGraph

end
end

end OAI
