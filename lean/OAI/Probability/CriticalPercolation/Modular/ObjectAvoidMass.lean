import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.ClusterObject
import OAI.Probability.CriticalPercolation.GraphGeometry.ObjectKernel
import OAI.Probability.CriticalPercolation.ProductMeasure.Associated
import OAI.Probability.CriticalPercolation.ProductMeasure.AvgDiv

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

noncomputable def objectAvoidMass (w : E → Prop → ℝ) (A B : Set V)
    (C : ClusterObject V E) : ℝ :=
  if Disjoint C.1 B then distribution w (fun ω => G.clusterObject ω A) C else 0

noncomputable def objectAvoidTotal (w : E → Prop → ℝ) (A B : Set V) : ℝ :=
  expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then 1 else 0)

lemma avg_objectAvoidMass (w : E → Prop → ℝ) (A B : Set V)
    (f : ClusterObject V E → ℝ) :
    avg (G.objectAvoidMass w A B) f =
      expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then f (G.clusterObject ω A) else 0) := by
  rw [expect_comp w (fun ω => G.clusterObject ω A)
    (fun C => if Disjoint C.1 B then f C else 0)]
  apply Finset.sum_congr rfl
  intro C _
  simp only [objectAvoidMass]
  split_ifs <;> simp

omit [Fintype V] in
lemma objectAvoidMass_nonneg (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    (A B : Set V) (C : ClusterObject V E) : 0 ≤ G.objectAvoidMass w A B C := by
  unfold objectAvoidMass
  split_ifs
  · exact distribution_nonneg hp _ _
  · exact le_rfl

lemma sum_objectAvoidMass (w : E → Prop → ℝ) (A B : Set V) :
    ∑ C, G.objectAvoidMass w A B C = G.objectAvoidTotal w A B := by
  simpa only [avg, mul_one, objectAvoidTotal] using
    G.avg_objectAvoidMass w A B (fun _ => 1)

omit [Fintype V] in
lemma objectAvoidTotal_symm (w : E → Prop → ℝ) (A B : Set V) :
    G.objectAvoidTotal w A B = G.objectAvoidTotal w B A := by
  unfold objectAvoidTotal
  congr 1
  funext ω
  rw [show Disjoint (G.clusterObject ω A).1 B ↔ Disjoint (G.clusterObject ω B).1 A from
    G.roots_disjoint_symm ω A B]

omit [Fintype V] in
lemma objectAvoidTotal_le_one (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hp : ∀ e b, 0 ≤ w e b) (A B : Set V) : G.objectAvoidTotal w A B ≤ 1 := by
  rw [← expect_const w hw 1]
  apply expect_mono hp
  intro ω
  split_ifs <;> norm_num

omit [Fintype V] in
lemma objectAvoidTotal_minorization (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    {A B : Set V} (hAB : Disjoint A B) :
    density w (fun _ => False) ≤ G.objectAvoidTotal w A B := by
  have h := Finset.single_le_sum (f := fun ω : E → Prop => density w ω *
    (if Disjoint (G.clusterObject ω A).1 B then 1 else 0))
    (s := Finset.univ) (a := fun _ => False)
    (fun ω _ => mul_nonneg (density_nonneg hp ω) (by split_ifs <;> norm_num)) (Finset.mem_univ _)
  simpa only [objectAvoidTotal, expect,
    show (fun _ : E => False) = (∅ : Set E) from rfl,
    G.clusterObject_empty, ite_eq_left hAB, mul_one] using h

lemma objectAvoidMass_halfstationary (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (A B : Set V) (f : ClusterObject V E → ℝ) :
    avg (G.objectAvoidMass w A B) (step (G.objectKernel w B) f) =
      avg (G.objectAvoidMass w B A) f := by
  rw [G.avg_objectAvoidMass, G.avg_objectAvoidMass]
  simp only [G.step_objectKernel]
  have he := G.clusterObject_avoidance_exposure w hw A B (fun _ D => f D)
  refine he.symm.trans ?_
  congr 1
  funext ω
  rw [show Disjoint (G.clusterObject ω A).1 B ↔ Disjoint (G.clusterObject ω B).1 A from
    G.roots_disjoint_symm ω A B]

noncomputable def objectAvoidLaw (w : E → Prop → ℝ) (A B : Set V)
    (C : ClusterObject V E) : ℝ := G.objectAvoidMass w A B C/G.objectAvoidTotal w A B

lemma objectAvoidLaw_stationary (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (A B : Set V) (D : ClusterObject V E) :
    ∑ C, G.objectAvoidLaw w A B C *
      compose (G.objectKernel w B) (G.objectKernel w A) C D = G.objectAvoidLaw w A B D := by
  apply stationary_of_avg
  intro f
  change avg (fun C => G.objectAvoidMass w A B C/G.objectAvoidTotal w A B)
    (step (compose (G.objectKernel w B) (G.objectKernel w A)) f) = _
  rw [avg_div, step_compose, G.objectAvoidMass_halfstationary w hw,
    G.objectAvoidMass_halfstationary w hw]
  exact (avg_div _ _ _).symm

theorem objectAvoidLaw_associated (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hp : ∀ e b, 0 ≤ w e b)
    (hc : ∀ e, 0 < w e False) {A B : Set V} (hAB : Disjoint A B) :
    Associated (G.objectAvoidLaw w A B) := by
  let a := density w (fun _ => False)
  have ha : 0 < a := Finset.prod_pos fun e _ => hc e
  have hZ := G.objectAvoidTotal_minorization w hp hAB
  have hZp : 0 < G.objectAvoidTotal w A B := ha.trans_le hZ
  have ha1 : a ≤ 1 := hZ.trans (G.objectAvoidTotal_le_one w hw hp A B)
  apply stationary_associated
    (compose_nonneg (G.objectKernel_nonneg w hp B) (G.objectKernel_nonneg w hp A))
    (compose_mass (G.objectKernel_mass w hw B) (G.objectKernel_mass w hw A))
    (compose_associated (G.objectKernel_nonneg w hp B) (G.objectKernel_associated w hw hp B)
      (G.objectKernel_associated w hw hp A) (G.objectKernel_antitone w hp A))
    (fun _ hf => compose_monotone (G.objectKernel_antitone w hp B)
      (G.objectKernel_antitone w hp A) hf)
    ha ha1
    (compose_minorization (G.objectKernel_nonneg w hp B) (G.objectKernel_mass w hw B)
      (G.objectKernel_minorization w hp A))
    (G.objectAvoidLaw w A B)
  · intro C
    exact div_nonneg (G.objectAvoidMass_nonneg w hp A B C) hZp.le
  · simp only [objectAvoidLaw, ← Finset.sum_div, G.sum_objectAvoidMass, div_self hZp.ne']
  · exact G.objectAvoidLaw_stationary w hw A B

lemma avg_objectAvoidLaw (w : E → Prop → ℝ) (A B : Set V) (f : ClusterObject V E → ℝ) :
    avg (G.objectAvoidLaw w A B) f =
      (expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then f (G.clusterObject ω A) else 0)) /
      G.objectAvoidTotal w A B := by
  change avg (fun C => G.objectAvoidMass w A B C/G.objectAvoidTotal w A B) f = _
  rw [avg_div, G.avg_objectAvoidMass]

theorem clusterObject_avoidance_cross (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hp : ∀ e b, 0 ≤ w e b)
    (hc : ∀ e, 0 < w e False) {A B : Set V} (hAB : Disjoint A B)
    (f g : ClusterObject V E → ℝ) (hf : Monotone f) (hg : Monotone g) :
    (expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then
      f (G.clusterObject ω A) * g (G.clusterObject ω B) else 0))/G.objectAvoidTotal w A B ≤
    ((expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then f (G.clusterObject ω A) else 0))/
      G.objectAvoidTotal w A B) *
    ((expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then g (G.clusterObject ω B) else 0))/
      G.objectAvoidTotal w A B) := by
  have hassoc := G.objectAvoidLaw_associated w hw hp hc hAB
  have hh := hassoc.cross f (step (G.objectKernel w B) g) hf
    (G.objectKernel_antitone w hp B g hg)
  rw [G.avg_objectAvoidLaw, G.avg_objectAvoidLaw, G.avg_objectAvoidLaw] at hh
  simp only [G.step_objectKernel] at hh
  have hj := G.clusterObject_avoidance_exposure w hw A B (fun C D => f C*g D)
  have hm := G.clusterObject_avoidance_exposure w hw A B (fun _ D => g D)
  simp only [expect_const_mul] at hj
  exact hj.symm ▸ hm.symm ▸ hh

end CriticalPercolation.BondGraph

end
end

end OAI
