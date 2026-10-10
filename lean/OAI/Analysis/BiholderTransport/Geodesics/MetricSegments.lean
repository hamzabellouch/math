import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

namespace WeakMTWTransport
variable {M : Type*} [MetricSpace M]

def IsMetricChain (x y : M) (A : Set (ℝ × M)) : Prop :=
  (0,x) ∈ A ∧ (dist x y,y) ∈ A ∧
  A ⊆ Icc 0 (dist x y) ×ˢ univ ∧
  ∀ u ∈ A, ∀ v ∈ A, dist u.2 v.2 = |u.1-v.1|

lemma isMetricChain_initial (x y : M) :
    IsMetricChain x y {(0,x),(dist x y,y)} := by
  refine ⟨by simp,by simp,?_,?_⟩
  · intro u hu
    rcases hu with hu|hu
    · subst u; exact ⟨⟨le_rfl,dist_nonneg⟩,mem_univ _⟩
    · rcases hu with rfl
      exact ⟨⟨dist_nonneg,le_rfl⟩,mem_univ _⟩
  · intro u hu v hv
    rcases hu with rfl|hu <;> rcases hv with rfl|hv
    · simp
    · rcases hv with rfl
      simp [abs_of_nonneg dist_nonneg]
    · rcases hu with rfl
      simp [dist_comm,abs_of_nonneg dist_nonneg]
    · rcases hu with rfl; rcases hv with rfl
      simp

lemma IsMetricChain.closure {x y : M} {A : Set (ℝ × M)}
    (hA : IsMetricChain x y A) : IsMetricChain x y (closure A) := by
  refine ⟨subset_closure hA.1,subset_closure hA.2.1,
    closure_minimal hA.2.2.1 (isClosed_Icc.prod isClosed_univ),?_⟩
  intro u hu v hv
  have hvA (w : ℝ × M) (hw : w ∈ A) : dist w.2 v.2 = |w.1-v.1| := by
    have hc : IsClosed {v : ℝ × M | dist w.2 v.2 = |w.1-v.1|} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    exact closure_minimal (fun z hz => hA.2.2.2 w hw z hz) hc hv
  have hc : IsClosed {u : ℝ × M | dist u.2 v.2 = |u.1-v.1|} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  exact closure_minimal hvA hc hu

lemma exists_maximal_metricChain (x y : M) :
    ∃ A : Set (ℝ × M), Maximal (IsMetricChain x y) A := by
  let S : Set (Set (ℝ × M)) := {A | IsMetricChain x y A}
  have hchains : ∀ c ⊆ S, IsChain (fun a b => a ⊆ b) c → c.Nonempty →
      ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hchain hne
    obtain ⟨B,hB⟩ := hne
    refine ⟨⋃₀ c,?_,fun s hs => subset_sUnion_of_mem hs⟩
    refine ⟨mem_sUnion.mpr ⟨B,hB,(hc hB).1⟩,
      mem_sUnion.mpr ⟨B,hB,(hc hB).2.1⟩,?_,?_⟩
    · intro u hu
      obtain ⟨C,hC,huC⟩ := mem_sUnion.mp hu
      exact (hc hC).2.2.1 huC
    · intro u hu v hv
      obtain ⟨C,hC,huC⟩ := mem_sUnion.mp hu
      obtain ⟨D,hD,hvD⟩ := mem_sUnion.mp hv
      obtain ⟨F,hF,hCF,hDF⟩ := hchain.directedOn C hC D hD
      exact (hc hF).2.2.2 u (hCF huC) v (hDF hvD)
  obtain ⟨A,_,hA⟩ := zorn_subset_nonempty S hchains
    {(0,x),(dist x y,y)} (isMetricChain_initial x y)
  exact ⟨A,hA⟩

lemma insert_midpoint_metricChain {x y : M} {A : Set (ℝ × M)}
    (hA : IsMetricChain x y A) {u v : ℝ × M} (hu : u ∈ A) (hv : v ∈ A)
    (huv : u.1 < v.1)
    (hgap : ∀ w ∈ A, w.1 ≤ u.1 ∨ v.1 ≤ w.1) {z : M}
    (huz : dist u.2 z = dist u.2 v.2/2)
    (hzv : dist z v.2 = dist u.2 v.2/2) :
    IsMetricChain x y (insert ((u.1+v.1)/2,z) A) := by
  let m : ℝ := (u.1+v.1)/2
  have hadist : dist u.2 v.2 = v.1-u.1 := by
    rw [hA.2.2.2 u hu v hv,abs_of_neg (sub_neg.mpr huv)]
    ring
  rw [hadist] at huz hzv
  have hwm (w : ℝ × M) (hw : w ∈ A) : dist w.2 z = |w.1-m| := by
    have hwu := hA.2.2.2 w hw u hu
    have hwv := hA.2.2.2 w hw v hv
    rcases hgap w hw with hleft|hright
    · have habs1 : |w.1-u.1| = u.1-w.1 := by rw [abs_of_nonpos (sub_nonpos.mpr hleft)]; ring
      have habs2 : |w.1-v.1| = v.1-w.1 := by rw [abs_of_nonpos (by linarith)]; ring
      rw [habs1] at hwu
      rw [habs2] at hwv
      have hwmle : w.1 ≤ m := by dsimp [m]; linarith
      rw [abs_of_nonpos (sub_nonpos.mpr hwmle)]
      have hubound := dist_triangle w.2 u.2 z
      have hlbound := dist_triangle w.2 z v.2
      dsimp [m]
      linarith
    · have habs1 : |w.1-u.1| = w.1-u.1 := abs_of_nonneg (by linarith)
      have habs2 : |w.1-v.1| = w.1-v.1 := abs_of_nonneg (sub_nonneg.mpr hright)
      rw [habs1] at hwu
      rw [habs2] at hwv
      have hwmle : m ≤ w.1 := by dsimp [m]; linarith
      rw [abs_of_nonneg (sub_nonneg.mpr hwmle)]
      have hubound := dist_triangle w.2 v.2 z
      have hlbound := dist_triangle w.2 z u.2
      rw [dist_comm v.2 z] at hubound
      rw [dist_comm z u.2] at hlbound
      dsimp [m]
      linarith
  refine ⟨mem_insert_of_mem _ hA.1,mem_insert_of_mem _ hA.2.1,?_,?_⟩
  · intro w hw
    rcases hw with rfl|hw
    · have hux := (hA.2.2.1 hu).1
      have hvx := (hA.2.2.1 hv).1
      exact ⟨⟨by dsimp; linarith [hux.1,hvx.1],by dsimp; linarith [hux.2,hvx.2]⟩,mem_univ _⟩
    · exact hA.2.2.1 hw
  · intro w hw q hq
    rcases hw with rfl|hw <;> rcases hq with rfl|hq
    · simp
    · simpa only [dist_comm z q.2,abs_sub_comm] using hwm q hq
    · exact hwm w hw
    · exact hA.2.2.2 w hw q hq

lemma maximal_metricChain_full_projection [CompactSpace M] (x y : M)
    (hmid : ∀ u v : M, ∃ z, dist u z = dist u v/2 ∧ dist z v = dist u v/2)
    {A : Set (ℝ × M)} (hA : Maximal (IsMetricChain x y) A) :
    Prod.fst '' A = Icc 0 (dist x y) := by
  have hAc : IsClosed A := by
    have heq : closure A = A := subset_antisymm (hA.2 hA.1.closure subset_closure) subset_closure
    rw [← heq]
    exact isClosed_closure
  have hAk : IsCompact A := (isCompact_Icc.prod isCompact_univ).of_isClosed_subset hAc hA.1.2.2.1
  let K : Set ℝ := Prod.fst '' A
  have hK : IsCompact K := hAk.image continuous_fst
  apply Subset.antisymm
  · rintro t ⟨w,hw,rfl⟩
    exact (hA.1.2.2.1 hw).1
  · intro t ht
    by_contra htn
    have hK0 : 0 ∈ K := ⟨(0,x),hA.1.1,rfl⟩
    have hKL : dist x y ∈ K := ⟨(dist x y,y),hA.1.2.1,rfl⟩
    obtain ⟨a,ha,hamax⟩ := (hK.inter_right isClosed_Iic).exists_isMaxOn
      ⟨0,hK0,ht.1⟩ continuousOn_id
    obtain ⟨b,hb,hbmin⟩ := (hK.inter_right isClosed_Ici).exists_isMinOn
      ⟨dist x y,hKL,ht.2⟩ continuousOn_id
    have hat : a < t := lt_of_le_of_ne ha.2 (by intro heq; exact htn (heq ▸ ha.1))
    have htb : t < b := lt_of_le_of_ne hb.2 (by intro heq; exact htn (heq.symm ▸ hb.1))
    obtain ⟨u,hu,hua⟩ := ha.1
    obtain ⟨v,hv,hvb⟩ := hb.1
    have huv : u.1 < v.1 := by rw [hua,hvb]; exact hat.trans htb
    have hgap : ∀ w ∈ A, w.1 ≤ u.1 ∨ v.1 ≤ w.1 := by
      intro w hw
      have hwK : w.1 ∈ K := ⟨w,hw,rfl⟩
      by_cases hwt : w.1 ≤ t
      · exact Or.inl (by rw [hua]; exact hamax ⟨hwK,hwt⟩)
      · exact Or.inr (by rw [hvb]; exact hbmin ⟨hwK,(lt_of_not_ge hwt).le⟩)
    obtain ⟨z,huz,hzv⟩ := hmid u.2 v.2
    have hi := insert_midpoint_metricChain hA.1 hu hv huv hgap huz hzv
    have himem : ((u.1+v.1)/2,z) ∈ A := hA.2 hi (subset_insert _ _) (mem_insert _ _)
    rcases hgap _ himem with hl|hr
    · dsimp at hl; linarith
    · dsimp at hr; linarith

lemma exists_metric_segment [CompactSpace M] (x y : M)
    (hmid : ∀ u v : M, ∃ z, dist u z = dist u v/2 ∧ dist z v = dist u v/2) :
    ∃ γ : Icc (0:ℝ) (dist x y) → M, Isometry γ ∧
      γ ⟨0,⟨le_rfl,dist_nonneg⟩⟩ = x ∧
      γ ⟨dist x y,⟨dist_nonneg,le_rfl⟩⟩ = y := by
  obtain ⟨A,hA⟩ := exists_maximal_metricChain x y
  have hfull := maximal_metricChain_full_projection x y hmid hA
  have hex (t : Icc (0:ℝ) (dist x y)) : ∃ z : M, (t.1,z) ∈ A := by
    have hm : t.1 ∈ Prod.fst '' A := by rw [hfull]; exact t.2
    obtain ⟨w,hw,hwf⟩ := hm
    exact ⟨w.2,by simpa only [← hwf] using hw⟩
  choose γ hγ using hex
  refine ⟨γ,?_,?_,?_⟩
  · apply Isometry.of_dist_eq
    intro s t
    simpa only [Subtype.dist_eq,Real.dist_eq] using hA.1.2.2.2 (s.1,γ s) (hγ s) (t.1,γ t) (hγ t)
  · have hh := hA.1.2.2.2 _ (hγ ⟨0,⟨le_rfl,dist_nonneg⟩⟩) _ hA.1.1
    exact dist_eq_zero.mp (by simpa only [sub_self,abs_zero] using hh)
  · have hh := hA.1.2.2.2 _ (hγ ⟨dist x y,⟨dist_nonneg,le_rfl⟩⟩) _ hA.1.2.1
    exact dist_eq_zero.mp (by simpa only [sub_self,abs_zero] using hh)

end WeakMTWTransport

end

end OAI
