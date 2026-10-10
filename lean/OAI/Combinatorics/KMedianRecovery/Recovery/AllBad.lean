import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Produce
import OAI.Combinatorics.KMedianRecovery.Geometry.RealCost
import OAI.Combinatorics.KMedianRecovery.Recovery.Cluster

namespace OAI

namespace MetricKMedianRecovery.IntegralCandidates
open LocalSearch Anchoring Completion Sampling Surplus
variable {V : Type*} [MetricSpace V] [LinearOrder V] [Fintype V]

omit [LinearOrder V] [Fintype V] in
lemma realCost_eq (D S : Finset V) : realCost D S = cost D S := by
  by_cases hS : S.Nonempty
  · simp only [realCost,cost,connection,dite_eq_left hS,distanceTo]
  · simp only [realCost,cost,connection,dite_eq_right hS,Finset.sum_const_zero]

omit [LinearOrder V] [Fintype V] in
lemma comparisonCost_nearest (D O : Finset V) (hO : O.Nonempty) :
    comparisonCost D (LocalSearch.nearest O hO) = cost D O := by
  simp only [comparisonCost,cost,nearest_distance]

noncomputable def allBad (D S O : Finset V) (hO : O.Nonempty) (hcard : S.card = O.card) :
    Comparison D S O where
  assign := LocalSearch.nearest O hO
  assigned := fun p _ => nearest_mem O hO p
  nearest := fun p _ i hi => (nearest_distance O hO p).trans_le (connection_le hi)
  good := ∅
  good_subset := Finset.empty_subset _
  proxy := id
  proxy_mem := by simp
  proxy_inj := by simp
  same_card := hcard
  proxy_cost := by
    simp only [Finset.sum_empty,zero_add,comparisonCost_nearest]
    exact mul_nonneg (by norm_num) (cost_nonneg D O)

omit [Fintype V] in
lemma allBad_count (D S O : Finset V) (hO : O.Nonempty) (hcard : S.card = O.card) :
    (allBad D S O hO hcard).bad.card = O.card := by
  simp only [Comparison.bad,allBad,Finset.sdiff_empty]

omit [Fintype V] in

theorem separated_comparison (F D O S : Finset V) (hO : O.Nonempty) (hS : S.Nonempty)
    (hO2 : 2 ≤ O.card) (hOF : O ⊆ F) (hSF : S ⊆ F) (hcard : S.card = O.card)
    (hlocal : WidthLocalMin F D S 5) (beta : ℝ) (hbeta : 0 < beta) (hP : 0 < cost D O)
    (hsep : ∀ i ∈ O, beta*cost D O ≤
      ((Anchoring.cluster D (LocalSearch.nearest O hO) i).card:ℝ)*separation O i) :
    ∃ C : Comparison D S O,
      C.assign = LocalSearch.nearest O hO ∧ (C.bad.card:ℝ) ≤ countConstant (1/100)/beta := by
  let b := beta*cost D O
  have hb : 0 < b := mul_pos hbeta hP
  have hshort : shortCenters O (clusterScale D O (LocalSearch.nearest O hO)) b = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hh := Finset.mem_filter.mp hi
    exact (not_lt.mpr (hsep i hh.1)) hh.2
  have hscale : b*((S.card:ℝ)-O.card+
      (shortCenters O (clusterScale D O (LocalSearch.nearest O hO)) b).card) ≤ 10*cost D O := by
    simp only [hshort,Finset.card_empty,hcard,sub_self,Nat.cast_zero,add_zero,mul_zero]
    positivity
  obtain ⟨G,B,hpart,hdis,hinj,hmem,hproxy,hcount⟩ :=
    anchoring F D O S hO hS hO2 hSF hOF (by omega) hlocal b (1/100) hb hP
      (by norm_num) (by norm_num) hscale
  have hGO : G ⊆ O := by rw [← hpart]; exact Finset.subset_union_left
  let C : Comparison D S O := {
    assign := LocalSearch.nearest O hO
    assigned := fun p _ => nearest_mem O hO p
    nearest := fun p _ i hi => (nearest_distance O hO p).trans_le (connection_le hi)
    good := G
    good_subset := hGO
    proxy := LocalSearch.nearest S hS
    proxy_mem := hmem
    proxy_inj := hinj
    same_card := hcard
    proxy_cost := by
      rw [comparisonCost_nearest]
      exact hproxy }
  have hbad : C.bad = B := by
    change O \ G = B
    ext i
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨hi,hng⟩
      rw [← hpart] at hi
      rcases Finset.mem_union.mp hi with hg | hb
      · exact False.elim (hng hg)
      · exact hb
    · intro hi
      refine ⟨?_,?_⟩
      · rw [← hpart]
        exact Finset.mem_union_right _ hi
      · exact fun hg => Finset.disjoint_left.mp hdis hg hi
  refine ⟨C,rfl,?_⟩
  rw [hbad]
  have he : countConstant (1/100)*cost D O/b = countConstant (1/100)/beta := by
    dsimp [b]
    field_simp
  exact hcount.trans_eq he

omit [Fintype V] in

theorem local_anchor (δ : V → V → ℕ) (F D : Finset V) (r M : ℕ)
    (hr : 0 < r) (hrF : r ≤ F.card)
    (hδ : ∀ p ∈ D, ∀ i ∈ F, (δ p i : ℝ) = dist p i)
    (hM : ∀ p ∈ D, ∀ i ∈ F, δ p i ≤ M) :
    ∃ S : Finset V, S ⊆ F ∧ S.Nonempty ∧ S.card = r ∧ WidthLocalMin F D S 5 ∧
      cost D S ≤ 5*optimum F D r := by
  have hF : F.Nonempty := Finset.card_pos.mp (hr.trans_le hrF)
  obtain ⟨i,hi⟩ := hF
  obtain ⟨S,hSF,hS,hcard,_,hlocal⟩ := PhaseSurplusProducer.pad_and_descend δ F D {i} r M
    (Finset.singleton_nonempty _) (Finset.singleton_subset_iff.mpr hi)
    (by simpa only [Finset.card_singleton] using Nat.succ_le_iff.mpr hr) hrF hδ hM
  refine ⟨S,hSF,hS,hcard,hlocal,?_⟩
  obtain ⟨O,hOF,hO,hOr,hopt⟩ := optimum_attained F D ⟨i,hi⟩ r hr
  simpa only [hopt] using local_five_approx F D S O hS hO hSF hlocal hOF (hcard ▸ hOr)

end MetricKMedianRecovery.IntegralCandidates

end OAI
