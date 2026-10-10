import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.LeafDistances
import OAI.Combinatorics.KMedianRecovery.Recovery.NearMass

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable def cluster (D : Finset V) (c : V → V) (o : V) : Finset V :=
  D.filter (fun p => c p = o)

noncomputable def clusterCost (D : Finset V) (c : V → V) (o : V) : ℝ :=
  ∑ p ∈ cluster D c o, dist p o

noncomputable def clusterMean (D : Finset V) (c : V → V) (o : V) : ℝ :=
  clusterCost D c o / (cluster D c o).card

noncomputable def comparisonCost (D : Finset V) (c : V → V) : ℝ :=
  ∑ p ∈ D, dist p (c p)

omit [PseudoMetricSpace V] in
lemma cluster_mem (D : Finset V) (c : V → V) (p o : V) :
    p ∈ cluster D c o ↔ p ∈ D ∧ c p = o := Finset.mem_filter

omit [PseudoMetricSpace V] in
lemma cluster_subset (D : Finset V) (c : V → V) (o : V) : cluster D c o ⊆ D :=
  Finset.filter_subset _ _

omit [PseudoMetricSpace V] in
lemma cluster_partition (D O : Finset V) (c : V → V)
    (hc : ∀ p ∈ D, c p ∈ O) (f : V → ℝ) :
    (∑ o ∈ O, ∑ p ∈ cluster D c o, f p) = ∑ p ∈ D, f p := by
  classical
  simp only [cluster, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  simp [hc p hp]

lemma clusterCost_nonneg (D : Finset V) (c : V → V) (o : V) : 0 ≤ clusterCost D c o :=
  Finset.sum_nonneg (fun _ _ => dist_nonneg)

lemma clusterMean_nonneg (D : Finset V) (c : V → V) (o : V) : 0 ≤ clusterMean D c o :=
  div_nonneg (clusterCost_nonneg D c o) (Nat.cast_nonneg _)

lemma clusterMean_mul_card (D : Finset V) (c : V → V) (o : V) :
    clusterMean D c o * (cluster D c o).card = clusterCost D c o := by
  by_cases h : (cluster D c o).card = 0
  · have he := Finset.card_eq_zero.mp h
    simp [clusterMean, clusterCost, he]
  · exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr h)

lemma comparisonCost_eq (D O : Finset V) (c : V → V) (hc : ∀ p ∈ D, c p ∈ O) :
    (∑ o ∈ O, clusterCost D c o) = comparisonCost D c := by
  have hh := cluster_partition D O c hc (fun p => dist p (c p))
  refine Eq.trans ?_ hh
  apply Finset.sum_congr rfl
  intro o _
  apply Finset.sum_congr rfl
  intro p hp
  rw [(cluster_mem D c p o).mp hp |>.2]

structure Comparison (D S O : Finset V) where
  assign : V → V
  assigned : ∀ p ∈ D, assign p ∈ O
  nearest : ∀ p ∈ D, ∀ o ∈ O, dist p (assign p) ≤ dist p o
  good : Finset V
  good_subset : good ⊆ O
  proxy : V → V
  proxy_mem : ∀ o ∈ good, proxy o ∈ S
  proxy_inj : Set.InjOn proxy (↑good)
  same_card : S.card = O.card
  proxy_cost : (∑ o ∈ good, ∑ p ∈ cluster D assign o, dist p (proxy o)) ≤
    (∑ o ∈ good, clusterCost D assign o) + (1/100 : ℝ)*comparisonCost D assign

namespace Comparison
variable {D S O : Finset V}
noncomputable def bad (C : Comparison D S O) : Finset V := O \ C.good
noncomputable def nonproxy (C : Comparison D S O) : Finset V := S \ C.good.image C.proxy
noncomputable def covered (C : Comparison D S O) (s : State V) : Finset V :=
  (s.leaves.map (fun z => C.assign z.1)).toFinset
noncomputable def near (C : Comparison D S O) (o : V) : Finset V :=
  (cluster D C.assign o).filter (fun p => dist p o ≤ (6/5 : ℝ)*clusterMean D C.assign o)
noncomputable def nearTotal (C : Comparison D S O) (Δ : ℝ) (s : State V) : ℝ :=
  ∑ o ∈ C.bad \ C.covered s, ∑ p ∈ C.near o, reference S Δ s p
noncomputable def removalTotal (C : Comparison D S O) (Δ : ℝ) (s : State V) : ℝ :=
  ∑ p ∈ D.filter (fun p => ∃ o ∈ C.nonproxy \ s.deleted, chosen S Δ s p = realTag o),
    reference S Δ s p

lemma nonproxy_card (C : Comparison D S O) : C.nonproxy.card = C.bad.card := by
  have hsub : C.good.image C.proxy ⊆ S := Finset.image_subset_iff.mpr C.proxy_mem
  rw [nonproxy, Finset.card_sdiff_of_subset hsub, bad,
    Finset.card_sdiff_of_subset C.good_subset, C.same_card,
    Finset.card_image_of_injOn C.proxy_inj]

lemma proxy_survives (C : Comparison D S O) (s : State V) (hq : s.deleted ⊆ C.nonproxy)
    (o : V) (ho : o ∈ C.good) : C.proxy o ∈ S \ s.deleted := by
  refine Finset.mem_sdiff.mpr ⟨C.proxy_mem o ho, ?_⟩
  intro hh
  have hn := (Finset.mem_sdiff.mp (hq hh)).2
  exact hn (Finset.mem_image.mpr ⟨o,ho,rfl⟩)

lemma good_reference_bound (C : Comparison D S O) (Δ : ℝ) (s : State V)
    (hq : s.deleted ⊆ C.nonproxy) :
    (∑ o ∈ C.good, ∑ p ∈ cluster D C.assign o, reference S Δ s p) ≤
      (∑ o ∈ C.good, clusterCost D C.assign o) +
        (1/100 : ℝ)*comparisonCost D C.assign := by
  apply le_trans ?_ C.proxy_cost
  apply Finset.sum_le_sum
  intro o ho
  apply Finset.sum_le_sum
  intro p _
  exact reference_le_real S Δ s p (C.proxy o) (C.proxy_survives s hq o ho)

lemma covered_empty (C : Comparison D S O) : C.covered State.initial = ∅ := by
  simp [covered, State.initial]

lemma covered_add (C : Comparison D S O) (s : State V) (w : V) (R : ℝ) :
    C.covered (s.add w R) = insert (C.assign w) (C.covered s) := by
  simp [covered, State.add, Finset.union_comm]

lemma covered_remove (C : Comparison D S O) (s : State V) (v : V) :
    C.covered (s.remove v) = C.covered s := rfl

def Correct (C : Comparison D S O) (hD : D.Nonempty) (kappa : ℝ) (s : State V) : Prop :=
  s.deleted ⊆ C.nonproxy ∧
  (s.leaves.map (fun z => C.assign z.1)).Nodup ∧
  ∀ z ∈ s.leaves,
    z.1 ∈ D ∧ C.assign z.1 ∈ C.bad ∧
    dist z.1 (C.assign z.1) ≤ (6/5 : ℝ)*clusterMean D C.assign (C.assign z.1) ∧
    0 < z.2 ∧ dist z.1 (C.assign z.1) ≤ z.2 ∧
    z.2 ≤ (1+kappa)*dist z.1 (C.assign z.1) +
      kappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card z.1

lemma correct_initial (C : Comparison D S O) (hD : D.Nonempty) (kappa : ℝ) :
    C.Correct hD kappa State.initial := by
  simp [Correct, State.initial]

lemma correct_covered_subset (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) : C.covered s ⊆ C.bad := by
  intro o ho
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ho)
  exact (hs.2.2 z hz).2.1

lemma correct_lengths (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) :
    s.leaves.length ≤ C.bad.card ∧ s.deleted.card ≤ C.bad.card := by
  have hc : (C.covered s).card = s.leaves.length := by
    rw [covered, List.toFinset_card_of_nodup hs.2.1, List.length_map]
  refine ⟨?_, ?_⟩
  · rw [← hc]
    exact Finset.card_le_card (C.correct_covered_subset hD kappa s hs)
  · rw [← C.nonproxy_card]
    exact Finset.card_le_card hs.1

lemma correct_radii_nonneg (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) : ∀ z ∈ s.leaves, 0 ≤ z.2 := by
  intro z hz
  exact (hs.2.2 z hz).2.2.2.1.le

lemma correct_remove (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (v : V) (hv : v ∈ C.nonproxy) : C.Correct hD kappa (s.remove v) := by
  refine ⟨?_,hs.2⟩
  simpa only [State.remove, Finset.insert_subset_iff] using And.intro hv hs.1

lemma correct_add (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (w : V) (R : ℝ) (hw : w ∈ D) (hb : C.assign w ∈ C.bad)
    (hnew : C.assign w ∉ C.covered s)
    (hnear : dist w (C.assign w) ≤ (6/5 : ℝ)*clusterMean D C.assign (C.assign w))
    (hR : 0 < R) (hlow : dist w (C.assign w) ≤ R)
    (hupp : R ≤ (1+kappa)*dist w (C.assign w) +
      kappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card w) :
    C.Correct hD kappa (s.add w R) := by
  refine ⟨hs.1,?_,?_⟩
  · change ((s.leaves ++ [(w,R)]).map (fun z => C.assign z.1)).Nodup
    rw [List.map_append]
    apply List.nodup_append.mpr
    refine ⟨hs.2.1,by simp,?_⟩
    intro a ha b hb hab
    have he : b = C.assign w := by simpa using hb
    apply hnew
    exact List.mem_toFinset.mpr ((hab.trans he) ▸ ha)
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hs.2.2 z hz
    · have he : z = (w,R) := by simpa using hz
      subst z
      exact ⟨hw,hb,hnear,hR,hlow,hupp⟩

lemma covered_witness (C : Comparison D S O) (s : State V) (o : V)
    (ho : o ∈ C.covered s) : ∃ z ∈ s.leaves, C.assign z.1 = o := by
  exact List.mem_map.mp (List.mem_toFinset.mp ho)

lemma reference_leaf_mem (Δ : ℝ) (s : State V) (z : V × ℝ) (hz : z ∈ s.leaves) (p : V) :
    reference S Δ s p ≤ dist p z.1+z.2 := by
  obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hz
  exact reference_le_leaf S Δ s p j z hj

lemma covered_client_bound (C : Comparison D S O) (hD : D.Nonempty)
    (kappa Δ : ℝ) (s : State V) (_hs : C.Correct hD kappa s)
    (z : V × ℝ) (hz : z ∈ s.leaves) (p : V) :
    reference S Δ s p ≤ dist p (C.assign z.1) + dist z.1 (C.assign z.1) + z.2 := by
  have hh := reference_leaf_mem (S := S) Δ s z hz p
  have ht := dist_triangle p (C.assign z.1) z.1
  rw [dist_comm (C.assign z.1) z.1] at ht
  linarith

lemma covered_cluster_bound (C : Comparison D S O) (hD : D.Nonempty)
    (kappa Δ : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (hP : 0 < comparisonCost D C.assign) (hk : 0 ≤ kappa) (hm : 0 < C.bad.card)
    (o : V) (ho : o ∈ C.covered s) :
    (∑ p ∈ cluster D C.assign o, reference S Δ s p) ≤
      (17/5+(22/5)*kappa)*clusterCost D C.assign o +
        2*kappa*comparisonCost D C.assign/C.bad.card := by
  obtain ⟨z,hz,he⟩ := C.covered_witness s o ho
  have hc := hs.2.2 z hz
  have hC : (cluster D C.assign o).Nonempty :=
    ⟨z.1,(cluster_mem D C.assign z.1 o).mpr ⟨hc.1,he⟩⟩
  have hn : (0 : ℝ) < (cluster D C.assign o).card := Nat.cast_pos.mpr (Finset.card_pos.mpr hC)
  have hmR : (0 : ℝ) < C.bad.card := Nat.cast_pos.mpr hm
  have hnear : dist z.1 o ≤ (6/5 : ℝ)*clusterMean D C.assign o := by simpa only [he] using hc.2.2.1
  have hrad : z.2 ≤ (1+kappa)*dist z.1 o +
      kappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card z.1 := by
    simpa only [he] using hc.2.2.2.2.2
  have hq := Population.leader_radius_le D (cluster D C.assign o) hD hC
    (cluster_subset D C.assign o) (comparisonCost D C.assign) C.bad.card z.1 o
    (clusterMean D C.assign o) (6/5) hP hm (by norm_num)
    (clusterMean_mul_card D C.assign o).symm hnear
  have hsumb : (∑ p ∈ cluster D C.assign o, reference S Δ s p) ≤
      clusterCost D C.assign o +
        (dist z.1 o+z.2)*(cluster D C.assign o).card := by
    calc
      _ ≤ ∑ p ∈ cluster D C.assign o, (dist p o+(dist z.1 o+z.2)) := by
        apply Finset.sum_le_sum
        intro p _
        have hp := C.covered_client_bound hD kappa Δ s hs z hz p
        simpa only [he, add_assoc] using hp
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul, clusterCost]; ring
  have hu : dist z.1 o+z.2 ≤
      (12/5+(22/5)*kappa)*clusterMean D C.assign o +
        kappa*(2*comparisonCost D C.assign/((C.bad.card : ℝ)*(cluster D C.assign o).card)) := by
    have hqk := mul_le_mul_of_nonneg_left hq hk
    have hnk := mul_le_mul_of_nonneg_left hnear (show 0 ≤ 2+kappa by linarith)
    nlinarith
  have hum := mul_le_mul_of_nonneg_right hu hn.le
  have heq : (kappa*(2*comparisonCost D C.assign /
      ((C.bad.card : ℝ)*(cluster D C.assign o).card)))*(cluster D C.assign o).card =
      2*kappa*comparisonCost D C.assign/C.bad.card := by field_simp
  have hrhs : ((12/5+(22/5)*kappa)*clusterMean D C.assign o +
      kappa*(2*comparisonCost D C.assign/((C.bad.card : ℝ)*(cluster D C.assign o).card)))*
        (cluster D C.assign o).card =
      (12/5+(22/5)*kappa)*clusterCost D C.assign o+
        2*kappa*comparisonCost D C.assign/C.bad.card := by
    rw [add_mul, mul_assoc, clusterMean_mul_card, heq]
  rw [hrhs] at hum
  linarith

lemma uncovered_cluster_bound (C : Comparison D S O) (hD : D.Nonempty)
    (kappa Δ : ℝ) (s : State V) (hs : C.Correct hD kappa s) (hΔ : 0 ≤ Δ) (o : V) :
    (∑ p ∈ cluster D C.assign o, reference S Δ s p) ≤
      (37/20 : ℝ)*clusterCost D C.assign o +
        61*(∑ p ∈ C.near o, reference S Δ s p) := by
  classical
  let X := cluster D C.assign o
  let H := reference S Δ s
  have hH : ∀ p : V, 0 ≤ H p := fun p => reference_nonneg S Δ s p hΔ
    (C.correct_radii_nonneg hD kappa s hs)
  by_cases hX : X.Nonempty
  · have hn : (0 : ℝ) < X.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hX)
    let T := ∑ p ∈ C.near o, H p
    have hT : 0 ≤ T := Finset.sum_nonneg (fun p _ => hH p)
    have hb : ∀ p ∈ X \ C.near o, H p ≤ (37/20 : ℝ)*dist p o + 60*T/X.card := by
      intro p hp
      have hpX := (Finset.mem_sdiff.mp hp).1
      have hfar : (6/5 : ℝ)*clusterMean D C.assign o < dist p o := by
        apply lt_of_not_ge
        intro hh
        exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_filter.mpr ⟨hpX,hh⟩)
      exact NearClients.main_far_bound X hX o p (clusterMean D C.assign o) H
        (clusterMean_mul_card D C.assign o).symm (fun q _ => hH q)
        (fun q _ => by simpa only [dist_comm o q] using reference_triangle S Δ s o q)
        (reference_triangle S Δ s p o) hfar
    have hnear : C.near o ⊆ X := Finset.filter_subset _ _
    have hpart := Finset.sum_sdiff hnear (f := H)
    have hcost : (∑ p ∈ X \ C.near o, dist p o) ≤ clusterCost D C.assign o :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => dist_nonneg)
    have hcard : ((X \ C.near o).card : ℝ) ≤ X.card := by exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    have hfars : (∑ p ∈ X \ C.near o, H p) ≤ (37/20 : ℝ)*clusterCost D C.assign o + 60*T := by
      have hh := Finset.sum_le_sum hb
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hh
      have heq : (X.card : ℝ)*(60*T/X.card) = 60*T := by field_simp
      have htpos : 0 ≤ 60*T/(X.card : ℝ) := div_nonneg (by positivity) hn.le
      have hm := mul_le_mul_of_nonneg_right hcard htpos
      rw [heq] at hm
      nlinarith
    change (∑ p ∈ X, H p) ≤ (37/20 : ℝ)*clusterCost D C.assign o+61*T
    linarith
  · have he : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hX
    have hnear : C.near o = ∅ := by
      have hh : C.near o ⊆ X := Finset.filter_subset _ _
      rw [he] at hh
      exact Finset.subset_empty.mp hh
    simp only [show cluster D C.assign o = ∅ from he, Finset.sum_empty, clusterCost,
      hnear, mul_zero, add_zero, le_refl]

lemma center_sum_partition (C : Comparison D S O) (s : State V)
    (hA : C.covered s ⊆ C.bad) (f : V → ℝ) :
    (∑ o ∈ O, f o) = (∑ o ∈ C.good, f o) + (∑ o ∈ C.covered s, f o) +
      ∑ o ∈ C.bad \ C.covered s, f o := by
  have hg := Finset.sum_sdiff C.good_subset (f := f)
  have ha := Finset.sum_sdiff hA (f := f)
  change (∑ o ∈ C.bad, f o)+(∑ o ∈ C.good, f o) = ∑ o ∈ O, f o at hg
  linarith

lemma covered_cost_aggregate (C : Comparison D S O) (hD : D.Nonempty)
    (kappa Δ : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (hP : 0 < comparisonCost D C.assign) (hk : 0 ≤ kappa) (hm : 0 < C.bad.card) :
    (∑ o ∈ C.covered s, ∑ p ∈ cluster D C.assign o, reference S Δ s p) ≤
      (17/5+(22/5)*kappa)*(∑ o ∈ C.covered s, clusterCost D C.assign o) +
        2*kappa*comparisonCost D C.assign := by
  have hh := Finset.sum_le_sum (fun o ho => C.covered_cluster_bound hD kappa Δ s hs hP hk hm o ho)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hh
  have hcard : ((C.covered s).card : ℝ) ≤ C.bad.card := by
    exact_mod_cast Finset.card_le_card (C.correct_covered_subset hD kappa s hs)
  have hmR : (0 : ℝ) < C.bad.card := Nat.cast_pos.mpr hm
  have hc : 0 ≤ 2*kappa*comparisonCost D C.assign/(C.bad.card : ℝ) :=
    div_nonneg (by positivity) hmR.le
  have hn := mul_le_mul_of_nonneg_right hcard hc
  have he : (C.bad.card : ℝ)*(2*kappa*comparisonCost D C.assign/C.bad.card) =
      2*kappa*comparisonCost D C.assign := by field_simp
  rw [he] at hn
  linarith

lemma correct_weight_bound (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (s : State V) (hs : C.Correct hD (1/1000000) s) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card) :
    totalWeight D S Δ s ≤ (171/50 : ℝ)*comparisonCost D C.assign+61*C.nearTotal Δ s := by
  have hA := C.correct_covered_subset hD (1/1000000) s hs
  have hW : totalWeight D S Δ s = ∑ p ∈ D, reference S Δ s p := by
    apply Finset.sum_congr rfl
    intro p _
    exact clientWeight_eq S Δ s p hΔ (C.correct_radii_nonneg hD (1/1000000) s hs)
  have hpart := C.center_sum_partition s hA (clusterCost D C.assign)
  rw [comparisonCost_eq D O C.assign C.assigned] at hpart
  have hRef := C.center_sum_partition s hA (fun o =>
    ∑ p ∈ cluster D C.assign o, reference S Δ s p)
  rw [cluster_partition D O C.assign C.assigned] at hRef
  have hG := C.good_reference_bound Δ s hs.1
  have hAA := C.covered_cost_aggregate hD (1/1000000) Δ s hs hP (by norm_num) hm
  have hBB := Finset.sum_le_sum (s := C.bad \ C.covered s) (fun o _ =>
    C.uncovered_cluster_bound hD (1/1000000) Δ s hs hΔ o)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hBB
  have hG0 : 0 ≤ ∑ o ∈ C.good, clusterCost D C.assign o :=
    Finset.sum_nonneg (fun o _ => clusterCost_nonneg D C.assign o)
  have hB0 : 0 ≤ ∑ o ∈ C.bad \ C.covered s, clusterCost D C.assign o :=
    Finset.sum_nonneg (fun o _ => clusterCost_nonneg D C.assign o)
  unfold nearTotal
  rw [hW]
  linarith

lemma comparison_triangle (C : Comparison D S O) (w p : V) (hw : w ∈ D) (hp : p ∈ D) :
    dist w (C.assign w) ≤ dist w p + dist p (C.assign p) :=
  (C.nearest w hw (C.assign p) (C.assigned p hp)).trans (dist_triangle w p (C.assign p))

lemma correct_leaf_dominates (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (w : V) (hw : w ∈ D) (z : V × ℝ) (hz : z ∈ s.leaves) :
    dist w (C.assign w) ≤ dist w z.1+z.2 := by
  have hh := C.comparison_triangle w z.1 hw (hs.2.2 z hz).1
  have hr := (hs.2.2 z hz).2.2.2.2.1
  linarith

lemma correct_nearestLeaf_lower (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (w : V) (hw : w ∈ D) (r : ℝ) (hr : nearestLeaf s w = some r) :
    dist w (C.assign w) ≤ r :=
  nearestLeaf_lower s w r _ hr (fun z hz => C.correct_leaf_dominates hD kappa s hs w hw z hz)

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
