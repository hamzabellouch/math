import Mathlib
import OAI.Combinatorics.KMedianRecovery.Strictness.ClientCharge
import OAI.Combinatorics.KMedianRecovery.Recovery.CoveredCenter
import OAI.Combinatorics.KMedianRecovery.Branching.SuccessfulCompletionCharge

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

noncomputable def destinations (C : Comparison D S O) (s : State V) :
    Finset (Destination V s.leaves.length) :=
  C.good.image (fun o => Destination.proxy (C.proxy o)) ∪
    Finset.univ.image Destination.covered ∪
    (C.bad \ C.covered s).image Destination.uncovered

noncomputable def ownDestination (C : Comparison D S O) (s : State V) (p : V) :
    Destination V s.leaves.length :=
  if C.assign p ∈ C.good then .proxy (C.proxy (C.assign p))
  else if h : C.assign p ∈ C.covered s then .covered (C.coveredIndex s (C.assign p) h)
  else .uncovered (C.assign p)

lemma ownDestination_mem (C : Comparison D S O) (s : State V) (p : V) (hp : p ∈ D) :
    C.ownDestination s p ∈ C.destinations s := by
  classical
  unfold ownDestination destinations
  split_ifs with hg hc
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hg, rfl⟩))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨_, Finset.mem_univ _, rfl⟩))
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨_, Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨C.assigned p hp, hg⟩, hc⟩, rfl⟩)

lemma destinations_nonempty (C : Comparison D S O) (hD : D.Nonempty) (s : State V) :
    (C.destinations s).Nonempty := by
  obtain ⟨p, hp⟩ := hD
  exact ⟨_, C.ownDestination_mem s p hp⟩

lemma own_charge_good (C : Comparison D S O) (s : State V) (theta : ℝ)
    (p o : V) (ho : o ∈ C.good) (hp : C.assign p = o) :
    clientCharge theta (C.coveredCenter s) (leafCenter s) (leafRadius s) p
      (C.ownDestination s p) = dist p (C.proxy o) := by
  simp [ownDestination, hp, ho, clientCharge]

lemma own_charge_covered (C : Comparison D S O) (hD : D.Nonempty) (kappa : ℝ)
    (s : State V) (hs : C.Correct hD kappa s) (theta : ℝ)
    (p o : V) (ho : o ∈ C.covered s) (hp : C.assign p = o) :
    clientCharge theta (C.coveredCenter s) (leafCenter s) (leafRadius s) p
      (C.ownDestination s p) =
      dist p o + theta * (dist (C.leaderPair s o).1 o + (C.leaderPair s o).2) := by
  have hn : o ∉ C.good := (Finset.mem_sdiff.mp (C.correct_covered_subset hD kappa s hs ho)).2
  simp only [ownDestination, hp, ite_eq_right hn, dite_eq_left ho, clientCharge,
    coveredIndex_spec, leafCenter, leafRadius, C.leafPair_index hD kappa s hs o ho]

lemma own_charge_uncovered (C : Comparison D S O) (s : State V) (theta : ℝ)
    (p o : V) (ho : o ∈ C.bad \ C.covered s) (hp : C.assign p = o) :
    clientCharge theta (C.coveredCenter s) (leafCenter s) (leafRadius s) p
      (C.ownDestination s p) = dist p o := by
  have hg : o ∉ C.good := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp ho).1).2
  have hc := (Finset.mem_sdiff.mp ho).2
  simp [ownDestination, hp, hg, hc, clientCharge]

lemma convex_capped_le (theta b x : ℝ) (ht : theta ≤ 1) :
    theta*b+(1-theta)*min b x ≤ b := by
  have hh := mul_le_mul_of_nonneg_left (min_le_left b x) (sub_nonneg.mpr ht)
  nlinarith

lemma interpolated_reference_le (Δ : ℝ) (s : State V)
    {E : Type*} (loc : E → V) (X : Finset E) (theta : ℝ) (ht : theta ≤ 1) (p : V) :
    theta * reference S Δ s p + (1-theta) *
      cappedCost (reference S Δ s p) (fun e => dist p (loc e)) X ≤ reference S Δ s p := by
  have hh := cappedCost_le_base (reference S Δ s p) (fun e => dist p (loc e)) X
  nlinarith [mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr ht)]

lemma interpolated_covered_charge (C : Comparison D S O) (hD : D.Nonempty)
    (kappa Δ : ℝ) (s : State V) (_hs : C.Correct hD kappa s)
    {E : Type*} (loc : E → V) (X : Finset E)
    (hcenter : ∀ i, ∃ e ∈ X, loc e = C.coveredCenter s i)
    (theta : ℝ) (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1)
    (p o : V) (ho : o ∈ C.covered s) :
    theta * reference S Δ s p + (1-theta) *
      cappedCost (reference S Δ s p) (fun e => dist p (loc e)) X ≤
      dist p o + theta * (dist (C.leaderPair s o).1 o + (C.leaderPair s o).2) := by
  let i := C.coveredIndex s o ho
  obtain ⟨e, he, heo⟩ := hcenter i
  have hei : C.coveredCenter s i = o := C.coveredIndex_spec s o ho
  have heo' : loc e = o := heo.trans hei
  have hc := cappedCost_le_offer (reference S Δ s p) (fun e => dist p (loc e)) he
  rw [heo'] at hc
  have hw := C.leaderPair_spec s o ho
  obtain ⟨j, hj, hjz⟩ := List.mem_iff_getElem.mp hw.1
  have href := reference_le_leaf S Δ s p j (C.leaderPair s o)
    (by simp only [List.getElem?_eq_getElem hj, hjz])
  have tri := dist_triangle p o (C.leaderPair s o).1
  rw [dist_comm o (C.leaderPair s o).1] at tri
  have hc' := mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr ht1)
  have hr' := mul_le_mul_of_nonneg_left href ht0
  have ht' := mul_le_mul_of_nonneg_left tri ht0
  nlinarith

noncomputable def endpointCharge (C : Comparison D S O) (Δ : ℝ) (s : State V)
    (theta : ℝ) (J : Finset V) (p : V) : ℝ :=
  if C.assign p ∈ C.good then dist p (C.proxy (C.assign p))
  else if C.assign p ∈ C.covered s then
    dist p (C.assign p) + theta *
      (dist (C.leaderPair s (C.assign p)).1 (C.assign p) + (C.leaderPair s (C.assign p)).2)
  else if p ∈ J then dist p (C.assign p) else reference S Δ s p

lemma own_charge_le_endpoint (C : Comparison D S O) (hD : D.Nonempty)
    (kappa Δ : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (theta : ℝ) (J : Finset V) (p : V) (hp : p ∈ D) (hpJ : p ∈ J) :
    clientCharge theta (C.coveredCenter s) (leafCenter s) (leafRadius s) p
      (C.ownDestination s p) ≤ C.endpointCharge Δ s theta J p := by
  by_cases hg : C.assign p ∈ C.good
  · rw [C.own_charge_good s theta p (C.assign p) hg rfl]
    simp [endpointCharge,hg]
  by_cases hc : C.assign p ∈ C.covered s
  · rw [C.own_charge_covered hD kappa s hs theta p (C.assign p) hc rfl]
    simp [endpointCharge,hg,hc]
  · have hb : C.assign p ∈ C.bad \ C.covered s :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨C.assigned p hp,hg⟩,hc⟩
    rw [C.own_charge_uncovered s theta p (C.assign p) hb rfl]
    simp [endpointCharge,hg,hc,hpJ]

lemma interpolation_le_endpoint (C : Comparison D S O) (hD : D.Nonempty)
    (kappa Δ : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    {E : Type*} (loc : E → V) (X : Finset E)
    (hcenter : ∀ i, ∃ e ∈ X, loc e = C.coveredCenter s i)
    (theta : ℝ) (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1)
    (J : Finset V) (p : V) (hpJ : p ∉ J) :
    theta * reference S Δ s p + (1-theta) *
      cappedCost (reference S Δ s p) (fun e => dist p (loc e)) X ≤
      C.endpointCharge Δ s theta J p := by
  by_cases hg : C.assign p ∈ C.good
  · simp only [endpointCharge,ite_eq_left hg]
    exact (interpolated_reference_le Δ s loc X theta ht1 p).trans
      (reference_le_real S Δ s p (C.proxy (C.assign p))
        (C.proxy_survives s hs.1 (C.assign p) hg))
  by_cases hc : C.assign p ∈ C.covered s
  · simp only [endpointCharge,ite_eq_right hg,ite_eq_left hc]
    exact C.interpolated_covered_charge hD kappa Δ s hs loc X hcenter theta ht0 ht1 p (C.assign p) hc
  · simp only [endpointCharge,ite_eq_right hg,ite_eq_right hc,ite_eq_right hpJ]
    exact interpolated_reference_le Δ s loc X theta ht1 p

lemma endpoint_charge_sum (C : Comparison D S O) (hD : D.Nonempty)
    (kappa Δ : ℝ) (s : State V) (hs : C.Correct hD kappa s) (theta : ℝ) (J : Finset V) :
    (∑ p ∈ D, C.endpointCharge Δ s theta J p) =
      (∑ o ∈ C.good, ∑ p ∈ cluster D C.assign o, dist p (C.proxy o)) +
      (∑ o ∈ C.covered s, ∑ p ∈ cluster D C.assign o,
        (dist p o+theta*(dist (C.leaderPair s o).1 o+(C.leaderPair s o).2))) +
      (∑ o ∈ C.bad \ C.covered s, ∑ p ∈ cluster D C.assign o,
        if p ∈ J then dist p o else reference S Δ s p) := by
  rw [← cluster_partition D O C.assign C.assigned (C.endpointCharge Δ s theta J)]
  rw [C.center_sum_partition s (C.correct_covered_subset hD kappa s hs)
    (fun o => ∑ p ∈ cluster D C.assign o, C.endpointCharge Δ s theta J p)]
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intro o ho
      apply Finset.sum_congr rfl
      intro p hp
      simp only [endpointCharge,(cluster_mem D C.assign p o).mp hp |>.2,ite_eq_left ho]
    · apply Finset.sum_congr rfl
      intro o ho
      have hn := (Finset.mem_sdiff.mp (C.correct_covered_subset hD kappa s hs ho)).2
      apply Finset.sum_congr rfl
      intro p hp
      simp only [endpointCharge,(cluster_mem D C.assign p o).mp hp |>.2,ite_eq_right hn,ite_eq_left ho]
  · apply Finset.sum_congr rfl
    intro o ho
    have hc := (Finset.mem_sdiff.mp ho).2
    have hg := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp ho).1).2
    apply Finset.sum_congr rfl
    intro p hp
    simp only [endpointCharge,(cluster_mem D C.assign p o).mp hp |>.2,ite_eq_right hg,ite_eq_right hc]

lemma completion_endpoint_success (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (s : State V) (hs : C.Correct hD (1/1000000) s) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (hI : C.removalTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (hT : C.nearTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    {E : Type*} (loc : E → V) (X : Finset E)
    (hcenter : ∀ i, ∃ e ∈ X, loc e = C.coveredCenter s i) :
    let J := assignedClients D (C.nonproxy \ s.deleted) (completionAssignment S Δ s)
    2 * (∑ p ∈ J, virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ p) +
      (∑ p ∈ J, clientCharge (19/50) (C.coveredCenter s) (leafCenter s) (leafRadius s) p
        (C.ownDestination s p)) +
      ∑ p ∈ D \ J, ((19/50) * virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ p +
        (1-19/50) * cappedCost (virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ p)
          (fun e => dist p (loc e)) X) ≤
      (240258179/125000000:ℝ)*comparisonCost D C.assign := by
  classical
  dsimp only
  let J := assignedClients D (C.nonproxy \ s.deleted) (completionAssignment S Δ s)
  have hJD : J ⊆ D := Finset.filter_subset _ _
  have hsum := C.successful_completion_charge hD Δ s hs hΔ hP hm J (C.removalTotal Δ s) hI hT
  have hemp := C.endpoint_charge_sum hD (1/1000000) Δ s hs (19/50) J
  have hsum' : 2*C.removalTotal Δ s + (∑ p ∈ D, C.endpointCharge Δ s (19/50) J p) ≤
      (240258179/125000000:ℝ)*comparisonCost D C.assign := by linarith
  have h₁ := Finset.sum_le_sum (s := J) (fun p hp =>
    C.own_charge_le_endpoint hD (1/1000000) Δ s hs (19/50) J p (hJD hp) hp)
  have h₂ := Finset.sum_le_sum (s := D \ J) (fun p hp =>
    C.interpolation_le_endpoint hD (1/1000000) Δ s hs loc X hcenter
      (19/50) (by norm_num) (by norm_num) J p (Finset.mem_sdiff.mp hp).2)
  have hsplit := Finset.sum_sdiff hJD (f := C.endpointCharge Δ s (19/50) J)
  have hIeq : (∑ p ∈ J, virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ p) =
      C.removalTotal Δ s := assigned_reference_total_agree D S (C.nonproxy \ s.deleted) Δ s
  change 2*(∑ p ∈ J, virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ p) +
    (∑ p ∈ J, _) + (∑ p ∈ D \ J, _) ≤ _
  rw [hIeq]
  simp_rw [← reference_eq_virtualNearest] at ⊢
  linarith

lemma surrogate_success {E R : Type*} [DecidableEq E] [Fintype R]
    (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (s : State V) (hs : C.Correct hD (1/1000000) s) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (hI : C.removalTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (hN : C.nearTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (loc : E → V) (X : Finset E)
    (hcenter : ∀ i, ∃ e ∈ X, loc e = C.coveredCenter s i)
    (G Blue : Finset V) (redLoc : R → V) (hredInj : Function.Injective redLoc)
    (q : ℕ) (T : Finset R) (hT : T.card = q)
    (hdisj : Disjoint (T.image redLoc) Blue)
    (hcover : T.image redLoc ∪ Blue = C.nonproxy \ s.deleted)
    (hredDest : ∀ r ∈ T,
      match selectedDestination (19/50) (C.coveredCenter s) (leafCenter s) (leafRadius s)
          (C.destinations s) (C.destinations_nonempty hD s) (redLoc r) with
      | .proxy φ => φ ∈ G | .covered _ => True | .uncovered _ => False)
    (K : ℝ)
    (hK : K ≤ ∑ u ∈ Blue, assignmentWeight D (completionAssignment S Δ s) u *
      minimumMixed (19/50) (C.coveredCenter s) (leafCenter s) (leafRadius s)
        (C.destinations s) (C.destinations_nonempty hD s) u) :
    let Ψ := surrogate (P := ↥D) K q
      (fun p => virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ p)
      (fun p e => dist (p:V) (loc e))
      (fun r => assignmentWeight D (completionAssignment S Δ s) (redLoc r))
      (fun r => virtualNearest G (leafCenter s) (leafRadius s) Δ (redLoc r))
      (fun r e => dist (redLoc r) (loc e))
    (19/50)*Ψ ∅+(1-19/50)*Ψ X ≤
      (240258179/125000000:ℝ)*comparisonCost D C.assign := by
  dsimp only
  have h₁ := surrogate_comparison_bound D (S \ s.deleted) G (C.nonproxy \ s.deleted) Blue
    (leafCenter s) (C.coveredCenter s) (leafRadius s) Δ (19/50) K (by norm_num) (by norm_num)
    (completionAssignment S Δ s) redLoc hredInj T hT hdisj hcover loc X hcenter
    (C.destinations s) (C.destinations_nonempty hD s) (fun r hr => by
      have hh := hredDest r hr
      cases hd : selectedDestination (19/50) (C.coveredCenter s) (leafCenter s)
          (leafRadius s) (C.destinations s) (C.destinations_nonempty hD s) (redLoc r) with
      | proxy φ => simpa only [hd] using hh
      | covered i => trivial
      | uncovered v => simp only [hd] at hh) hK
  have h₂ := completion_endpoint_bound D (S \ s.deleted) (C.nonproxy \ s.deleted)
    (leafCenter s) (C.coveredCenter s) (leafRadius s) Δ (19/50) (by norm_num) (by norm_num)
    (completionAssignment S Δ s) (completionAssignment_distance S Δ s)
    (C.destinations s) (C.destinations_nonempty hD s) (C.ownDestination s)
    (C.ownDestination_mem s) loc X
  exact h₁.trans (h₂.trans (C.completion_endpoint_success hD Δ s hs hΔ hP hm hI hN loc X hcenter))

end MetricKMedianRecovery.Sampling.Comparison

end OAI
