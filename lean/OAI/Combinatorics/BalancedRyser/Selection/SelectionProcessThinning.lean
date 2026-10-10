import OAI.Combinatorics.BalancedRyser.Selection.SelectionProcessLaw
import OAI.Combinatorics.BalancedRyser.Selection.SelectionThinning

namespace OAI

open scoped BigOperators Classical

namespace Balanced.Selection.Process

noncomputable section

variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] in
lemma flagsWeight_eq_thinningMass (p : Parameters) (q : ℕ) (G : Input I V)
    (S : State I V) (flags : V → Bool) :
    flagsWeight p q G S flags =
      SelectionThinning.thinningMass (thinningRate p q G S) flags := rfl

omit [Fintype I] in

lemma sum_drawWeight_adj_vertex (G : Input I V) (S : State I V) (i : I) (u : V) :
    (∑ w : V, if G.graph.Adj u w then drawWeight G S i w else 0) =
      if i ∈ S.remaining then
        (((neighbors G u) ∩ domain G S i).card : ℝ) *
          ((S.remaining.card : ℝ) * (domain G S i).card)⁻¹ else 0 := by
  by_cases hi : i ∈ S.remaining
  · rw [ite_eq_left hi]
    calc
      _ = ∑ w : V, if w ∈ neighbors G u ∩ domain G S i then
          ((S.remaining.card : ℝ) * (domain G S i).card)⁻¹ else 0 := by
        apply Finset.sum_congr rfl
        intro w _
        by_cases ha : G.graph.Adj u w <;> by_cases hd : w ∈ domain G S i <;>
          simp [hi, ha, hd, drawWeight, neighbors]
      _ = _ := by
        rw [← Finset.sum_filter]
        have hfilter : (Finset.univ.filter (fun w : V => w ∈ neighbors G u ∩ domain G S i)) =
            neighbors G u ∩ domain G S i := by ext; simp
        rw [hfilter, Finset.sum_const, nsmul_eq_mul]
  · simp [drawWeight, hi]

lemma drawWeight_conflict_mass (G : Input I V) (S : State I V) (u : V) :
    SelectionThinning.eventMass (fun iw : I × V => drawWeight G S iw.1 iw.2)
      (fun iw => G.graph.Adj u iw.2) = hazard G S u := by
  unfold SelectionThinning.eventMass
  rw [Fintype.sum_prod_type]
  simp_rw [sum_drawWeight_adj_vertex]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  unfold hazard
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp [div_eq_mul_inv, mul_comm, mul_assoc]

lemma drawWeight_pair_sum (G : Input I V) (S : State I V)
    (hS : S.remaining.Nonempty) (hdom : ∀ i ∈ S.remaining, (domain G S i).Nonempty) :
    (∑ iw : I × V, drawWeight G S iw.1 iw.2) = 1 := by
  rw [Fintype.sum_prod_type]
  exact sum_drawWeight G S hS hdom

lemma performed_survival_mass (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (hp : Precheck p q t G S) (u : V)
    (hu : u ∈ currentVertices G S) :
    (∑ r : Noise I V, if u ∈ survivors G S r.2.1 r.2.2 then
      noiseWeight p q G S r else 0) = 1 - p.alpha q := by
  have hnorm := drawWeight_pair_sum G S hp.1 (fun i hi => (hp.2.2.2.1 i hi).1)
  have hbad : SelectionThinning.eventMass
      (fun iw : I × V => drawWeight G S iw.1 iw.2)
      (fun iw => G.graph.Adj iw.2 u) = hazard G S u := by
    simpa only [SimpleGraph.adj_comm] using drawWeight_conflict_mass G S u
  have hs := SelectionThinning.surviving_event_mass
    (fun iw : I × V => drawWeight G S iw.1 iw.2) (thinningRate p q G S)
    (fun iw => ¬ G.graph.Adj iw.2 u) u
  rw [SelectionThinning.eventMass_compl _ hnorm, hbad] at hs
  have hrate : thinningRate p q G S u =
      SelectionThinning.thinningRate (p.alpha q) (hazard G S u) := by
    simp [thinningRate, hu, SelectionThinning.thinningRate]
  rw [hrate, SelectionThinning.equal_survival
    (lt_of_le_of_lt (hp.2.2.2.2 u hu) hp.2.2.1)] at hs
  simp only [Noise, Fintype.sum_prod_type] at hs ⊢
  convert hs using 1
  apply Finset.sum_congr (by ext; simp)
  intro i _
  apply Finset.sum_congr (by ext; simp)
  intro w _
  apply Finset.sum_congr (by ext; simp)
  intro flags _
  by_cases he : ¬ G.graph.Adj w u ∧ flags u = false <;>
    simp [survivors, hu, he, noiseWeight, SelectionThinning.jointMass,
      flagsWeight_eq_thinningMass]

lemma drawWeight_slot_mass (G : Input I V) (S : State I V)
    (hS : S.remaining.Nonempty) (hdom : ∀ i ∈ S.remaining, (domain G S i).Nonempty)
    (j : I) (hj : j ∈ S.remaining) :
    SelectionThinning.eventMass (fun iw : I × V => drawWeight G S iw.1 iw.2)
      (fun iw => iw.1 = j) = (S.remaining.card : ℝ)⁻¹ := by
  unfold SelectionThinning.eventMass
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ i : I, if i = j then (∑ w : V, drawWeight G S i w) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = j <;> simp [hi]
    _ = ∑ w : V, drawWeight G S j w := by simp
    _ = _ := by rw [sum_drawWeight_vertex G S hS hdom, ite_eq_left hj]

omit [Fintype I] [Fintype V] in
lemma drawWeight_eq_zero_of_same_slot_conflict (G : Input I V) (S : State I V)
    (hwithin : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (i : I) (w u : V) (hi : i = G.slot u) (ha : G.graph.Adj w u) :
    drawWeight G S i w = 0 := by
  unfold drawWeight
  split_ifs with hd
  · have hw : G.slot w = i := (Finset.mem_filter.mp hd.2).2
    exact (hwithin w u (hw.trans hi) ha).elim
  · rfl

lemma drawWeight_survives_slot_mass (G : Input I V) (S : State I V)
    (hS : S.remaining.Nonempty) (hdom : ∀ i ∈ S.remaining, (domain G S i).Nonempty)
    (hwithin : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (u : V) (hu : G.slot u ∈ S.remaining) :
    SelectionThinning.eventMass (fun iw : I × V => drawWeight G S iw.1 iw.2)
      (fun iw => ¬ G.graph.Adj iw.2 u ∧ iw.1 ≠ G.slot u) =
      1 - hazard G S u - (S.remaining.card : ℝ)⁻¹ := by
  have hbad : SelectionThinning.eventMass
      (fun iw : I × V => drawWeight G S iw.1 iw.2)
      (fun iw => G.graph.Adj iw.2 u) = hazard G S u := by
    simpa only [SimpleGraph.adj_comm] using drawWeight_conflict_mass G S u
  calc
    _ = (∑ iw : I × V, drawWeight G S iw.1 iw.2) -
        SelectionThinning.eventMass (fun iw : I × V => drawWeight G S iw.1 iw.2)
          (fun iw => G.graph.Adj iw.2 u) -
        SelectionThinning.eventMass (fun iw : I × V => drawWeight G S iw.1 iw.2)
          (fun iw => iw.1 = G.slot u) := by
      unfold SelectionThinning.eventMass
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro iw _
      by_cases ha : G.graph.Adj iw.2 u <;> by_cases hi : iw.1 = G.slot u
      · have hz := drawWeight_eq_zero_of_same_slot_conflict G S hwithin iw.1 iw.2 u hi ha
        rw [hi] at hz
        simp [ha, hi, hz]
      all_goals simp [ha, hi]
    _ = _ := by
      rw [drawWeight_pair_sum G S hS hdom, hbad, drawWeight_slot_mass G S hS hdom _ hu]

lemma performed_post_survival_mass_le (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (hp : Precheck p q t G S)
    (hwithin : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (u : V) (hu : u ∈ currentVertices G S) :
    (∑ r : Noise I V, if u ∈ (update G S r.1 r.2.1 r.2.2).alive then
      noiseWeight p q G S r else 0) ≤
      (1 - p.alpha q) * (1 - (S.remaining.card : ℝ)⁻¹) := by
  have hslot : G.slot u ∈ S.remaining := (Finset.mem_filter.mp hu).2
  have hs := SelectionThinning.surviving_event_mass
    (fun iw : I × V => drawWeight G S iw.1 iw.2) (thinningRate p q G S)
    (fun iw => ¬ G.graph.Adj iw.2 u ∧ iw.1 ≠ G.slot u) u
  rw [drawWeight_survives_slot_mass G S hp.1
    (fun i hi => (hp.2.2.2.1 i hi).1) hwithin u hslot] at hs
  have hrate : thinningRate p q G S u =
      SelectionThinning.thinningRate (p.alpha q) (hazard G S u) := by
    simp [thinningRate, hu, SelectionThinning.thinningRate]
  have heq := SelectionThinning.equal_survival (α := p.alpha q)
    (lt_of_le_of_lt (hp.2.2.2.2 u hu) hp.2.2.1)
  rw [← hrate] at heq
  have hmir := (thinningRate_bounds_of_precheck p q t G S hp u).2
  have hmul : 0 ≤ (S.remaining.card : ℝ)⁻¹ *
      (p.alpha q - thinningRate p q G S u) := mul_nonneg (by positivity) (sub_nonneg.mpr hmir)
  have hbound : (1 - hazard G S u - (S.remaining.card : ℝ)⁻¹) *
      (1 - thinningRate p q G S u) ≤
      (1 - p.alpha q) * (1 - (S.remaining.card : ℝ)⁻¹) := by nlinarith
  have hfinal := hs.trans_le hbound
  simp only [Noise, Fintype.sum_prod_type] at hfinal ⊢
  convert hfinal using 1
  apply Finset.sum_congr (by ext; simp)
  intro i _
  apply Finset.sum_congr (by ext; simp)
  intro w _
  apply Finset.sum_congr (by ext; simp)
  intro flags _
  have hm : u ∈ (update G S i w flags).alive ↔
      (¬ G.graph.Adj w u ∧ i ≠ G.slot u) ∧ flags u = false := by
    simp [update, survivors, hu, ne_comm, and_comm, and_assoc]
  simp only [hm]
  by_cases he : (¬ G.graph.Adj w u ∧ i ≠ G.slot u) ∧ flags u = false <;>
    simp [he, noiseWeight, SelectionThinning.jointMass, flagsWeight_eq_thinningMass]

lemma performed_count_eq_sum (p : Parameters) (q : ℕ) (G : Input I V)
    (S : State I V) (C : Finset V) (A : Noise I V → Finset V) :
    (∑ r : Noise I V, noiseWeight p q G S r * ((C ∩ A r).card : ℝ)) =
      ∑ u ∈ C, ∑ r : Noise I V, if u ∈ A r then noiseWeight p q G S r else 0 := by
  calc
    _ = ∑ r : Noise I V, ∑ u ∈ C,
        if u ∈ A r then noiseWeight p q G S r else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      have hfilter : C ∩ A r = C.filter (fun u => u ∈ A r) := by ext; simp
      rw [hfilter, ← Finset.sum_boole (fun u => u ∈ A r) C, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      by_cases h : u ∈ A r <;> simp [h]
    _ = _ := Finset.sum_comm

lemma performed_survivor_count (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (hp : Precheck p q t G S) (C : Finset V)
    (hC : C ⊆ currentVertices G S) :
    (∑ r : Noise I V, noiseWeight p q G S r *
      ((C ∩ survivors G S r.2.1 r.2.2).card : ℝ)) =
        (1 - p.alpha q) * C.card := by
  rw [performed_count_eq_sum]
  calc
    _ = ∑ _u ∈ C, (1 - p.alpha q) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact performed_survival_mass p q t G S hp u (hC hu)
    _ = _ := by simp [mul_comm]; ring

lemma performed_alive_count_le (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (hp : Precheck p q t G S)
    (hwithin : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (C : Finset V) (hC : C ⊆ currentVertices G S) :
    (∑ r : Noise I V, noiseWeight p q G S r *
      ((C ∩ (update G S r.1 r.2.1 r.2.2).alive).card : ℝ)) ≤
        (1 - p.alpha q) * (1 - (S.remaining.card : ℝ)⁻¹) * C.card := by
  rw [performed_count_eq_sum]
  calc
    _ ≤ ∑ _u ∈ C, ((1 - p.alpha q) * (1 - (S.remaining.card : ℝ)⁻¹)) := by
      apply Finset.sum_le_sum
      intro u hu
      exact performed_post_survival_mass_le p q t G S hp hwithin u (hC hu)
    _ = _ := by simp [mul_comm]

omit [Fintype I] [Fintype V] in
lemma currentVertices_update (G : Input I V) (S : State I V) (i : I)
    (w : V) (flags : V → Bool) :
    currentVertices G (update G S i w flags) = (update G S i w flags).alive := by
  ext u
  simp only [currentVertices, update, Finset.mem_filter, survivors, Finset.mem_erase]
  aesop

lemma performed_degree_le (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (hp : Precheck p q t G S)
    (hwithin : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) (v : V) :
    (∑ r : Noise I V, noiseWeight p q G S r *
      (degree G (update G S r.1 r.2.1 r.2.2) v : ℝ)) ≤
        (1 - p.alpha q) * (1 - (S.remaining.card : ℝ)⁻¹) * degree G S v := by
  have h := performed_alive_count_le p q t G S hp hwithin
    (neighbors G v ∩ currentVertices G S) Finset.inter_subset_right
  convert h using 1
  apply Finset.sum_congr rfl
  intro r _
  congr 2
  unfold degree
  rw [currentVertices_update]
  congr 1
  ext u
  simp only [Finset.mem_inter, update, Finset.mem_filter, survivors]
  aesop
  all_goals rfl

omit [Fintype I] [Fintype V] in
lemma domain_subset_currentVertices (G : Input I V) (S : State I V)
    (i : I) (hi : i ∈ S.remaining) : domain G S i ⊆ currentVertices G S := by
  intro u hu
  rcases Finset.mem_filter.mp hu with ⟨hu, hslot⟩
  exact Finset.mem_filter.mpr ⟨hu, hslot ▸ hi⟩

lemma performed_domain_size (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (hp : Precheck p q t G S) (i : I) (hi : i ∈ S.remaining) :
    (∑ r : Noise I V, noiseWeight p q G S r *
      ((domain G S i ∩ survivors G S r.2.1 r.2.2).card : ℝ)) =
        (1 - p.alpha q) * (domain G S i).card :=
  performed_survivor_count p q t G S hp (domain G S i)
    (domain_subset_currentVertices G S i hi)

end
end Balanced.Selection.Process

end OAI
