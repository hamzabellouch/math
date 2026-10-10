import OAI.Combinatorics.ThinTrees.ExtractionLimit

namespace OAI

section

noncomputable section
open Finset Matrix
open scoped MatrixOrder
namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
lemma treePackable_edgeConnected {r : ℕ} (hp : G.TreePackable univ r) : G.EdgeConnected r := by
  have hh := G.packableOn_edgeConnectedReal ((G.packableOn_univ univ r).mpr hp)
  intro S hS hS'
  have hs : S ⊂ (univ : Finset (Fin n)) := Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _,hS'⟩
  have hc := hh S hS hs
  have hi : G.inducedEdges univ = univ := by ext e; simp [mem_inducedEdges]
  rw [hi] at hc
  exact_mod_cast hc

lemma packable_of_parts_le_one (hn : 0 < n) {F : Finset (Fin m)} {q : ℕ}
    (hc : (G.packingParts F q).card ≤ 1) : G.TreePackable F q := by
  classical
  have hne : (G.packingParts F q).Nonempty :=
    ⟨G.partOf F q ⟨0,hn⟩,mem_filter.mpr ⟨mem_univ _,(G.partOf_spec F q ⟨0,hn⟩).2⟩⟩
  have hc1 : (G.packingParts F q).card=1 := by have := card_pos.mpr hne; omega
  obtain ⟨A,hA⟩ := card_eq_one.mp hc1
  have hh := (G.packingParts_partition F q).2.2
  rw [hA] at hh
  have hAu : A = univ := by simpa using hh
  apply (G.packableOn_univ F q).mp
  rw [hA] at hne
  have hp := ((G.packingParts_partition F q).1 A (hA ▸ mem_singleton_self A)).2
  simpa only [hAu] using hp

lemma consistent_packable (hn : 0 < n) {r q : ℕ} (hqp : 0 < q)
    (hp : G.TreePackable univ r) {X : Matrix (Fin n) (Fin n) ℝ} {t δ s : ℝ}
    (hst : 2*t < s) (hnum : (q:ℝ) < (1-2*δ)*r)
    (hcount : (((G.thresholdCrossing q X s).filter (fun e => 2*t < G.resistance X e)).card:ℝ) ≤
      2*δ*(G.thresholdCrossing q X s).card) :
    G.TreePackable (G.thresholdEdges (G.resistance X) s) q := by
  classical
  let F := G.thresholdEdges (G.resistance X) s
  let p := G.partLabel F q
  let B := G.crossing univ p
  by_contra hnot
  have hd : 1 < (G.packingParts F q).card := by
    by_contra hh
    exact hnot (G.packable_of_parts_le_one hn (F:=F) (q:=q) (by omega))
  have hupper := G.packingParts_crossing_lt hqp hd
  have hlower := G.partition_criterion_necessary hn hp p
  rw [G.partLabel_size] at hlower
  let Bad := B.filter (fun e => 2*t < G.resistance X e)
  let Good := B.filter (fun e => ¬(2*t < G.resistance X e))
  have hsub : Good ⊆ G.crossing F p := by
    intro e he
    obtain ⟨heB,heR⟩ := mem_filter.mp he
    refine mem_filter.mpr ⟨?_,(mem_filter.mp heB).2⟩
    exact mem_filter.mpr ⟨mem_univ _,(le_of_not_gt heR).trans hst.le⟩
  have hsum : Bad.card+Good.card=B.card := card_filter_add_card_filter_not _
  have hrate : 0 < 1-2*δ := by
    have hr : (0:ℝ) ≤ r := Nat.cast_nonneg _
    have hq : (0:ℝ) ≤ q := Nat.cast_nonneg _
    nlinarith
  have hMR : (r:ℝ)*((G.packingParts F q).card-1:ℕ) ≤ (B.card:ℝ) := by
    exact_mod_cast hlower
  have hpos : (0:ℝ) < ((G.packingParts F q).card-1:ℕ) := by
    exact_mod_cast (show 0 < (G.packingParts F q).card-1 by omega)
  have hm := mul_le_mul_of_nonneg_left hMR hrate.le
  have hstrict := mul_lt_mul_of_pos_right hnum hpos
  have hGood : (Good.card:ℝ) ≤ (G.crossing F p).card := by exact_mod_cast card_le_card hsub
  have hu : ((G.crossing F p).card:ℝ) < (q:ℝ)*((G.packingParts F q).card-1:ℕ) := by exact_mod_cast hupper
  have hs : (Bad.card:ℝ)+(Good.card:ℝ)=B.card := by exact_mod_cast hsum
  change (Bad.card:ℝ) ≤ 2*δ*B.card at hcount
  nlinarith

theorem extraction_from_response_threshold {qH : ℕ} (hqH : 2 ≤ qH)
    (hresp : ∀q : ℕ, qH ≤ q → ∀(n m : ℕ) (G : MultiGraph n m), 0 < n →
      G.TreePackable univ q → ∀(R : Fin m → ℝ) (t : ℝ), 0 < t →
      ∃Y ∈ G.matrixDomain, ∀s : ℝ,
      (((univ.filter (fun e => t < G.resistance Y e)) ∩
        G.crossing univ (G.partLabel (G.thresholdEdges R s) q)).card:ℝ) ≤
      16*((q:ℝ)^(-31/40:ℝ)/t+1/q)*(G.crossing univ (G.partLabel (G.thresholdEdges R s) q)).card)
    (hn : 2 ≤ n) {r q : ℕ} (hqr : q ≤ r) (hq : qH ≤ q)
    (hp : G.TreePackable univ r) {t : ℝ} (ht : 0 < t)
    (hnum : (q:ℝ) < (1-2*(16*((q:ℝ)^(-31/40:ℝ)/t+1/q)))*r) :
    ∃X ∈ G.matrixDomain, G.TreePackable (G.thresholdEdges (G.resistance X) (4*t)) q := by
  classical
  have hqp : 0 < q := by omega
  have hc : G.EdgeConnected 1 := fun S hS hS' => (by omega : 1 ≤ r).trans
    (G.treePackable_edgeConnected hp S hS hS')
  obtain ⟨X,hX,hconsistent⟩ := G.response_limit hn hc q ht (fun X _ =>
    hresp q hq n m G (by omega) (G.treePackable_mono_count hqr hp) (G.resistance X) t ht)
  obtain ⟨s,hs,havoid⟩ := (Set.Ioo_infinite (show 3*t < 4*t by linarith)).exists_notMem_finite
    (Set.finite_range (G.resistance X))
  have ha : ∀e, G.resistance X e ≠ s := fun e he => havoid ⟨e,he⟩
  have hpF := G.consistent_packable (by omega) hqp hp (by linarith [hs.1] : 2*t < s) hnum (hconsistent s ha)
  refine ⟨X,hX,G.treePackable_mono_edges ?_ hpF⟩
  intro e he
  exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp he).2.trans hs.2.le⟩

end StrongThinTree.MultiGraph

end
end

end OAI
