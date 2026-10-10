import OAI.Combinatorics.MatchingPSD.FiniteFactorization

namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing
attribute [local instance] Classical.propDecidable

noncomputable def pairingEdge {n : ℕ} (M : Pairing (Fin n)) (v : Fin n) : Edge n :=
  if h : v < M.1 v then ⟨(v,M.1 v),h⟩ else
    ⟨(M.1 v,v),lt_of_le_of_ne (le_of_not_gt h) (M.partner_ne v)⟩

lemma pairingEdge_partner {n : ℕ} (M : Pairing (Fin n)) (v : Fin n) :
    pairingEdge M (M.1 v) = pairingEdge M v := by
  by_cases h : v < M.1 v
  · simp [pairingEdge, h, M.partner_partner, not_lt.mpr h.le]
  · have h' : M.1 v < v := lt_of_le_of_ne (le_of_not_gt h) (M.partner_ne v)
    simp [pairingEdge, h, h', M.partner_partner]

lemma pairingEdge_incident {n : ℕ} (M : Pairing (Fin n)) (v : Fin n) :
    (pairingEdge M v).1.1 = v ∨ (pairingEdge M v).1.2 = v := by
  unfold pairingEdge
  split_ifs <;> simp

lemma pairingEdge_mem {n : ℕ} (M : Pairing (Fin n)) (v : Fin n) :
    M.1 (pairingEdge M v).1.1 = (pairingEdge M v).1.2 := by
  unfold pairingEdge
  split_ifs <;> simp

lemma eq_pairingEdge {n : ℕ} (M : Pairing (Fin n)) (e : Edge n) (hM : M.1 e.1.1 = e.1.2)
    (v : Fin n) (hv : e.1.1 = v ∨ e.1.2 = v) : e = pairingEdge M v := by
  have he : e = pairingEdge M e.1.1 := by
    simp only [pairingEdge, hM, e.2, dite_true]
  rcases hv with rfl | rfl
  · exact he
  · rw [← hM, pairingEdge_partner]
    exact he

noncomputable def fromPairing {n : ℕ} (M : Pairing (Fin n)) : PerfectMatching n :=
  ⟨Finset.univ.filter (fun e : Edge n => M.1 e.1.1 = e.1.2), by
    intro v
    apply Finset.card_eq_one.mpr
    refine ⟨pairingEdge M v, ?_⟩
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hM,hv⟩
      exact eq_pairingEdge M e hM v hv
    · rintro rfl
      exact ⟨pairingEdge_mem M v, pairingEdge_incident M v⟩⟩

@[simp] lemma mem_fromPairing {n : ℕ} (M : Pairing (Fin n)) (e : Edge n) :
    e ∈ (fromPairing M).1 ↔ M.1 e.1.1 = e.1.2 := by
  simp [fromPairing]

lemma pairingEdge_cross {n : ℕ} (M : Pairing (Fin n)) (U : Finset (Fin n))
    (v : Fin n) (hv : v ∈ U) (hp : M.1 v ∉ U) : Crosses U (pairingEdge M v) := by
  unfold pairingEdge
  split_ifs <;> simp [Crosses, hv, hp]

lemma cross_edge_inside {n : ℕ} (M : Pairing (Fin n)) (U : Finset (Fin n))
    (e : Edge n) (he : e ∈ (fromPairing M).1) (hc : Crosses U e) :
    ∃ v : Fin n, (v ∈ U ∧ M.1 v ∉ U) ∧ pairingEdge M v = e := by
  have hm := (mem_fromPairing M e).mp he
  rcases hc with hc | hc
  · refine ⟨e.1.1,⟨hc.1,?_⟩,(eq_pairingEdge M e hm _ (Or.inl rfl)).symm⟩
    simpa only [hm] using hc.2
  · refine ⟨e.1.2,⟨hc.2,?_⟩,(eq_pairingEdge M e hm _ (Or.inr rfl)).symm⟩
    simpa only [← hm, M.partner_partner] using hc.1

lemma pairingEdge_inside_injective {n : ℕ} (M : Pairing (Fin n)) (U : Finset (Fin n)) :
    Function.Injective (fun v : {v : Fin n // v ∈ U ∧ M.1 v ∉ U} => pairingEdge M v.1) := by
  intro v w h
  apply Subtype.ext
  have hv := pairingEdge_incident M v.1
  have hw := pairingEdge_incident M w.1
  change pairingEdge M v.1 = pairingEdge M w.1 at h
  rw [← h] at hw
  rcases hv with hv | hv <;> rcases hw with hw | hw
  · exact hv.symm.trans hw
  · have hm := pairingEdge_mem M v.1
    rw [hv,hw] at hm
    exact False.elim (v.2.2 (hm ▸ w.2.1))
  · have hm := pairingEdge_mem M v.1
    rw [hw,hv] at hm
    exact False.elim (w.2.2 (hm ▸ v.2.1))
  · exact hv.symm.trans hw

lemma crossingCount_fromPairing {n : ℕ} (M : Pairing (Fin n)) (U : Finset (Fin n)) :
    crossingCount U (fromPairing M) = Fintype.card {v : Fin n // v ∈ U ∧ M.1 v ∉ U} := by
  classical
  rw [crossingCount, ← Fintype.card_coe]
  symm
  apply Fintype.card_of_bijective (f := fun v : {v : Fin n // v ∈ U ∧ M.1 v ∉ U} =>
    (⟨pairingEdge M v.1,by simp [pairingEdge_mem, pairingEdge_cross M U v.1 v.2.1 v.2.2]⟩ :
      {e // e ∈ (fromPairing M).1.filter (Crosses U)}))
  constructor
  · intro v w h
    exact pairingEdge_inside_injective M U (congrArg Subtype.val h)
  · intro e
    obtain ⟨v,hv,he⟩ := cross_edge_inside M U e.1 (Finset.mem_filter.mp e.2).1 (Finset.mem_filter.mp e.2).2
    exact ⟨⟨v,hv⟩,Subtype.ext he⟩

lemma crossingCount_tableCoordinate {n : ℕ} (M : Pairing (Fin n)) (U : Finset (Fin n)) :
    (crossingCount U (fromPairing M) : ℝ) =
      tableCoordinate (fun v => decide (v ∈ U)) (true,false) M := by
  rw [crossingCount_fromPairing]
  simp [tableCoordinate, Fintype.card_subtype, Finset.sum_boole]

end PerfectMatchingPSD

end OAI
