import OAI.Probability.SpanningForest.EdgeAction

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336

def withinRadius (G : GraphCode) : ℕ → ℕ → ℕ → Prop
  | 0, u, v => u = v
  | n + 1, u, v => withinRadius G n u v ∨
      ∃ w, withinRadius G n u w ∧ Adj G w v

@[simp] theorem withinRadius_zero (G : GraphCode) (u v : ℕ) :
    withinRadius G 0 u v ↔ u = v := Iff.rfl

theorem withinRadius_succ (G : GraphCode) (n u v : ℕ) :
    withinRadius G (n + 1) u v ↔ withinRadius G n u v ∨
      ∃ w, withinRadius G n u w ∧ Adj G w v := Iff.rfl

theorem withinRadius_mono {G : GraphCode} {n m u v : ℕ}
    (hnm : n ≤ m) (h : withinRadius G n u v) : withinRadius G m u v := by
  induction hnm with
  | refl => exact h
  | step hnm ih => exact Or.inl ih

@[simp] theorem withinRadius_refl (G : GraphCode) (n u : ℕ) :
    withinRadius G n u u :=
  withinRadius_mono (Nat.zero_le n) rfl

theorem withinRadius_reachable {G : GraphCode} {n u v : ℕ}
    (h : withinRadius G n u v) :
    Relation.ReflTransGen (Adj G) u v := by
  induction n generalizing v with
  | zero => exact (withinRadius_zero G u v).mp h ▸ Relation.ReflTransGen.refl
  | succ n ih =>
      rcases h with h | ⟨w, hw, hwv⟩
      · exact ih h
      · exact (ih hw).tail hwv

theorem exists_withinRadius_of_reachable {G : GraphCode} {u v : ℕ}
    (h : Relation.ReflTransGen (Adj G) u v) :
    ∃ n, withinRadius G n u v := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail huv hvw ih =>
      rcases ih with ⟨n, hn⟩
      exact ⟨n + 1, Or.inr ⟨_, hn, hvw⟩⟩

theorem reachable_iff_exists_withinRadius (G : GraphCode) (u v : ℕ) :
    Relation.ReflTransGen (Adj G) u v ↔ ∃ n, withinRadius G n u v :=
  ⟨exists_withinRadius_of_reachable, fun ⟨_, hn⟩ => withinRadius_reachable hn⟩

theorem exists_withinRadius (G : GraphCode) (hG : GraphConnected G) (u v : ℕ) :
    ∃ n, withinRadius G n u v :=
  exists_withinRadius_of_reachable (hG u v)

theorem finite_withinRadius (G : GraphCode) (hG : GraphLocallyFinite G)
    (n u : ℕ) : Set.Finite {v | withinRadius G n u v} := by
  induction n with
  | zero => simp [withinRadius]
  | succ n ih =>
      have hf := ih.biUnion (fun w _ => hG w)
      convert ih.union hf using 1
      ext v
      simp [withinRadius]

theorem measurableSet_adj (u v : ℕ) :
    MeasurableSet {G : GraphCode | Adj G u v} := by
  exact measurableSet_eq_fun
    ((measurable_pi_apply v).comp ((measurable_pi_apply u).comp measurable_subtype_coe))
    measurable_const

theorem measurableSet_withinRadius (n u v : ℕ) :
    MeasurableSet {G : GraphCode | withinRadius G n u v} := by
  induction n generalizing u v with
  | zero =>
      by_cases h : u = v <;> simp [withinRadius, h]
  | succ n ih =>
      simp only [withinRadius, Set.ofPred_or, Set.ofPred_exists, Set.ofPred_and]
      exact (ih u v).union (MeasurableSet.iUnion fun w =>
        (ih u w).inter (measurableSet_adj w v))

@[simp] theorem withinRadius_relabel (σ : Equiv ℕ ℕ) (G : GraphCode)
    (n u v : ℕ) :
    withinRadius (relabelGraph σ G) n (σ u) (σ v) ↔ withinRadius G n u v := by
  induction n generalizing u v with
  | zero => simp [withinRadius]
  | succ n ih =>
      simp only [withinRadius_succ, ih]
      constructor
      · rintro (h | ⟨w, hw, hwv⟩)
        · exact Or.inl h
        · right
          refine ⟨σ.symm w, ?_, ?_⟩
          · simpa using (ih u (σ.symm w)).mp (by simpa using hw)
          · simpa [Adj, relabelGraph] using hwv
      · rintro (h | ⟨w, hw, hwv⟩)
        · exact Or.inl h
        · right
          exact ⟨σ w, (ih u w).mpr hw, by simpa [Adj, relabelGraph] using hwv⟩

def edgeBall (G : GraphCode) (n : ℕ) (e : EdgeCode) : Set ℕ :=
  {v | withinRadius G n e.val.1 v ∨ withinRadius G n e.val.2 v}

theorem finite_edgeBall (G : GraphCode) (hG : GraphLocallyFinite G)
    (n : ℕ) (e : EdgeCode) : (edgeBall G n e).Finite :=
  (finite_withinRadius G hG n e.val.1).union
    (finite_withinRadius G hG n e.val.2)

theorem edgeBall_mono (G : GraphCode) (e : EdgeCode) {n m : ℕ} (h : n ≤ m) :
    edgeBall G n e ⊆ edgeBall G m e := by
  intro v hv
  exact hv.imp (withinRadius_mono h) (withinRadius_mono h)

theorem measurableSet_mem_edgeBall (n v : ℕ) (e : EdgeCode) :
    MeasurableSet {G : GraphCode | v ∈ edgeBall G n e} :=
  (measurableSet_withinRadius n e.val.1 v).union
    (measurableSet_withinRadius n e.val.2 v)

theorem mem_edgeBall_mkEdge (G : GraphCode) (n u v w : ℕ) (h : u ≠ v) :
    w ∈ edgeBall G n (mkEdge u v h) ↔
      withinRadius G n u w ∨ withinRadius G n v w := by
  unfold edgeBall mkEdge
  split_ifs <;> simp only [Set.mem_ofPred_eq]; tauto

@[simp] theorem mem_edgeBall_mapEdge (σ : Equiv ℕ ℕ) (G : GraphCode)
    (n v : ℕ) (e : EdgeCode) :
    σ v ∈ edgeBall (relabelGraph σ G) n (mapEdge σ e) ↔ v ∈ edgeBall G n e := by
  unfold mapEdge
  rw [mem_edgeBall_mkEdge]
  simp only [withinRadius_relabel]
  rfl

theorem edgeBall_relabel (σ : Equiv ℕ ℕ) (G : GraphCode)
    (n : ℕ) (e : EdgeCode) :
    edgeBall (relabelGraph σ G) n (mapEdge σ e) = σ '' edgeBall G n e := by
  ext v
  constructor
  · intro hv
    refine ⟨σ.symm v, ?_, by simp⟩
    exact (mem_edgeBall_mapEdge σ G n (σ.symm v) e).mp (by simpa using hv)
  · rintro ⟨w, hw, rfl⟩
    exact (mem_edgeBall_mapEdge σ G n w e).mpr hw

theorem exists_mem_edgeBall (G : GraphCode) (hG : GraphConnected G)
    (e : EdgeCode) (v : ℕ) : ∃ n, v ∈ edgeBall G n e := by
  rcases exists_withinRadius G hG e.val.1 v with ⟨n, hn⟩
  exact ⟨n, Or.inl hn⟩

theorem measurable_edgeBall (n : ℕ) (e : EdgeCode) :
    Measurable (fun G : GraphCode => edgeBall G n e) := by
  exact Measurable.of_eval fun v =>
    measurableSet_setOfPred.mp (measurableSet_mem_edgeBall n v e)

theorem measurable_edgeBall_joint :
    Measurable (fun q : GraphCode × (ℕ × EdgeCode) => edgeBall q.1 q.2.1 q.2.2) :=
  measurable_from_prod_countable_left fun ne => measurable_edgeBall ne.1 ne.2

def finiteSetCode (s : Set ℕ) : Finset ℕ := by
  classical
  exact if hs : s.Finite then hs.toFinset else ∅

@[simp] theorem finiteSetCode_of_finite (s : Set ℕ) (hs : s.Finite) :
    finiteSetCode s = hs.toFinset := by
  simp [finiteSetCode, hs]

theorem finiteSetCode_eq_iff (s : Set ℕ) (t : Finset ℕ) :
    finiteSetCode s = t ↔ s = (t : Set ℕ) ∨ (t = ∅ ∧ ¬s.Finite) := by
  classical
  by_cases hs : s.Finite
  · simp only [finiteSetCode, hs, not_true_eq_false, and_false, or_false]
    rw [← Finset.coe_inj]
    simp
  · have hne : s ≠ (t : Set ℕ) := fun h => hs (h ▸ t.finite_toSet)
    simp [finiteSetCode, hs, hne, eq_comm]

theorem measurable_finiteSetCode : Measurable finiteSetCode := by
  have hf (t : Finset ℕ) : MeasurableSet {s : Set ℕ | finiteSetCode s = t} := by
    simp only [finiteSetCode_eq_iff]
    exact ((measurable_id.eq_const (t : Set ℕ)).or
      (measurable_const.and (measurableSet_setOfPred.mp
        Set.Countable.ofPred_finite.measurableSet).not)).setOf
  exact measurable_to_countable fun s => hf (finiteSetCode s)

def edgeBallCode (G : GraphCode) (n : ℕ) (e : EdgeCode) : Finset ℕ :=
  finiteSetCode (edgeBall G n e)

theorem measurable_edgeBallCode :
    Measurable (fun q : GraphCode × (ℕ × EdgeCode) => edgeBallCode q.1 q.2.1 q.2.2) :=
  measurable_finiteSetCode.comp measurable_edgeBall_joint

@[simp] theorem mem_edgeBallCode (G : GraphCode) (hG : GraphLocallyFinite G)
    (n v : ℕ) (e : EdgeCode) : v ∈ edgeBallCode G n e ↔ v ∈ edgeBall G n e := by
  simp [edgeBallCode, finiteSetCode, finite_edgeBall G hG n e]

theorem finiteSetCode_image (σ : Equiv ℕ ℕ) (s : Set ℕ) :
    finiteSetCode (σ '' s) = (finiteSetCode s).image σ := by
  classical
  by_cases hs : s.Finite
  · rw [finiteSetCode_of_finite s hs,
      finiteSetCode_of_finite (σ '' s) (hs.image σ)]
    exact hs.toFinset_image σ (hs.image σ)
  · have hi : ¬(σ '' s).Finite := fun h => hs (h.of_finite_image σ.injective.injOn)
    simp [finiteSetCode, hs, hi]

theorem edgeBallCode_relabel (σ : Equiv ℕ ℕ) (G : GraphCode)
    (n : ℕ) (e : EdgeCode) :
    edgeBallCode (relabelGraph σ G) n (mapEdge σ e) = (edgeBallCode G n e).image σ := by
  unfold edgeBallCode
  rw [edgeBall_relabel, finiteSetCode_image]

end Problem336

end

end OAI
