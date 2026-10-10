import OAI.Combinatorics.MatchingEntropy.Basic

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.LooplessGraph

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def Crosses (G : LooplessGraph V E) (S : Finset V) (e : E) : Prop :=
  (G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.left e ∉ S ∧ G.right e ∈ S)

instance crossesDecidable (G : LooplessGraph V E) (S : Finset V) (e : E) :
    Decidable (G.Crosses S e) := inferInstanceAs (Decidable
      ((G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.left e ∉ S ∧ G.right e ∈ S)))

def cut (G : LooplessGraph V E) (S : Finset V) : Finset E :=
  Finset.univ.filter (G.Crosses S)

def degree (G : LooplessGraph V E) (x : E → ℝ) (v : V) : ℝ :=
  ∑ e, if G.Incident v e then x e else 0

def cutMass (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ G.cut S, x e

def constraintPolytope (G : LooplessGraph V E) : Set (E → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ (∀ v, G.degree x v = 1) ∧
    (∀ S : Finset V, Odd S.card → 1 ≤ G.cutMass x S)}

omit [Fintype V] [DecidableEq E] in
@[simp] theorem mem_cut (G : LooplessGraph V E) (S : Finset V) (e : E) :
    e ∈ G.cut S ↔ G.Crosses S e := by simp [cut]

omit [Fintype E] [DecidableEq E] in
theorem crosses_compl (G : LooplessGraph V E) (S : Finset V) (e : E) :
    G.Crosses Sᶜ e ↔ G.Crosses S e := by
  simp only [Crosses, Finset.mem_compl, not_not]
  tauto

omit [DecidableEq E] in
@[simp] theorem cut_compl (G : LooplessGraph V E) (S : Finset V) :
    G.cut Sᶜ = G.cut S := by ext; simp [crosses_compl]

omit [Fintype V] in
theorem degree_indicator (G : LooplessGraph V E) (M : G.Matching) (v : V) :
    G.degree (G.indicator M) v = 1 := by
  obtain ⟨e, ⟨he, hev⟩, huniq⟩ := M.property v
  rw [degree, Finset.sum_eq_single e]
  · simp [hev, indicator, he]
  · intro e' _ hne
    by_cases hv : G.Incident v e'
    · have hh : e' ∉ M.val := by
        intro hm
        exact hne (huniq e' ⟨hm, hv⟩)
      simp [hv, indicator, hh]
    · simp [hv]
  · simp

omit [Fintype V] in
theorem degree_mean (G : LooplessGraph V E) (p : G.Matching → ℝ) (v : V) :
    G.degree (G.mean p) v = ∑ M, p M := by
  classical
  have he : ∀ e, (if G.Incident v e then G.mean p e else 0) =
      ∑ M, p M*(if G.Incident v e then G.indicator M e else 0) := by
    intro e
    by_cases h : G.Incident v e <;> simp [h, mean]
  unfold degree
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _
  rw [← Finset.mul_sum]
  change p M*G.degree (G.indicator M) v = p M
  rw [G.degree_indicator, mul_one]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem incidence_sum (G : LooplessGraph V E) (e : E) (S : Finset V) :
    (∑ v ∈ S, if G.Incident v e then (1:ℕ) else 0) =
      (if G.left e ∈ S then 1 else 0) + (if G.right e ∈ S then 1 else 0) := by
  have hv : ∀ v, (if G.Incident v e then (1:ℕ) else 0) =
      (if v = G.left e then 1 else 0) + (if v = G.right e then 1 else 0) := by
    intro v
    by_cases hl : v = G.left e <;> by_cases hr : v = G.right e
    · exact ((G.loopless e) (hl.symm.trans hr)).elim
    · simp [Incident, hl, G.loopless e, Ne.symm (G.loopless e)]
    · simp [Incident, hr, G.loopless e, Ne.symm (G.loopless e)]
    · simp [Incident, Ne.symm hl, Ne.symm hr, hl, hr]
  simp_rw [hv, Finset.sum_add_distrib]
  simp

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem matching_incidence_count (G : LooplessGraph V E) (M : G.Matching)
    (S : Finset V) :
    (∑ e ∈ M.val, ((if G.left e ∈ S then (1:ℕ) else 0) +
      (if G.right e ∈ S then 1 else 0))) = S.card := by
  have hsum : ∀ v, (∑ e ∈ M.val, if G.Incident v e then (1:ℕ) else 0) = 1 := by
    intro v
    obtain ⟨e, ⟨he, hev⟩, hu⟩ := M.property v
    rw [Finset.sum_eq_single e]
    · simp [hev]
    · intro e' he' hh
      have hv : ¬G.Incident v e' := fun hv => hh (hu e' ⟨he', hv⟩)
      simp [hv]
    · simp [he]
  calc
    _ = ∑ e ∈ M.val, ∑ v ∈ S, if G.Incident v e then (1:ℕ) else 0 := by
      simp_rw [incidence_sum]
    _ = ∑ v ∈ S, ∑ e ∈ M.val, if G.Incident v e then (1:ℕ) else 0 := Finset.sum_comm
    _ = S.card := by simp_rw [hsum]; simp

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem matching_crosses_odd (G : LooplessGraph V E) (M : G.Matching)
    (S : Finset V) (hS : Odd S.card) : ∃ e ∈ M.val, G.Crosses S e := by
  by_contra h
  push Not at h
  have heq : ∀ e ∈ M.val, ((if G.left e ∈ S then (1:ℕ) else 0) +
      (if G.right e ∈ S then 1 else 0)) = 2*(if G.left e ∈ S then 1 else 0) := by
    intro e he
    have hc := h e he
    simp only [Crosses] at hc
    by_cases hl : G.left e ∈ S <;> by_cases hr : G.right e ∈ S <;>
      simp_all
  have hh := G.matching_incidence_count M S
  have heqsum := Finset.sum_congr rfl heq
  rw [heqsum, ← Finset.mul_sum] at hh
  obtain ⟨k, hk⟩ := hS
  omega

omit [Fintype V] [DecidableEq E] in
theorem degree_linear (G : LooplessGraph V E) (x y : E → ℝ) (a b : ℝ) (v : V) :
    G.degree (a • x+b • y) v = a*G.degree x v+b*G.degree y v := by
  have he : ∀ e, (if G.Incident v e then (a • x+b • y) e else 0) =
      a*(if G.Incident v e then x e else 0)+b*(if G.Incident v e then y e else 0) := by
    intro e
    by_cases h : G.Incident v e <;> simp [h]
  simp only [degree, he, Finset.sum_add_distrib, ← Finset.mul_sum]

omit [Fintype V] [DecidableEq E] in
theorem cutMass_linear (G : LooplessGraph V E) (x y : E → ℝ) (a b : ℝ) (S : Finset V) :
    G.cutMass (a • x+b • y) S = a*G.cutMass x S+b*G.cutMass y S := by
  simp [cutMass, Finset.sum_add_distrib, Finset.mul_sum]

omit [Fintype V] [DecidableEq E] in
theorem convex_constraintPolytope (G : LooplessGraph V E) :
    Convex ℝ G.constraintPolytope := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun e => add_nonneg (mul_nonneg ha (hx.1 e)) (mul_nonneg hb (hy.1 e)), ?_, ?_⟩
  · intro v
    rw [degree_linear, hx.2.1, hy.2.1, mul_one, mul_one, hab]
  · intro S hS
    rw [cutMass_linear]
    calc
      1 = a*1+b*1 := by linarith
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hx.2.2 S hS) ha)
        (mul_le_mul_of_nonneg_left (hy.2.2 S hS) hb)

omit [Fintype V] in
theorem indicator_mem_constraintPolytope (G : LooplessGraph V E) (M : G.Matching) :
    G.indicator M ∈ G.constraintPolytope := by
  refine ⟨?_, G.degree_indicator M, ?_⟩
  · intro e; simp [indicator]; split <;> norm_num
  · intro S hS
    obtain ⟨e, he, hc⟩ := G.matching_crosses_odd M S hS
    have h := Finset.single_le_sum (f := G.indicator M)
      (s := G.cut S) (a := e) (by intro e' _; simp [indicator]; split <;> norm_num)
      ((G.mem_cut S e).mpr hc)
    simpa only [cutMass, indicator, he, ite_true] using h

omit [Fintype V] in
theorem polytope_subset_constraintPolytope (G : LooplessGraph V E) :
    G.polytope ⊆ G.constraintPolytope := by
  apply convexHull_min
  · rintro x ⟨M, rfl⟩
    exact G.indicator_mem_constraintPolytope M
  · exact G.convex_constraintPolytope

omit [Fintype V] [DecidableEq E] in
theorem constraint_coordinate_le_one (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) (e : E) : x e ≤ 1 := by
  have h := Finset.single_le_sum (f := fun e' => if G.Incident (G.left e) e' then x e' else 0)
    (s := Finset.univ) (a := e) (by
      intro e' _; split; exact hx.1 e'; rfl) (Finset.mem_univ e)
  have he : G.Incident (G.left e) e := Or.inl rfl
  change (if G.Incident (G.left e) e then x e else 0) ≤ G.degree x (G.left e) at h
  simpa only [he, ite_true, hx.2.1] using h

omit [Fintype V] [DecidableEq E] in
theorem continuous_degree (G : LooplessGraph V E) (v : V) :
    Continuous (fun x : E → ℝ => G.degree x v) := by
  unfold degree
  apply continuous_finsetSum
  intro e _
  split <;> fun_prop

omit [Fintype V] [DecidableEq E] in
theorem continuous_cutMass (G : LooplessGraph V E) (S : Finset V) :
    Continuous (fun x : E → ℝ => G.cutMass x S) := by
  unfold cutMass
  fun_prop

omit [Fintype V] [DecidableEq E] in
theorem isClosed_constraintPolytope (G : LooplessGraph V E) :
    IsClosed G.constraintPolytope := by
  simp only [constraintPolytope, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter fun e => isClosed_le continuous_const (continuous_apply e)).inter
    ((isClosed_iInter fun v => isClosed_eq (G.continuous_degree v) continuous_const).inter
      (isClosed_iInter fun S => isClosed_iInter fun _ =>
        isClosed_le continuous_const (G.continuous_cutMass S)))

omit [Fintype V] [DecidableEq E] in
theorem isCompact_constraintPolytope (G : LooplessGraph V E) :
    IsCompact G.constraintPolytope := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : E → ℝ) 1)).of_isClosed_subset
    G.isClosed_constraintPolytope
  intro x hx
  exact ⟨hx.1, fun e => G.constraint_coordinate_le_one hx e⟩

end MatchingEntropyBounds.LooplessGraph

end

end OAI
