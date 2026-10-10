import OAI.Probability.FirstPassage.Target

namespace OAI

namespace PlanarFPP

def horizontal (n : ℤ) : List Step :=
  if 0 ≤ n then List.replicate n.toNat Step.east
  else List.replicate (-n).toNat Step.west

def vertical (n : ℤ) : List Step :=
  if 0 ≤ n then List.replicate n.toNat Step.north
  else List.replicate (-n).toNat Step.south

theorem displacement_horizontal (n : ℤ) : displacement (horizontal n) = (n, 0) := by
  by_cases hn : 0 ≤ n
  · simp [horizontal, hn, displacement, Step.delta,
      Int.toNat_of_nonneg hn]
  · have hn' : 0 ≤ -n := by omega
    simp [horizontal, hn, displacement, Step.delta,
      Int.toNat_of_nonneg hn']

theorem displacement_vertical (n : ℤ) : displacement (vertical n) = (0, n) := by
  by_cases hn : 0 ≤ n
  · simp [vertical, hn, displacement, Step.delta,
      Int.toNat_of_nonneg hn]
  · have hn' : 0 ≤ -n := by omega
    simp [vertical, hn, displacement, Step.delta,
      Int.toNat_of_nonneg hn']

theorem exists_path (p q : Vertex) : ∃ ds, p + displacement ds = q := by
  refine ⟨horizontal (q.1 - p.1) ++ vertical (q.2 - p.2), ?_⟩
  rw [displacement_append, displacement_horizontal, displacement_vertical]
  ext <;> simp

theorem path_costs_nonempty (τ : Edge → ℝ) (p q : Vertex) :
    {t | ∃ ds : List Step, p + displacement ds = q ∧ pathCost τ p ds = t}.Nonempty := by
  obtain ⟨ds, hds⟩ := exists_path p q
  exact ⟨pathCost τ p ds, ds, hds, rfl⟩

theorem path_costs_bddBelow (τ : Edge → ℝ) (hτ : ∀ e, 0 ≤ τ e) (p q : Vertex) :
    BddBelow {t | ∃ ds : List Step, p + displacement ds = q ∧ pathCost τ p ds = t} := by
  refine ⟨0, ?_⟩
  rintro t ⟨ds, _, rfl⟩
  exact pathCost_nonneg hτ p ds

theorem passageTime_nonneg (τ : Edge → ℝ) (hτ : ∀ e, 0 ≤ τ e) (p q : Vertex) :
    0 ≤ passageTime τ p q := by
  apply le_csInf (path_costs_nonempty τ p q)
  rintro t ⟨ds, _, rfl⟩
  exact pathCost_nonneg hτ p ds

theorem passageTime_le_cost (τ : Edge → ℝ) (hτ : ∀ e, 0 ≤ τ e)
    (p q : Vertex) (ds : List Step) (hend : p + displacement ds = q) :
    passageTime τ p q ≤ pathCost τ p ds :=
  csInf_le (path_costs_bddBelow τ hτ p q) ⟨ds, hend, rfl⟩

theorem passageTime_self (τ : Edge → ℝ) (hτ : ∀ e, 0 ≤ τ e) (p : Vertex) :
    passageTime τ p p = 0 := by
  apply le_antisymm _ (passageTime_nonneg τ hτ p p)
  exact passageTime_le_cost τ hτ p p [] (by simp)

theorem exists_near_optimal_path (τ : Edge → ℝ) (p q : Vertex)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ds : List Step, p + displacement ds = q ∧
      pathCost τ p ds < passageTime τ p q + ε := by
  obtain ⟨t, ⟨ds, hend, hcost⟩, ht⟩ :=
    exists_lt_of_csInf_lt (path_costs_nonempty τ p q)
      (show sInf {t | ∃ ds : List Step, p + displacement ds = q ∧ pathCost τ p ds = t}
        < passageTime τ p q + ε by change passageTime τ p q < _; linarith)
  exact ⟨ds, hend, by simpa [hcost] using ht⟩

theorem passageTime_triangle (τ : Edge → ℝ) (hτ : ∀ e, 0 ≤ τ e) (p q r : Vertex) :
    passageTime τ p r ≤ passageTime τ p q + passageTime τ q r := by
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨ds, hd, hdc⟩ := exists_near_optimal_path τ p q (ε / 2) (by linarith)
  obtain ⟨es, he, hec⟩ := exists_near_optimal_path τ q r (ε / 2) (by linarith)
  have hfinish : p + displacement (ds ++ es) = r := by
    rw [displacement_append, ← add_assoc, hd, he]
  have hc := passageTime_le_cost τ hτ p r (ds ++ es) hfinish
  rw [pathCost_append, hd] at hc
  linarith

end PlanarFPP

end OAI
