import OAI.Probability.Ising.RandomCluster
import OAI.Probability.Ising.Colorings

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

/-- Independent bond part of the comparison FK weight; the cluster factor
is supplied by summing compatible fair cluster colors. -/
noncomputable def fkEdgeWeight {n m : ℕ} (G : FiniteGraph n m)
    (F : Finset (Fin n)) (ω : Finset (Fin m)) : ℝ :=
  ∏ e ∈ keptEdges G F,
    if e ∈ ω then 1 - Real.exp (-2 * G.coupling e) else Real.exp (-2 * G.coupling e)

noncomputable def jointColorWeight {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) (σ : KeptVertex F → Bool) : ℝ :=
  if Respects (comparisonSetoid G I J F ω) σ then fkEdgeWeight G F ω else 0

noncomputable def comparisonSpinWeight {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (σ : KeptVertex F → Bool) : ℝ :=
  ∑ ω ∈ (keptEdges G F).powerset, jointColorWeight G I J F ω σ

lemma sum_jointColorWeight {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) :
    (∑ σ, jointColorWeight G I J F ω σ) = fkWeight G I J F ω := by
  calc
    _ = fkEdgeWeight G F ω * ∑ σ : KeptVertex F → Bool,
        if Respects (comparisonSetoid G I J F ω) σ then 1 else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      simp only [jointColorWeight]
      split_ifs <;> simp
    _ = _ := by
      rw [sum_respects_one]
      exact mul_comm _ _

lemma sum_jointColorWeight_spin_product {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) (i j : KeptVertex F) :
    (∑ σ, jointColorWeight G I J F ω σ * spin (σ i) * spin (σ j)) =
      if (comparisonSetoid G I J F ω).r i j then fkWeight G I J F ω else 0 := by
  calc
    _ = fkEdgeWeight G F ω * ∑ σ : KeptVertex F → Bool,
        if Respects (comparisonSetoid G I J F ω) σ then spin (σ i) * spin (σ j)
        else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      simp only [jointColorWeight]
      split_ifs <;> ring
    _ = _ := by
      rw [sum_respects_spin_product]
      split_ifs
      · exact mul_comm _ _
      · exact mul_zero _

lemma sum_comparisonSpinWeight {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) :
    (∑ σ, comparisonSpinWeight G I J F σ) =
      ∑ ω ∈ (keptEdges G F).powerset, fkWeight G I J F ω := by
  unfold comparisonSpinWeight
  rw [Finset.sum_comm]
  simp only [sum_jointColorWeight]

lemma sum_comparisonSpinWeight_spin_product {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (i j : KeptVertex F) :
    (∑ σ, comparisonSpinWeight G I J F σ * spin (σ i) * spin (σ j)) =
      ∑ ω ∈ (keptEdges G F).powerset,
        if (comparisonSetoid G I J F ω).r i j then fkWeight G I J F ω else 0 := by
  unfold comparisonSpinWeight
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [sum_jointColorWeight_spin_product]

/-- Finite Edwards–Sokal color averaging after vertex deletion and separate terminal contraction. -/
lemma qZero_eq_color_correlation {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (i j : KeptVertex F) :
    qZero G I J F i j =
      (∑ σ, comparisonSpinWeight G I J F σ * spin (σ i) * spin (σ j)) /
        ∑ σ, comparisonSpinWeight G I J F σ := by
  rw [sum_comparisonSpinWeight_spin_product, sum_comparisonSpinWeight]
  rfl

lemma sum_subsets_product {E : Type*} [DecidableEq E] (s : Finset E)
    (f g : E → ℝ) :
    (∑ ω ∈ s.powerset, ∏ e ∈ s, if e ∈ ω then f e else g e) =
      ∏ e ∈ s, (f e + g e) := by
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro ω hω
  have hsub := Finset.mem_powerset.mp hω
  rw [Finset.prod_ite]
  have hf : s.filter (fun e => e ∈ ω) = ω := by
    ext e
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun he => ⟨hsub he, he⟩⟩
  have hg : s.filter (fun e => e ∉ ω) = s \ ω := by
    ext e
    simp
  rw [hf, hg]

/-- Extend a coloring from the vertex-DELETED graph. The values at deleted
vertices are immaterial: every incident edge is absent from keptEdges. -/
def extendKept {n : ℕ} (F : Finset (Fin n)) (σ : KeptVertex F → Bool) : Spins n :=
  fun v => if hv : v ∉ F then σ ⟨v, hv⟩ else false

@[simp] lemma extendKept_apply {n : ℕ} (F : Finset (Fin n))
    (σ : KeptVertex F → Bool) (v : KeptVertex F) :
    extendKept F σ v.val = σ v := by
  simp [extendKept, v.property]

def BondCompatible {n m : ℕ} (G : FiniteGraph n m)
    (F : Finset (Fin n)) (σ : KeptVertex F → Bool) (ω : Finset (Fin m)) : Prop :=
  ∀ e ∈ ω, extendKept F σ (G.left e) = extendKept F σ (G.right e)

lemma respects_comparison_iff {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) (hω : ω ⊆ keptEdges G F)
    (σ : KeptVertex F → Bool) :
    Respects (comparisonSetoid G I J F ω) σ ↔
      Respects (comparisonSetoid G I J F ∅) σ ∧ BondCompatible G F σ ω := by
  simp only [comparisonSetoid, respects_eqvGen]
  constructor
  · intro H
    constructor
    · intro u v huv
      rcases huv with hi | hj | ⟨e, he, _⟩
      · exact H u v (Or.inl hi)
      · exact H u v (Or.inr (Or.inl hj))
      · exact (Finset.notMem_empty e he).elim
    · intro e he
      have hk := (Finset.mem_filter.mp (hω he)).2
      let u : KeptVertex F := ⟨G.left e, hk.1⟩
      let v : KeptVertex F := ⟨G.right e, hk.2⟩
      have He := H u v (Or.inr (Or.inr ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩))
      simpa only [← extendKept_apply F σ u, ← extendKept_apply F σ v] using He
  · rintro ⟨H, Hω⟩ u v huv
    rcases huv with hi | hj | ⟨e, he, huv | hvu⟩
    · exact H u v (Or.inl hi)
    · exact H u v (Or.inr (Or.inl hj))
    · have He := Hω e he
      rw [huv.1, huv.2] at He
      simpa only [extendKept_apply] using He
    · have He := Hω e he
      rw [hvu.1, hvu.2] at He
      simpa only [extendKept_apply] using He.symm

lemma prod_conditioned_subset {E : Type*} [DecidableEq E] (s ω : Finset E)
    (hω : ω ⊆ s) (P : E → Prop) [DecidablePred P] (f g : E → ℝ) :
    (if ∀ e ∈ ω, P e then ∏ e ∈ s, if e ∈ ω then f e else g e else 0) =
      ∏ e ∈ s, if e ∈ ω then (if P e then f e else 0) else g e := by
  by_cases H : ∀ e ∈ ω, P e
  · rw [ite_eq_left H]
    apply Finset.prod_congr rfl
    intro e _
    by_cases he : e ∈ ω
    · simp only [he, H e he, ite_true]
    · simp only [he, ite_false]
  · rw [ite_eq_right H]
    push Not at H
    obtain ⟨e, he, hP⟩ := H
    symm
    apply Finset.prod_eq_zero (hω he)
    simp only [he, hP, ite_true, ite_false]

lemma jointColorWeight_expansion {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) (hω : ω ⊆ keptEdges G F)
    (σ : KeptVertex F → Bool) :
    jointColorWeight G I J F ω σ =
      if Respects (comparisonSetoid G I J F ∅) σ then
        ∏ e ∈ keptEdges G F, if e ∈ ω then
          (if extendKept F σ (G.left e) = extendKept F σ (G.right e)
            then 1 - Real.exp (-2 * G.coupling e) else 0)
          else Real.exp (-2 * G.coupling e)
      else 0 := by
  unfold jointColorWeight
  rw [respects_comparison_iff G I J F ω hω σ]
  by_cases H : Respects (comparisonSetoid G I J F ∅) σ
  · simp only [H, true_and, ite_true]
    have hP := prod_conditioned_subset (keptEdges G F) ω hω
      (fun e => extendKept F σ (G.left e) = extendKept F σ (G.right e))
      (fun e => 1 - Real.exp (-2 * G.coupling e))
      (fun e => Real.exp (-2 * G.coupling e))
    unfold BondCompatible fkEdgeWeight
    by_cases Hω : ∀ e ∈ ω, extendKept F σ (G.left e) = extendKept F σ (G.right e)
    · rw [ite_eq_left Hω] at hP ⊢
      exact hP
    · rw [ite_eq_right Hω] at hP ⊢
      exact hP
  · simp only [H, false_and, ite_false]

lemma comparisonSpinWeight_product {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (σ : KeptVertex F → Bool) :
    comparisonSpinWeight G I J F σ =
      if Respects (comparisonSetoid G I J F ∅) σ then
        ∏ e ∈ keptEdges G F,
          ((if extendKept F σ (G.left e) = extendKept F σ (G.right e)
            then 1 - Real.exp (-2 * G.coupling e) else 0) +
              Real.exp (-2 * G.coupling e))
      else 0 := by
  unfold comparisonSpinWeight
  by_cases H : Respects (comparisonSetoid G I J F ∅) σ
  · simp only [H, ite_true]
    calc
      _ = ∑ ω ∈ (keptEdges G F).powerset, ∏ e ∈ keptEdges G F,
          if e ∈ ω then
            (if extendKept F σ (G.left e) = extendKept F σ (G.right e)
              then 1 - Real.exp (-2 * G.coupling e) else 0)
            else Real.exp (-2 * G.coupling e) := by
        apply Finset.sum_congr rfl
        intro ω hω
        rw [jointColorWeight_expansion G I J F ω (Finset.mem_powerset.mp hω) σ]
        simp only [H, ite_true]
      _ = _ := sum_subsets_product _ _ _
  · simp only [H, ite_false]
    apply Finset.sum_eq_zero
    intro ω hω
    rw [jointColorWeight_expansion G I J F ω (Finset.mem_powerset.mp hω) σ]
    simp only [H, ite_false]

lemma es_one_edge_identity (K : ℝ) (s t : Bool) :
    ((if s = t then 1 - Real.exp (-2 * K) else 0) + Real.exp (-2 * K)) =
      Real.exp (-K) * Real.exp (K * spin s * spin t) := by
  rw [← Real.exp_add]
  cases s <;> cases t <;> simp [spin] <;> ring

noncomputable def deletedEnergy {n m : ℕ} (G : FiniteGraph n m)
    (F : Finset (Fin n)) (σ : KeptVertex F → Bool) : ℝ :=
  ∑ e ∈ keptEdges G F,
    G.coupling e * spin (extendKept F σ (G.left e)) * spin (extendKept F σ (G.right e))

/-- Zero-field Ising weight on the vertex-deleted graph, with I,J separately
contracted by restricting each to constant spin assignments. -/
noncomputable def contractedZeroWeight {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (σ : KeptVertex F → Bool) : ℝ :=
  if Respects (comparisonSetoid G I J F ∅) σ then Real.exp (deletedEnergy G F σ) else 0

lemma comparisonSpinWeight_eq_Ising {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (σ : KeptVertex F → Bool) :
    comparisonSpinWeight G I J F σ =
      Real.exp (-(∑ e ∈ keptEdges G F, G.coupling e)) * contractedZeroWeight G I J F σ := by
  rw [comparisonSpinWeight_product]
  unfold contractedZeroWeight
  split_ifs
  · simp only [es_one_edge_identity, Finset.prod_mul_distrib, ← Real.exp_sum,
      Finset.sum_neg_distrib]
    rfl
  · exact (mul_zero _).symm

/-- The zero-field FK/Ising identity with vertex deletion, separate terminal contractions, and parallel edges. -/
lemma qZero_eq_zero_field_correlation {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (i j : KeptVertex F) :
    qZero G I J F i j =
      (∑ σ, contractedZeroWeight G I J F σ * spin (σ i) * spin (σ j)) /
        ∑ σ, contractedZeroWeight G I J F σ := by
  rw [qZero_eq_color_correlation]
  simp only [comparisonSpinWeight_eq_Ising, mul_assoc, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

end BufferedIsing

end OAI
