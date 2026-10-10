import OAI.Probability.SwitchChain.DisjointIndicators

namespace OAI

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Problem315.FiniteEventVectors

variable {Ω : Type*} [Fintype Ω] [sectionDecidableEqΩ : DecidableEq Ω]

def probability (s : Finset Ω) : ℝ := (s.card : ℝ) / Fintype.card Ω

def rawIndicator (s : Finset Ω) : EuclideanSpace ℝ Ω :=
  WithLp.toLp 2 (fun x => if x ∈ s then 1 else 0)

def eventVector (s : Finset Ω) : EuclideanSpace ℝ Ω :=
  (Real.sqrt (Fintype.card Ω : ℝ))⁻¹ • rawIndicator s

def constantVector : EuclideanSpace ℝ Ω := eventVector Finset.univ

theorem inner_rawIndicator_right (f : EuclideanSpace ℝ Ω) (s : Finset Ω) :
    ⟪f, rawIndicator s⟫ = ∑ x ∈ s, f x := by
  classical
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, rawIndicator,
    star_trivial]
  change (∑ x : Ω, (if x ∈ s then (1 : ℝ) else 0) * f x) = _
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem inner_eventVector_right (f : EuclideanSpace ℝ Ω) (s : Finset Ω) :
    ⟪f, eventVector s⟫ = (∑ x ∈ s, f x) / Real.sqrt (Fintype.card Ω : ℝ) := by
  rw [eventVector, real_inner_smul_right, inner_rawIndicator_right]
  simp only [div_eq_mul_inv, mul_comm]

theorem inner_constantVector_right (f : EuclideanSpace ℝ Ω) :
    ⟪f, constantVector⟫ = (∑ x : Ω, f x) / Real.sqrt (Fintype.card Ω : ℝ) :=
  inner_eventVector_right f Finset.univ

theorem inner_normalizedFlag_right (f : EuclideanSpace ℝ Ω) (s : Finset Ω) :
    ⟪f, DisjointIndicators.normalizedFlag constantVector (eventVector s) (probability s)⟫ =
      ((∑ x ∈ s, f x) - probability s * ∑ x : Ω, f x) /
        (Real.sqrt (Fintype.card Ω : ℝ) *
          Real.sqrt (probability s * (1 - probability s))) := by
  rw [DisjointIndicators.normalizedFlag, real_inner_smul_right, inner_sub_right,
    real_inner_smul_right, inner_eventVector_right, inner_constantVector_right]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem inner_rawIndicator (s t : Finset Ω) :
    ⟪rawIndicator s, rawIndicator t⟫ = ((s ∩ t).card : ℝ) := by
  classical
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    rawIndicator, star_trivial]
  have hpoint (x : Ω) :
      (if x ∈ t then (1 : ℝ) else 0) * (if x ∈ s then 1 else 0) =
        if x ∈ s ∩ t then 1 else 0 := by
    by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;> simp [hs, ht]
  simp_rw [hpoint]
  simp
  congr 1
  ext x
  simp

theorem inner_eventVector (s t : Finset Ω) :
    ⟪eventVector s, eventVector t⟫ = probability (s ∩ t) := by
  rw [eventVector, eventVector, real_inner_smul_left, real_inner_smul_right,
    inner_rawIndicator]
  have hs : Real.sqrt (Fintype.card Ω : ℝ) * Real.sqrt (Fintype.card Ω : ℝ) =
      (Fintype.card Ω : ℝ) := by
    simpa only [pow_two] using Real.sq_sqrt (Nat.cast_nonneg (Fintype.card Ω) :
      (0 : ℝ) ≤ Fintype.card Ω)
  rw [← mul_assoc, ← mul_inv, hs]
  simp only [probability, div_eq_mul_inv, mul_comm]

@[simp] theorem inner_eventVector_self (s : Finset Ω) :
    ⟪eventVector s, eventVector s⟫ = probability s := by
  rw [inner_eventVector, Finset.inter_self]

@[simp] theorem inner_eventVector_constant (s : Finset Ω) :
    ⟪eventVector s, constantVector⟫ = probability s := by
  rw [constantVector, inner_eventVector, Finset.inter_univ]

@[simp] theorem inner_constantVector_self [Nonempty Ω] :
    ⟪constantVector (Ω := Ω), constantVector⟫ = 1 := by
  rw [constantVector, inner_eventVector_self]
  simp only [probability, Finset.card_univ]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

theorem inner_eventVector_of_disjoint (s t : Finset Ω) (hd : Disjoint s t) :
    ⟪eventVector s, eventVector t⟫ = 0 := by
  rw [inner_eventVector, Finset.disjoint_iff_inter_eq_empty.mp hd]
  simp [probability]

include sectionDecidableEqΩ in
theorem probability_pos (s : Finset Ω) (hs : s.Nonempty) :
    0 < probability s := by
  have retainedsectionDecidableEqΩ := sectionDecidableEqΩ
  have hcard : 0 < Fintype.card Ω := by
    obtain ⟨x, hx⟩ := hs
    let : Nonempty Ω := ⟨x⟩
    exact Fintype.card_pos
  exact div_pos (by exact_mod_cast Finset.card_pos.mpr hs) (by exact_mod_cast hcard)

theorem probability_add_lt_one (s t : Finset Ω) (hd : Disjoint s t)
    (hcenter : ∃ x : Ω, x ∉ s ∧ x ∉ t) :
    probability s + probability t < 1 := by
  obtain ⟨x, hxs, hxt⟩ := hcenter
  let : Nonempty Ω := ⟨x⟩
  have hn : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos (α := Ω)
  have hlt : (s ∪ t).card < Fintype.card Ω := by
    have hproper : s ∪ t ⊂ (Finset.univ : Finset Ω) := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.subset_univ _, ?_⟩
      intro heq
      have hx : x ∈ s ∪ t := heq.symm ▸ Finset.mem_univ x
      simp [hxs, hxt] at hx
    simpa using Finset.card_lt_card hproper
  rw [Finset.card_union_of_disjoint hd] at hlt
  unfold probability
  rw [← add_div]
  apply (div_lt_one hn).mpr
  exact_mod_cast hlt

theorem normalized_events_gram (s t : Finset Ω)
    (hs : s.Nonempty) (ht : t.Nonempty) (hd : Disjoint s t)
    (hcenter : ∃ x : Ω, x ∉ s ∧ x ∉ t) :
    let e := constantVector (Ω := Ω)
    let u := DisjointIndicators.normalizedFlag e (eventVector s) (probability s)
    let v := DisjointIndicators.normalizedFlag e (eventVector t) (probability t)
    let c := DisjointIndicators.correlation (probability s) (probability t)
    ⟪e, e⟫ = 1 ∧ ⟪u, u⟫ = 1 ∧ ⟪v, v⟫ = 1 ∧
      ⟪u, e⟫ = 0 ∧ ⟪v, e⟫ = 0 ∧ ⟪u, v⟫ = c ∧ 1 - c ^ 2 ≠ 0 := by
  obtain ⟨x, hx⟩ := hs
  let : Nonempty Ω := ⟨x⟩
  have hp := probability_pos s ⟨x, hx⟩
  have hq := probability_pos t ht
  have hpq := probability_add_lt_one s t hd hcenter
  have hg := DisjointIndicators.normalized_flags_gram
    (constantVector (Ω := Ω)) (eventVector s) (eventVector t)
    (probability s) (probability t) hp hq hpq
    inner_constantVector_self (inner_eventVector_constant s) (inner_eventVector_self s)
    (inner_eventVector_constant t) (inner_eventVector_self t)
    (inner_eventVector_of_disjoint s t hd)
  exact ⟨inner_constantVector_self, hg.1, hg.2.1,
    DisjointIndicators.normalizedFlag_centered _ _ _ inner_constantVector_self
      (inner_eventVector_constant s),
    DisjointIndicators.normalizedFlag_centered _ _ _ inner_constantVector_self
      (inner_eventVector_constant t), hg.2.2.1, hg.2.2.2⟩

end Problem315.FiniteEventVectors

end

end OAI
