import OAI.Probability.SLE.Gauge.CoverLimits

namespace OAI

/-! Finite spatial selection and adapted failure accounting for the dense cover. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

/-- Extract disjoint candidate disks whose fourfold enlargements cover all
candidates, and charge their complete covering cost to one measure. -/
theorem select_disjoint_candidates_and_charge
    {ι : Type*} (I : Finset ι) (x : ι → ℂ) (r : ι → ℝ)
    (R : ℝ) (hr : ∀ i ∈ I, r i ≤ R)
    (ν : Measure ℂ) (A : Set ℂ)
    (hA : ∀ i ∈ I, closedBall (x i) (r i) ⊆ A)
    (cost : ι → ℝ≥0∞) (C : ℝ≥0∞)
    (hcost : ∀ i ∈ I, cost i ≤ C * ν (closedBall (x i) (r i))) :
    ∃ J : Finset ι, J ⊆ I ∧
      (J : Set ι).PairwiseDisjoint (fun i => closedBall (x i) (r i)) ∧
      (∀ i ∈ I, ∃ j ∈ J,
        closedBall (x i) (r i) ⊆ closedBall (x j) (4 * r j)) ∧
      ∑ j ∈ J, cost j ≤ C * ν A := by
  classical
  obtain ⟨u, hu, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
      (I : Set ι) x r R hr 4 (by norm_num)
  have hfin : u.Finite := I.finite_toSet.subset hu
  refine ⟨hfin.toFinset, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact hu (hfin.mem_toFinset.mp hj)
  · simpa only [hfin.coe_toFinset] using hdisj
  · intro i hi
    obtain ⟨j, hj, hij⟩ := hcover i hi
    exact ⟨j, hfin.mem_toFinset.mpr hj, hij⟩
  · apply disjoint_cover_charge hfin.toFinset ν
      (fun i => closedBall (x i) (r i)) A
      (by simpa only [hfin.coe_toFinset] using hdisj)
      (fun _ _ => isClosed_closedBall.measurableSet)
    · intro j hj
      exact hA j (hu (hfin.mem_toFinset.mp hj))
    · intro j hj
      exact hcost j (hu (hfin.mem_toFinset.mp hj))

/-- Candidate-containing cells and the remaining visited cells together form
an actual cover after disjoint spatial selection. -/
theorem selected_and_missed_cover
    {ι η : Type*} (I J : Finset ι) (M : Finset η)
    (D V : ι → Set ℂ) (Q : η → Set ℂ) (E : Set ℂ)
    (hselect : ∀ i ∈ I, ∃ j ∈ J, D i ⊆ V j)
    (hcell : ∀ z ∈ E, (∃ i ∈ I, z ∈ D i) ∨ ∃ k ∈ M, z ∈ Q k) :
    E ⊆ (⋃ j ∈ J, V j) ∪ ⋃ k ∈ M, Q k := by
  intro z hz
  rcases hcell z hz with ⟨i, hi, hzi⟩ | ⟨k, hk, hzk⟩
  · obtain ⟨j, hj, hij⟩ := hselect i hi
    exact Or.inl (mem_iUnion₂.mpr ⟨j, hj, hij hzi⟩)
  · exact Or.inr (mem_iUnion₂.mpr ⟨k, hk, hzk⟩)

/-- Repeated adapted tests require conditional success bounds, with no
independence assumption. All previous failures form a measurable past event. -/
theorem adapted_failures_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℕ mΩ) (failure : ℕ → Set Ω)
    (hmeas : ∀ n, MeasurableSet[F (n + 1)] (failure n))
    (q : ℝ≥0∞)
    (hstep : ∀ n (B : Set Ω), MeasurableSet[F n] B →
      P (B ∩ failure n) ≤ q * P B) :
    ∀ N : ℕ, P (⋂ n ∈ Finset.range N, failure n) ≤ q ^ N * P univ := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    let B : Set Ω := ⋂ n ∈ Finset.range N, failure n
    have hB : MeasurableSet[F N] B := by
      apply MeasurableSet.iInter
      intro n
      apply MeasurableSet.iInter
      intro hn
      exact (F.mono (Nat.succ_le_of_lt (Finset.mem_range.mp hn))) _ (hmeas n)
    have he : (⋂ n ∈ Finset.range (N + 1), failure n) = B ∩ failure N := by
      ext ω
      simp only [mem_iInter, Finset.mem_range, mem_inter_iff, B]
      constructor
      · intro hω
        exact ⟨fun n hn => hω n (Nat.lt_succ_of_lt hn), hω N (Nat.lt_succ_self N)⟩
      · rintro ⟨hω, hN⟩ n hn
        rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | rfl
        · exact hω n hn
        · exact hN
    rw [he, pow_succ]
    calc
      P (B ∩ failure N) ≤ q * P B := hstep N B hB
      _ ≤ q * (q ^ N * P univ) := mul_le_mul' le_rfl ih
      _ = q ^ N * q * P univ := by ac_rfl

end SLEExactGauge

end

end OAI
