import Mathlib
import OAI.Probability.Ballisticity.Estimates.WordPrefixes
import OAI.Probability.Ballisticity.Estimates.CellExhaustion

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

noncomputable def scheduledCellSuccess {d k : ℕ} (ν : Measure (Row d))
    (e f : Direction d) (hef : e.1 ≠ f.1) (a C c g₀ g₁ A : ℝ) (hc : 0 < c)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (v w m s i : ℕ) : Set (Environment d) :=
  if i < m then
    cellAttemptSuccess
      (cellSeedMass e f (a+cellOpportunity v w m i) (c*cellRadius ν e f C w m i)
        (cellWidth w m i) (cellRestart e a π v w m i))
      (cellEarlyMass e f hef (a+cellOpportunity v w m i) (c*cellRadius ν e f C w m i)
        (cellWidth w m i) (cellEarlyHeight v w m i s) (cellRestart e a π v w m i))
      (cellLateMass e f hef (a+cellOpportunity v w m i) c (cellRadius ν e f C w m i)
        hc (cellRadius_pos ν e f C w m i) (cellWidth w m i) (cellEarlyHeight v w m i s) s
        (cellLateHeight v w m i s) (cellRestart e a π v w m i)) g₀ g₁ (A*k) s (m-i)
  else ∅

lemma scheduledCellSuccess_or_failure {d k : ℕ} (ν : Measure (Row d))
    (e f : Direction d) (hef : e.1 ≠ f.1) (a C c g₀ g₁ A : ℝ) (hc : 0 < c)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (v w m s : ℕ) (hs : 0 < s)
    (i : ℕ) (hi : i < m) (ω : Environment d) :
    ω ∈ scheduledCellSuccess ν e f hef a C c g₀ g₁ A hc π v w m s i ∨
      ∃ n, 0 < n ∧ n ≤ m-i ∧ ω ∈ scheduledCellFailure ν e f hef a C c g₀ g₁ A hc π v w m s i n := by
  have hh := cell_failure_or_success
    (cellSeedMass e f (a+cellOpportunity v w m i) (c*cellRadius ν e f C w m i)
      (cellWidth w m i) (cellRestart e a π v w m i))
    (cellEarlyMass e f hef (a+cellOpportunity v w m i) (c*cellRadius ν e f C w m i)
      (cellWidth w m i) (cellEarlyHeight v w m i s) (cellRestart e a π v w m i))
    (cellLateMass e f hef (a+cellOpportunity v w m i) c (cellRadius ν e f C w m i)
      hc (cellRadius_pos ν e f C w m i) (cellWidth w m i) (cellEarlyHeight v w m i s) s
      (cellLateHeight v w m i s) (cellRestart e a π v w m i)) g₀ g₁ (A*k) s (m-i) hs (by omega) ω
  rcases hh with hh|⟨n,hn,hnm,hf⟩
  · exact Or.inl (by simpa only [scheduledCellSuccess,ite_eq_left hi] using hh)
  · exact Or.inr ⟨n,hn,hnm,by simpa only [scheduledCellFailure,ite_eq_left (show i < m ∧ 0 < n ∧ n ≤ m-i from ⟨hi,hn,hnm⟩)] using hf⟩

lemma no_cell_success_subset_exhaustion {d k : ℕ} (ν : Measure (Row d))
    (e f : Direction d) (hef : e.1 ≠ f.1) (a C c g₀ g₁ A : ℝ) (hc : 0 < c)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (v w m s : ℕ) (hs : 0 < s) :
    (⋃ i, scheduledCellSuccess ν e f hef a C c g₀ g₁ A hc π v w m s i)ᶜ ⊆
      ⋃ p : Composition m, failedOpportunityBlocks
        (scheduledCellFailure ν e f hef a C c g₀ g₁ A hc π v w m s) 0 p.blocks := by
  intro ω hω
  apply Set.mem_iUnion.mpr
  apply failed_blocks_of_no_success _
    (scheduledCellSuccess ν e f hef a C c g₀ g₁ A hc π v w m s) m
    (scheduledCellSuccess_or_failure ν e f hef a C c g₀ g₁ A hc π v w m s hs) ω
  intro i hi hS
  exact hω (Set.mem_iUnion.mpr ⟨i,hS⟩)

theorem actual_cell_no_success {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ k : ℕ, 2 ≤ k →
      ∃ C c g₀ g₁ : ℝ, 0 < C ∧ ∃ hc : 0 < c, c ≤ 1 ∧ 0 < g₀ ∧ 0 < g₁ ∧
      ∃ s : ℕ, 0 < s ∧ ∀ Bstar : ℝ, 0 < Bstar → ∃ w₀ : ℕ, 0 < w₀ ∧
      ∀ w ≥ w₀, ∀ m : ℕ, (2*A*k)*(m:ℝ) ≤ Bstar →
      ∀ v : ℕ, 2*cellWidth w m 0 ≤ v →
      ∀ (a : ℝ) (π : Environment d → LayerTupleProfile (k:=k) e a),
        @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π →
      environmentLaw ν (⋃ i, scheduledCellSuccess ν e f hef a C c g₀ g₁ A hc π v w m s i)ᶜ ≤
        (2:ℝ≥0∞)^(m-1)*ENNReal.ofReal (Real.exp (-2*k*m)) := by
  obtain ⟨A,hA,hk⟩ := actual_cell_exhaustion ν hue e f hef htrans
  refine ⟨A,hA,fun k hk₂ => ?_⟩
  obtain ⟨C,c,g₀,g₁,hC,hc,hc1,hg₀,hg₁,s,hs,hb⟩ := hk k hk₂
  refine ⟨C,c,g₀,g₁,hC,hc,hc1,hg₀,hg₁,s,hs,fun Bstar hB => ?_⟩
  obtain ⟨w₀,hw₀,hw⟩ := hb Bstar hB
  refine ⟨w₀,hw₀,fun w hww m hm v hv a π hπ => ?_⟩
  exact (measure_mono (no_cell_success_subset_exhaustion ν e f hef a C c g₀ g₁ A hc π v w m s hs)).trans
    (hw w hww m hm v hv a π hπ)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma budget_profile_prefix_certificate {d k : ℕ} (e f : Direction d)
    (a G r : ℝ) (π : BudgetProfile (k:=k) e f a G) (ω : Environment d)
    (h H : ℕ) (hh : h≤H) :
    relativeBudgetMassENN e f H r π.val ω ≤
      rawTupleMixture (realPosition (step e)) h π.val ω {y | TupleSeparated f (G-r) y} := by
  rw [relativeBudgetMassENN,rawTupleMixture_apply]
  apply lintegral_mono_ae
  filter_upwards [π.property.2] with x hx
  exact budget_prefix_certificate e f ω x h H hh G r hx.2

theorem protection_prefix_certificate {d k : ℕ} (e f : Direction d) (base G : ℝ)
    (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i,0≤r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G)
    (n h : ℕ) (hh : h≤H n) (ω : Environment d) :
    (∏ i∈Finset.range (n+1),ENNReal.ofReal (protectionMass e f base G H r hr π i ω)) ≤
      rawTupleMixture (realPosition (step e)) ((∑ i∈Finset.range n,H i)+h) (π ω).val ω
        {y | TupleSeparated f (protectionGap G r n-r n) y} := by
  let c := ∏ i∈Finset.range n,ENNReal.ofReal (protectionMass e f base G H r hr π i ω)
  let p := protectionProfile e f base G H r hr π n ω
  have hi := budget_profile_prefix_certificate e f _ _ (r n) p ω h (H n) hh
  have hp := protection_retained_le_raw e f base G H r hr π n ω
  rw [Finset.prod_range_succ,protectionMass_ennreal]
  change c*relativeBudgetMassENN e f (H n) (r n) p.val ω ≤ _
  calc
    _ ≤ c*rawTupleMixture (realPosition (step e)) h p.val ω
      {y | TupleSeparated f (protectionGap G r n-r n) y} := mul_le_mul_right hi c
    _ = rawTupleMixture (realPosition (step e)) h (c•p.val) ω
      {y | TupleSeparated f (protectionGap G r n-r n) y} := by
        rw [rawTupleMixture_smul,Measure.smul_apply,smul_eq_mul]
    _ ≤ rawTupleMixture (realPosition (step e)) h
      (rawTupleMixture (realPosition (step e)) (∑ i∈Finset.range n,H i) (π ω).val ω) ω
      {y | TupleSeparated f (protectionGap G r n-r n) y} := (rawTupleMixture_mono _ _ _ hp) _
    _ ≤ _ := rawTupleMixture_comp_le e (∑ i∈Finset.range n,H i) h (π ω).val ω _

theorem protection_prefix_after_retention {d k : ℕ} (e f : Direction d) (base G : ℝ)
    (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i,0≤r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G)
    (n h : ℕ) (hh : h≤H n) (ω : Environment d)
    (μ : Measure (Fin k → Lattice d)) (t : ℕ) (c : ℝ≥0∞)
    (hc : c•(π ω).val ≤ rawTupleMixture (realPosition (step e)) t μ ω) :
    c*(∏ i∈Finset.range (n+1),ENNReal.ofReal (protectionMass e f base G H r hr π i ω)) ≤
      rawTupleMixture (realPosition (step e)) (t+(∑ i∈Finset.range n,H i)+h) μ ω
        {y | TupleSeparated f (protectionGap G r n-r n) y} := by
  have hp := protection_prefix_certificate e f base G H r hr π n h hh ω
  calc
    _ ≤ c*rawTupleMixture (realPosition (step e)) ((∑ i∈Finset.range n,H i)+h) (π ω).val ω
      {y | TupleSeparated f (protectionGap G r n-r n) y} := mul_le_mul_right hp c
    _ = rawTupleMixture (realPosition (step e)) ((∑ i∈Finset.range n,H i)+h) (c•(π ω).val) ω
      {y | TupleSeparated f (protectionGap G r n-r n) y} := by
        rw [rawTupleMixture_smul,Measure.smul_apply,smul_eq_mul]
    _ ≤ rawTupleMixture (realPosition (step e)) ((∑ i∈Finset.range n,H i)+h)
      (rawTupleMixture (realPosition (step e)) t μ ω) ω
      {y | TupleSeparated f (protectionGap G r n-r n) y} := (rawTupleMixture_mono _ _ _ hc) _
    _ ≤ _ := by
      simpa only [Nat.add_assoc] using rawTupleMixture_comp_le e t ((∑ i∈Finset.range n,H i)+h) μ ω
        {y | TupleSeparated f (protectionGap G r n-r n) y}

end DirectionalTransience

end

end OAI
