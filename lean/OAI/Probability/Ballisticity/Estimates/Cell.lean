import Mathlib
import OAI.Probability.Ballisticity.Coupling.FreshClipping
import OAI.Probability.Ballisticity.Estimates.CellFailure
import OAI.Probability.Ballisticity.Coupling.CellSeedParameters

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma belowHeight_add_nat_mono {d : ℕ} (e : Direction d) (a : ℝ) (n : ℕ) :
    rowSigma (BelowHeight (realPosition (step e)) a) ≤
      rowSigma (BelowHeight (realPosition (step e)) (a+n)) := by
  apply rowSigma_mono
  intro x hx
  change dot (realPosition x) (realPosition (step e)) < a+n
  exact lt_of_lt_of_le hx (le_add_of_nonneg_right (Nat.cast_nonneg n))

noncomputable def cellLateMass {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (Hs He s : ℕ) (H : ℕ → ℕ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) : ℕ → Environment d → ℝ :=
  protectionMass e f (a+Hs+He) (3*c*ρ/4) H (lateBudget c ρ s)
    (fun i => (lateBudget_pos hc hρ s i).le)
    (cellLateInitial e f hef a c ρ hc.le hρ.le Hs He π)

theorem actual_consumed_cell_failure {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ k : ℕ, 2 ≤ k →
      ∃ C c g₀ g₁ : ℝ, 0 < C ∧ ∃ hc : 0 < c, c ≤ 1 ∧ 0 < g₀ ∧ 0 < g₁ ∧
      ∃ s H₀ : ℕ, 0 < s ∧ ∀ Bstar : ℝ, 0 < Bstar → ∃ R : ℝ, 0 < R ∧
      ∀ Hs ≥ H₀, ∀ (ρ : ℝ) (hρ : 0 < ρ), R ≤ ρ →
        ρ = fluctuationRadius (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) ((Hs:ℝ)/C) →
      ∀ He : ℕ, (He:ℝ) ≤ 3*C*fluctuationScale
        (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) ρ →
      ∀ H : ℕ → ℕ, (∀ i, (H i:ℝ) ≤ 3*C*fluctuationScale
        (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) ρ/(16:ℝ)^(s+i)) →
      ∀ m : ℕ, (2*A*k)*m ≤ Bstar → ∀ n : ℕ, 1 ≤ n → n ≤ m →
      ∀ (a : ℝ) (π : Environment d → LayerTupleProfile (k:=k) e a),
        @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π →
      ∀ E : Set (Environment d), MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] E →
        environmentLaw ν (E∩consumedCellFailure
          (cellSeedMass e f a (c*ρ) Hs π) (cellEarlyMass e f hef a (c*ρ) Hs He π)
          (cellLateMass e f hef a c ρ hc hρ Hs He s H π) g₀ g₁ (A*k) s m n) ≤
            ENNReal.ofReal (Real.exp (-2*k*n))*environmentLaw ν E := by
  obtain ⟨lam,Cmg,hlam,hlam1,hCmg,hlate⟩ :=
    actual_late_protection_first_failure ν hue e f hef htrans
  let A := max 1 (4*(Cmg+8)/lam)
  have hA : 1 ≤ A := le_max_left _ _
  have hchoice : Cmg+8 ≤ (lam/4)*A := by
    have h := le_max_right 1 (4*(Cmg+8)/lam)
    have hh := (div_le_iff₀ hlam).mp h
    dsimp [A]
    nlinarith only [hh]
  refine ⟨A,hA,fun k hk => ?_⟩
  obtain ⟨C,c,g₀,hC,hc,hc1,hg₀,H₀,hseed⟩ := adapted_separated_seeds_capped
    ν hue e f hef htrans k hk (Real.exp (-6*k)) (Real.exp_pos _)
  obtain ⟨s,hs,hsbound⟩ := hlate A hA hchoice k hk c C hc hc1 hC
  obtain ⟨g₁,hg₁,R₁,hR₁,hearly⟩ := adapted_initial_clipping ν hue e f hef htrans k
    (show 0 < 3*C by positivity) (show 0 < c/4 by positivity)
    (Real.exp_pos (-6*k*s))
  refine ⟨C,c,g₀,g₁,hC,hc,hc1,hg₀,hg₁,s,H₀,hs,fun Bstar hB => ?_⟩
  obtain ⟨R₂,hR₂,hb⟩ := hsbound Bstar hB
  refine ⟨max R₁ R₂,hR₁.trans_le (le_max_left _ _),?_⟩
  intro Hs hHs ρ hρ hρR hρeq He hHe H hH m hm n hn hnm a π hπ E hE
  have hr1 : R₁ ≤ ρ := (le_max_left _ _).trans hρR
  have hr2 : R₂ ≤ ρ := (le_max_right _ _).trans hρR
  apply consumedCellFailure_bound (environmentLaw ν) _ _ _ g₀ g₁ (A*k) s m n k (by omega) hn E
  · simpa only [cellSeedMass,hρeq] using hseed Hs hHs a π hπ E hE
  · have hEs : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) (a+Hs))] E :=
      belowHeight_add_nat_mono e a Hs E hE
    have hh := hearly ρ hr1 He hHe (a+Hs) (c*ρ)
      (fun ω => seedSeparatedProfile e f hef a (c*ρ) Hs (π ω) ω)
      (seedSeparatedProfile_measurable e f hef a (c*ρ) Hs π hπ) E hEs
    have heq : (c/4)*ρ=(c*ρ)/4 := by ring
    simpa only [heq,cellEarlyMass] using hh
  · intro hsn hnm'
    have heq : s+(n-s-1)+1=n := by omega
    have heq' : (s:ℝ)+((n-s-1:ℕ):ℝ)+1=n := by exact_mod_cast heq
    have ht : (2*A*k)*((s:ℝ)+((n-s-1:ℕ):ℝ)+1) ≤ Bstar := by
      rw [heq']
      exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hnm') (by positivity)).trans hm
    have hEl : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) (a+Hs+He))] E :=
      belowHeight_add_nat_mono e (a+Hs) He E (belowHeight_add_nat_mono e a Hs E hE)
    have hh := hb ρ hr2 (n-s-1) ht H (fun i _ => hH i) (a+Hs+He)
      (cellLateInitial e f hef a c ρ hc.le hρ.le Hs He π)
      (cellLateInitial_measurable e f hef a c ρ hc.le hρ.le Hs He π hπ) E hEl
    simpa only [cellLateMass,heq'] using hh

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma firstProtectionFailure_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    (q : ℕ → Ω → ℝ) (a s : ℝ) (n : ℕ) (hq : ∀ i ≤ n, Measurable (q i)) :
    MeasurableSet (firstProtectionFailure q a s n) := by
  unfold firstProtectionFailure
  rw [Set.ofPred_and]
  apply MeasurableSet.inter
  · rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro hj
    apply measurableSet_le measurable_const
    apply Finset.measurable_prod
    intro i hi
    exact hq i (by simp only [Finset.mem_range] at hi; omega)
  · apply measurableSet_lt _ measurable_const
    apply Finset.measurable_prod
    intro i hi
    exact hq i (by simpa using hi)

lemma consumedCellFailure_measurable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (seed : Ω → ℝ≥0∞) (early : Ω → ℝ) (q : ℕ → Ω → ℝ)
    (g₀ g₁ kA : ℝ) (s m n : ℕ)
    (hseed : n=1 ∨ n=min s m ∨ (s < n ∧ n ≤ m) → Measurable seed)
    (hearly : n=min s m ∨ (s < n ∧ n ≤ m) → Measurable early)
    (hq : s < n → n ≤ m → ∀ i ≤ n-s-1, Measurable (q i)) :
    MeasurableSet (consumedCellFailure seed early q g₀ g₁ kA s m n) := by
  unfold consumedCellFailure
  refine (MeasurableSet.union ?_ ?_).union ?_
  · by_cases hn : n=1
    · simpa only [hn,true_and] using measurableSet_lt (hseed (Or.inl hn)) measurable_const
    · simp only [hn,false_and,Set.ofPred_false]; exact MeasurableSet.empty
  · by_cases hn : n=min s m
    · simpa only [hn,true_and,Set.ofPred_and] using
        (measurableSet_le measurable_const (hseed (Or.inr (Or.inl hn)))).inter
          (measurableSet_lt (hearly (Or.inl hn)) measurable_const)
    · simp only [hn,false_and,Set.ofPred_false]; exact MeasurableSet.empty
  · by_cases hs : s < n
    · by_cases hm : n ≤ m
      · simpa only [hs,hm,true_and,Set.ofPred_and,Set.ofPred_mem_eq] using
          (measurableSet_le measurable_const (hseed (Or.inr (Or.inr ⟨hs,hm⟩)))).inter
            ((measurableSet_le measurable_const (hearly (Or.inr ⟨hs,hm⟩))).inter
              (firstProtectionFailure_measurable q kA s (n-s-1) (hq hs hm)))
      · simp only [hm,and_false,false_and,Set.ofPred_false]; exact MeasurableSet.empty
    · simp only [hs,false_and,Set.ofPred_false]; exact MeasurableSet.empty

lemma cellLateMass_measurable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (Hs He s : ℕ) (H : ℕ → ℕ)
    (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π) (i : ℕ) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e))
      (a+Hs+He+((∑ j∈Finset.range (i+1),H j):ℕ)))) _
      (cellLateMass e f hef a c ρ hc hρ Hs He s H π i) := by
  have hm := protectionMass_measurable e f (a+Hs+He) (3*c*ρ/4) H (lateBudget c ρ s)
    (fun j => (lateBudget_pos hc hρ s j).le)
    (cellLateInitial e f hef a c ρ hc.le hρ.le Hs He π)
    (cellLateInitial_measurable e f hef a c ρ hc.le hρ.le Hs He π hπ) i
  change @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e))
    (protectionHeight (a+Hs+He) H (i+1)))) _ _ at hm
  have ht : protectionHeight (a+Hs+He) H (i+1)=
      a+Hs+He+((∑ j∈Finset.range (i+1),H j):ℕ) := by
    rw [protectionHeight_eq,Nat.cast_sum]
  rw [ht] at hm
  exact hm

theorem actual_cell_failure_measurable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (Hs He s m n : ℕ) (H : ℕ → ℕ)
    (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (g₀ g₁ A b : ℝ)
    (hseed : n=1 ∨ n=min s m ∨ (s < n ∧ n ≤ m) → a+Hs ≤ b)
    (hearly : n=min s m ∨ (s < n ∧ n ≤ m) → a+Hs+He ≤ b)
    (hlate : s < n → n ≤ m → a+Hs+He+((∑ j∈Finset.range (n-s),H j):ℕ) ≤ b) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) b)]
      (consumedCellFailure (cellSeedMass e f a (c*ρ) Hs π)
        (cellEarlyMass e f hef a (c*ρ) Hs He π)
        (cellLateMass e f hef a c ρ hc hρ Hs He s H π) g₀ g₁ (A*k) s m n) := by
  let mB := rowSigma (BelowHeight (realPosition (step e)) b)
  have hmono {t : ℝ} (ht : t ≤ b) : rowSigma (BelowHeight (realPosition (step e)) t) ≤ mB :=
    rowSigma_mono (fun x hx => lt_of_lt_of_le hx ht)
  apply @consumedCellFailure_measurable _ mB
  · intro hn
    exact (cellSeedMass_measurable e f a (c*ρ) Hs π hπ).mono (hmono (hseed hn)) le_rfl
  · intro hn
    exact (cellEarlyMass_measurable e f hef a (c*ρ) Hs He π hπ).mono (hmono (hearly hn)) le_rfl
  · intro hsn hnm i hi
    apply (cellLateMass_measurable e f hef a c ρ hc hρ Hs He s H π hπ i).mono _ le_rfl
    apply hmono
    apply le_trans _ (hlate hsn hnm)
    have hsum : (∑ j∈Finset.range (i+1),H j) ≤ ∑ j∈Finset.range (n-s),H j :=
      Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    have hsum' : (((∑ j∈Finset.range (i+1),H j):ℕ):ℝ) ≤
        (((∑ j∈Finset.range (n-s),H j):ℕ):ℝ) := by exact_mod_cast hsum
    linarith only [hsum']

end DirectionalTransience

end

end OAI
