import OAI.NumberTheory.Ostmann.Construction.FiniteScheduledPhase

namespace OAI

/-! # The original-prior arithmetic transfer through a finite schedule -/
namespace Ostmann
open scoped BigOperators Classical

theorem scheduled_arithmetic_transfer_finite {I A Z : Type*}
    [Fintype I] [Fintype A] [Fintype Z]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n r : ℕ)
    (hpivot : ∀ k ≤ n, role (pivot k) = .pivot k) (e : Fin r ≃ CurrentPivotConstituent role n) (hist : A → FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hκ : ∀ i p, p ∈ P → ‖κ i p‖ ≤ 1)
    (Q : Fin r → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (S : Finset (Fin r → P)) (hS : ∀ x ∈ S, Function.Injective x)
    (T : Finset ℕ) (hT : ∀ M ∈ T, 0 < M) (hST : ∀ x ∈ S, (∏ i, (x i : ℕ)) ∈ T)
    (L : A → CopyScheduleH role n → ℕ) (U : Z → CopyScheduleY role n → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ z y, Fact (U z y).Prime]
    (center : ∀ p : ℕ, ZMod p) (W : Z → ℕ → A → ℂ) (μ : Z → ℝ)
    (hμ : ∀ z, 0 ≤ μ z) (hμsum : ∑ z, μ z ≤ 1)
    (B K V : ℕ)
    (hsupport : ∀ z M, M ∈ T → ∀ a, W z M a ≠ 0 →
      Pairwise (fun i j => (Sum.elim (L a) (U z) i).Coprime (Sum.elim (L a) (U z) j)) ∧
      M.Coprime ((∏ h, L a h) * ∏ y, U z y) ∧
      (frequencyRoot n (hist a)).natAbs ≤ B ∧ (∏ h, L a h) ≤ K)
    (hfreq : ∀ z x, x ∈ S → ∀ a, W z (∏ i, (x i : ℕ)) a ≠ 0 →
      ∀ i, ∀ s ∈ allFrequencyList n (hist a), (s : ZMod (x i : ℕ)) ≠ 0)
    (hscale : ∀ M ∈ T, 2 * B * K ≤ V * M)
    (hlargeL : ∀ a h, V < L a h) (hlargeU : ∀ z y, V < U z y)
    (d : ℝ) (hcost : ((r.factorial : ℝ) * ∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) ≤ Real.exp d) :
    Real.exp (-d) *
      ‖scheduledCurrentAmplitude role χ κ pivot n r e hist P hP Q S L U center W μ‖ ^ 2 ≤
      (∑ z, μ z * ∑ M ∈ T,
        (pivotDiagonal (fun a => ∏ h, L a h) (fun a => frequencyRoot n (hist a))
          (retainedWeightedCoefficient L (U z) center
            (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
            (scheduledRetainedGraph role initialCompleteGraph pivot n)
            (fun a h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
              n (hist a) h.val (L a h))
            (fun a y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
              n (hist a) y.val (U z y))
            (fun a => frequencyRoot n (hist a)) (W z) M)).re) +
      ‖∑ z, (μ z : ℂ) * scheduledNextAmplitude role χ initialCompleteGraph pivot
        (initialRegularUnary χ κ) n hist L (U z) center (W z) T V‖ := by
  have hcurrent := scheduledCurrentAmplitude_eq_grouped_finite role χ κ pivot n r hpivot e hist
    P hP Q S hS L U center W μ (by
      intro z x hx a ha
      have hs := hsupport z _ (hST x hx) a ha
      exact ⟨hs.1, hs.2.1, hfreq z x hx a ha⟩)
  rw [hcurrent]
  have ht := original_directed_transfer P hP Q hQP hQ S hS T hT hST
    (fun i => χ (e i).val) (fun i p => κ (e i).val p)
    (fun i p => hκ (e i).val p p.property) (fun _ => 1) L U center
    (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
    (scheduledRetainedGraph role initialCompleteGraph pivot n)
    (fun z a h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
      n (hist a) h.val (L a h))
    (fun z a y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
      n (hist a) y.val (U z y)) (fun a => frequencyRoot n (hist a)) W μ hμ hμsum
    B K V hsupport hscale hlargeL hlargeU
    (fun y => scheduledRetainedGraph_diagonal role pivot n (some (.inr y))) d hcost
  simpa only [copiedWeightedAmplitude_eq_scheduledNextAmplitude] using ht

theorem constituentPrimeGuardedAmplitude_step_finite {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (hpivot : ∀ k ≤ n, role (pivot k).1 = .pivot k) (p : I) (hp : role p = .pivot n) (hu : ∀ i, role i = .pivot n → i = p)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (hκ : ∀ i q, q ∈ P → ‖κ i q‖ ≤ 1)
    (hQP : ∀ i, Q i ⊆ P) (hQ : ∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹) ≠ 0)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (center : ∀ p : ℕ, ZMod p) (K V : ℕ) (T : Finset ℕ)
    (hST : ∀ x : Fin (size p) → P, Function.Injective x → (∀ i, (x i : ℕ) ∈ Q ⟨p, i⟩) → (∏ i, (x i : ℕ)) ∈ T)
    (hzero : ∀ x, fullAtomTransferWeight role childBound pivotBound ranges leaf 0 x (0 : ℤ) = 0)
    (hsmall : ∀ d s, s ∈ allFrequencyList n (hist d) → ∀ q ∈ P, s.natAbs < q)
    (hTpos : ∀ M ∈ T, 0 < M) (hTbound : ∀ M ∈ T, M ≤ pivotBound n)
    (hTfull : ∀ (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) d M, 0 < M → M ≤ pivotBound n →
      fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d) ≠ 0 → M ∈ T)
    (hcut : ∀ u, ∀ M ∈ T, ∀ a,
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0 →
      (frequencyRoot n (hist a.2)).natAbs ≤ childBound n ∧ (∏ h, (a.1 h : ℕ)) ≤ K)
    (hscale : ∀ M ∈ T, 2 * childBound n * K ≤ V * M)
    (hlarge : ∀ q ∈ P, V < q)
    (hgap : ∀ u, ∀ M ∈ T, ∀ a a',
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0 →
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a' ≠ 0 →
      2 * pivotBound n * childBound n < ∏ h, (a'.1 h : ℕ))
    (hrange : ∀ u, ∀ M ∈ T, ∀ a a',
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0 →
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a' ≠ 0 →
      ∀ b ∈ ranges (n + 1), b.Holds (copiedConstituentAtomValues role size n P u a.1 a'.1))
    (loss : ℝ) (hcost : (((size p).factorial : ℝ) *
      ∏ i : Fin (size p), (∑ q ∈ Q ⟨p, i⟩, (q : ℝ)⁻¹)⁻¹) ≤ Real.exp loss) :
    Real.exp (-loss) *
      ‖constituentPrimeGuardedAmplitude role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist center‖ ^ 2 ≤
      (∑ u, (∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y)) *
        ∑ M ∈ T, (constituentPivotDiagonal role size χ κ pivot n P hP Q
          childBound pivotBound ranges leaf hist center u M).re) +
      ‖constituentPrimeGuardedAmplitude role size χ κ pivot (n + 1) P hP Q
        childBound pivotBound ranges leaf (copiedConstituentHistory hist V) center‖ := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
    fun a h => ⟨hP _ (a.1 h).property⟩
  let : ∀ (u : CopyScheduleY ρ n → P) y, Fact (u y : ℕ).Prime :=
    fun u y => ⟨hP _ (u y).property⟩
  let μ (u : CopyScheduleY ρ n → P) :=
    ∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y)
  have hμ (u) : 0 ≤ μ u := Finset.prod_nonneg (fun _ _ => primeSubsetPrior_nonneg _ _ _)
  have hμsum : ∑ u, μ u = 1 := by
    rw [← Fintype.prod_sum]
    have hm (y : CopyScheduleY ρ n) :
        (∑ q : P, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) q) = 1 :=
      primeSubsetPrior_mass P _ (hQP _) (hQ _)
    simp only [hm, Finset.prod_const_one]
  have ht := scheduled_arithmetic_transfer_finite ρ χ κ pivot n (size p) hpivot
    (pivotConstituentEquiv role size n p hp hu) (fun a => hist a.2) P hP hκ
    (fun k => Q ⟨p, k⟩) (fun k => hQP ⟨p, k⟩) (fun k => hQ ⟨p, k⟩)
    (supportedPivotTuples P (fun k => Q ⟨p, k⟩))
    (fun x hx => ((mem_supportedPivotTuples _ _ _).mp hx).1)
    T hTpos (fun x hx => hST x ((mem_supportedPivotTuples _ _ _).mp hx).1
      ((mem_supportedPivotTuples _ _ _).mp hx).2)
    (fun a h => (a.1 h : ℕ)) (fun u y => (u y : ℕ)) center
    (constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist)
    μ hμ hμsum.le (childBound n) K V (by
      intro u M hM a ha
      have hs := constituentTransferWeight_support role size n p hp P Q childBound pivotBound ranges leaf hist u M a ha
      exact ⟨hs.1, hs.2.1, (hcut u M hM a ha).1, (hcut u M hM a ha).2⟩) (by
      intro u x _ a ha i s hs
      let : Fact (x i : ℕ).Prime := ⟨hP _ (x i).property⟩
      exact constituentTransferWeight_frequency_unit role size n P Q childBound pivotBound ranges leaf hist
        hzero u (∏ i, (x i : ℕ)) a ha (x i) s hs (hsmall a.2 s hs _ (x i).property))
    hscale (fun a h => hlarge _ (a.1 h).property) (fun u y => hlarge _ (u y).property) loss hcost
  have hc := constituentPrimeGuardedAmplitude_eq_supported_transfer role size χ κ pivot n p hp hu
    P hP Q childBound pivotBound ranges leaf hist center
  have hn := constituentPrimeGuardedAmplitude_next role size χ κ pivot n p hp P hP Q
    childBound pivotBound ranges leaf hist center K V T hTpos hTbound hTfull
    hcut hscale hlarge hgap hrange
  rw [← hc, ← hn] at ht
  exact ht

theorem constituentPrimeGuardedAmplitude_interval_step_finite {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (hpivot : ∀ k ≤ n, role (pivot k).1 = .pivot k) (p : I) (hp : role p = .pivot n) (hu : ∀ i, role i = .pivot n → i = p)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (hκ : ∀ i q, q ∈ P → ‖κ i q‖ ≤ 1)
    (hQP : ∀ i, Q i ⊆ P) (hQ : ∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹) ≠ 0)
    (lo hi : I → ℕ) (cellLo cellHi : (Σ i, Fin (size i)) → ℕ)
    (hcell : ∀ i q, q ∈ Q i → cellLo i ≤ q ∧ q ≤ cellHi i)
    (childBound pivotBound : ℕ → ℕ) (leaf : ScheduleAtomState role → ℤ → ℂ)
    (hist : D → FrequencyTree ℤ n) (center : ∀ p : ℕ, ZMod p) (K V : ℕ)
    (hpLo : 0 < lo p) (hpHi : hi p ≤ pivotBound n)
    (hcellLo : lo p ≤ ∏ k : Fin (size p), cellLo ⟨p, k⟩)
    (hcellHi : (∏ k : Fin (size p), cellHi ⟨p, k⟩) ≤ hi p)
    (hroot : ∀ d, (frequencyRoot n (hist d)).natAbs ≤ childBound n)
    (hzero : ∀ x, fullAtomTransferWeight role childBound pivotBound
      (atomIntervalRanges role lo hi) leaf 0 x (0 : ℤ) = 0)
    (hsmall : ∀ d s, s ∈ allFrequencyList n (hist d) → ∀ q ∈ P, s.natAbs < q)
    (hK : (∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
      cellHi (copyScheduleOrigin n h.val)) ≤ K)
    (hgap : 2 * pivotBound n * childBound n <
      ∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n, cellLo (copyScheduleOrigin n h.val))
    (hscale : 2 * childBound n * K ≤ V * lo p) (hlarge : ∀ q ∈ P, V < q)
    (loss : ℝ) (hcost : (((size p).factorial : ℝ) *
      ∏ i : Fin (size p), (∑ q ∈ Q ⟨p, i⟩, (q : ℝ)⁻¹)⁻¹) ≤ Real.exp loss) :
    Real.exp (-loss) *
      ‖constituentPrimeGuardedAmplitude role size χ κ pivot n P hP Q
        childBound pivotBound (atomIntervalRanges role lo hi) leaf hist center‖ ^ 2 ≤
      (∑ u, (∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y)) *
        ∑ M ∈ Finset.Icc (lo p) (hi p), (constituentPivotDiagonal role size χ κ pivot n P hP Q
          childBound pivotBound (atomIntervalRanges role lo hi) leaf hist center u M).re) +
      ‖constituentPrimeGuardedAmplitude role size χ κ pivot (n + 1) P hP Q
        childBound pivotBound (atomIntervalRanges role lo hi) leaf (copiedConstituentHistory hist V) center‖ := by
  apply constituentPrimeGuardedAmplitude_step_finite role size χ κ pivot n hpivot p hp hu P hP Q
    hκ hQP hQ childBound pivotBound (atomIntervalRanges role lo hi) leaf hist center K V
    (Finset.Icc (lo p) (hi p))
  · intro x _ hx
    apply Finset.mem_Icc.mpr
    exact ⟨hcellLo.trans (Finset.prod_le_prod (fun i _ => (hcell _ _ (hx i)).1)),
      (Finset.prod_le_prod (fun i _ => (hcell _ _ (hx i)).2)).trans hcellHi⟩
  · exact hzero
  · exact hsmall
  · intro M hM
    exact hpLo.trans_le (Finset.mem_Icc.mp hM).1
  · intro M hM
    exact (Finset.mem_Icc.mp hM).2.trans hpHi
  · intro u l d M _ _ hw
    exact Finset.mem_Icc.mpr (fullAtomTransferWeight_inserted_pivot_bounds role lo hi
      childBound pivotBound leaf n p hp M _ _ (hist d) hw)
  · intro u M _ a ha
    have hh := constituentTransferWeight_product_bounds role size n P Q childBound pivotBound
      (atomIntervalRanges role lo hi) leaf hist u M a ha cellLo cellHi hcell
    exact ⟨hroot a.2, hh.2.trans hK⟩
  · intro M hM
    exact hscale.trans (Nat.mul_le_mul_left V (Finset.mem_Icc.mp hM).1)
  · exact hlarge
  · intro u M _ a b _ hb
    have hh := constituentTransferWeight_product_bounds role size n P Q childBound pivotBound
      (atomIntervalRanges role lo hi) leaf hist u M b hb cellLo cellHi hcell
    exact hgap.trans_le hh.1
  · intro u M _ a b ha hb
    exact constituentTransferWeight_copied_intervals role size lo hi n P Q childBound pivotBound
      leaf hist u M a b ha hb
  · exact hcost

end Ostmann

end OAI
