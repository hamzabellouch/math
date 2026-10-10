import OAI.NumberTheory.Ostmann.Construction.ConstituentGuardedNext
import OAI.NumberTheory.Ostmann.Construction.ConstituentFrequencySupport
import OAI.NumberTheory.Ostmann.Construction.ConstituentDiagonal
import OAI.NumberTheory.Ostmann.Construction.ScheduledArithmeticTransfer
import OAI.NumberTheory.Ostmann.Construction.SupportedPivotTuples

namespace OAI

/-! # One arithmetic step of the actual guarded original-prior amplitude -/

namespace Ostmann

open scoped BigOperators Classical

theorem constituentPrimeGuardedAmplitude_step {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (hpivot : ∀ k, role (pivot k).1 = .pivot k)
    (n : ℕ) (p : I) (hp : role p = .pivot n) (hu : ∀ i, role i = .pivot n → i = p)
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
  have ht := scheduled_arithmetic_transfer ρ χ κ pivot hpivot n (size p)
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

end Ostmann

end OAI
