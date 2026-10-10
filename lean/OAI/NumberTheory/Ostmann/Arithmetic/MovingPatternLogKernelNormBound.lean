import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternLogIntegrand
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkArithmetic
import OAI.NumberTheory.Ostmann.Construction.OriginalAbsoluteBulkBound
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternNormKernel

namespace OAI

/-! # The sharp pattern kernel under its original bulk prime law -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

/-- The original deleted prime kernel keeps its terminal log cutoffs.
The main arithmetic norm bound is unchanged; only the explicit comparison
error budget contains the additional logarithmic variation cost. -/
theorem PublishedProgressionInput.movingPattern_log_norm_kernel_bound
    (P : PublishedProgressionInput) {B C Cell : Type*} [Fintype Cell]
    {N n m r₀ : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (hsmall : ∀ b, MovingLeafLengthLE n (small b) r₀)
    (base : Fin (N + 1) → ℕ) (childBound pivotBound : ℕ → ℕ)
    (j₀ : TreeLeafIndex n × Fin m)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)
    {tlog : ℕ} (logSlots : Fin tlog → List (Fin (N + 1))) (cb Dlog : ℝ)
    (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
    (rlog : ℕ) (hslots : ∀ j, (logSlots j).length ≤ rlog)
    (r : ℕ) [NeZero r]
    (p : Fin m → ℕ) [∀ i, NeZero (p i)]
    [NeZero (∏ i, bulkResidueModuli r p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (freq : ((TreeLeafIndex n × Fin m) → (ZMod r)ˣ) → ℂ)
    (spec : ∀ i, ((TreeLeafIndex n × Fin m) → (ZMod (p i))ˣ) → ℂ)
    (A : ℝ) (hA : 0 ≤ A) (hf : ∀ a, ‖freq a‖ ≤ A)
    (Q : ℕ) (hQ : 2 ≤ Q) (hMQ : (∏ i, bulkResidueModuli r p i) ≤ Q)
    (primes : Finset ℕ) (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
    (hu : ∀ j c, 1 ≤ u j c) (huv : ∀ j c, u j c ≤ v j c)
    (hshort : ∀ j c, v j c ≤ u j c + 1)
    (hmassCell : ∀ j c (a : (ZMod (∏ i, bulkResidueModuli r p i))ˣ),
      ∑ q ∈ primeLogCellSet (∏ i, bulkResidueModuli r p i) a.val.val (u j c) (v j c),
        (q : ℝ)⁻¹ ≤ 2)
    (c₀ : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ)
    (hP : ∀ j, primeCellSupport (∏ i, bulkResidueModuli r p i)
      (fun c : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) ⊆ primes)
    (hsep : ∀ j (c d : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ), c ≠ d →
      ¬Nat.ModEq (∏ i, bulkResidueModuli r p i) c.2.val.val d.2.val.val ∨
        v j c.1 ≤ u j d.1 ∨ v j d.1 ≤ u j c.1)
    (deleted : (TreeLeafIndex n × Fin m) → Finset ℕ)
    (hdeleted : ∀ j, (∑ q ∈ primeCellSupport (∏ i, bulkResidueModuli r p i)
      (fun c : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) \ deleted j, (q : ℝ)⁻¹) ≠ 0)
    (A₀ : ℝ) (hA₀ : 0 ≤ A₀) (H T : ℝ) (Bspec : Fin m → ℝ)
    (hBspec : ∀ i, 0 ≤ Bspec i) :
    let K := movingPatternLogIntegrand e tierB tierC t small slot perm pattern hB htier
      (fun i => (base i : ℝ)) childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq
      φ G Bφ Dφ hBφ hDφ hφ hlip hout L U logSlots cb
    let W := (movingFourierVariationBudget ψ V lo hi n *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
    let W₀ := ((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) * Bφ ^ (2 ^ n - 1)) ^ 2
    let M := ∏ i, bulkResidueModuli r p i
    let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1)
    let Z := fun j => (∑ q ∈ S j \ deleted j, (q : ℝ)⁻¹)⁻¹
    let label := fun (x : (TreeLeafIndex n × Fin m) → primes) j => primeCellLabel M
      (fun c : Cell × (ZMod M)ˣ => c.2.val.val) (fun c => u j c.1) (fun c => v j c.1) c₀ (x j)
    let a := fun z => freq (bulkResidueEquiv r p hc z).1 *
      ∏ i, spec i ((bulkResidueEquiv r p hc z).2 i)
    let err := fun c : (TreeLeafIndex n × Fin m) → Cell =>
      2 ^ Fintype.card (TreeLeafIndex n × Fin m) * ∑ j,
        bulkLogWeightedKernelPairBudget ψ V lo hi n
          (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 tlog rlog Bφ Dφ Dlog *
          bulkPrimeErrorFactor P Q (u j (c j))
    (∀ y : (TreeLeafIndex n × Fin m) → ℝ, (∀ j, 0 ≤ y j) →
      (Fintype.card ((TreeLeafIndex n × Fin m) → (ZMod M)ˣ) : ℝ)⁻¹ *
        ∑ z, ‖a z * ∏ j, pageGiantWeight P Q M (z j).val.val (y j)‖ ≤ A₀) →
    (∀ i z, ‖spec i z‖ ≤ Bspec i) →
    (∀ j, Z j * ∑ c, ∫ x in Set.Ioc (u j c) (v j c), (x : ℝ)⁻¹ ≤ 2) →
    (∀ j, Z j ≤ Real.exp H) →
    (∀ j q, q ∈ S j \ deleted j → Real.exp T ≤ (q : ℝ)) →
    ‖∑ x : (TreeLeafIndex n × Fin m) → primes,
      ((∏ j, primeSubsetPrior primes (S j \ deleted j) (x j) : ℝ) : ℂ) *
        (if Function.Injective x then a (fun j => (label x j).2) *
          K (fun j => Real.log (x j : ℕ)) else 0)‖ ≤
      (W₀ * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m) +
        (∏ j, Z j) * ∑ c : (TreeLeafIndex n × Fin m) → Cell, ∑ z, ‖a z‖ * err c +
        (A * (∏ i, Bspec i) * W) * (Fintype.card (TreeLeafIndex n × Fin m) : ℝ) ^ 2 *
          Real.exp (H - T) +
        (A * (∏ i, Bspec i) * W) * ((∏ j, (1 + Z j * ∑ q ∈ S j ∩ deleted j, (q : ℝ)⁻¹)) - 1) := by
  intro K W W₀ M S Z label a err hlocal hspec hmass hZ hlow
  have hW : 0 ≤ W := sq_nonneg _
  have hk : ∀ z, ‖K z‖ ≤ W := movingPatternLogIntegrand_norm e tierB tierC t small slot perm pattern hB htier
    (fun i => (base i : ℝ)) childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq
    φ G Bφ Dφ hBφ hDφ hφ hlip hout L U logSlots cb
  have hk₀ : ∀ z, ‖K z‖ ≤ W₀ := movingPatternLogIntegrand_norm_window e tierB tierC t small slot perm pattern hB htier
    (fun i => (base i : ℝ)) childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq
    φ G Bφ Dφ hBφ hDφ hφ hlip hout L U logSlots cb
  have herr (c : (TreeLeafIndex n × Fin m) → Cell)
      (z : (TreeLeafIndex n × Fin m) → (ZMod M)ˣ) :
      ‖(∫ y, K y ∂Measure.pi (fun j => primeLogCellMeasure M (z j).val.val (u j (c j)) (v j (c j)))) -
        ∫ y, K y ∂Measure.pi (fun j => primeGiantMeasure P Q M (z j).val.val (u j (c j)) (v j (c j)))‖ ≤
        err c :=
    P.movingPatternLogIntegrand_comparison e tierB tierC t small slot perm pattern hB htier
      (fun i => (base i : ℝ)) childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq φ G Bφ Dφ
      hBφ hDφ hφ hlip hout L U logSlots cb hsmall Dlog hDlog hloglip rlog hslots hQ (fun _ => ∏ i, bulkResidueModuli r p i)
      (fun j => (z j).val.val) (fun j => u j (c j)) (fun j => v j (c j))
      (fun _ => Nat.pos_of_ne_zero (NeZero.ne _)) (fun _ => hMQ)
      (fun j => ZMod.val_coe_unit_coprime (z j)) (fun j => hu j (c j))
      (fun j => huv j (c j)) (fun j => hshort j (c j)) (fun j => hmassCell j (c j) (z j))
  have hn (x : (TreeLeafIndex n × Fin m) → primes) :
      ‖a (fun j => (label x j).2) * K (fun j => Real.log (x j : ℕ))‖ ≤ A * (∏ i, Bspec i) * W := by
    rw [norm_mul]
    apply mul_le_mul _ (hk _) (norm_nonneg _) (mul_nonneg hA (Finset.prod_nonneg fun i _ => hBspec i))
    change ‖freq _ * ∏ i, spec i _‖ ≤ _
    rw [norm_mul, norm_prod]
    exact mul_le_mul (hf _) (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun i _ => hspec i _)) (Finset.prod_nonneg fun _ _ => norm_nonneg _) hA
  have hb := original_absolute_bulk_bound primes M u v
    (fun j c => lt_of_lt_of_le zero_lt_one (hu j c)) c₀ hP hsep deleted hdeleted
    K a P Q W₀ A₀ (sq_nonneg _) hA₀ hk₀
    (by
      intro y hy
      have hy' := hlocal y hy
      simp only [finite_univ_canonical, Fintype.card_eq_nat_card] at hy' ⊢
      exact hy') (fun c _ => err c) herr H T
    (A * (∏ i, Bspec i) * W)
    (mul_nonneg (mul_nonneg hA (Finset.prod_nonneg fun i _ => hBspec i)) hW)
  have hh := hb hmass hZ hlow hn
  simp only [finite_univ_canonical, Fintype.card_eq_nat_card] at hh ⊢
  exact hh

end Ostmann

end OAI
