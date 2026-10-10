import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateLogCorrelation
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateLogDiagonal
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateSymmetrizedNorm

namespace OAI

/-! # The actual retained-log symmetrized energy from diagonal and good-pair bounds -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingTemplate_log_symmetrized_energy_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n r m k : ℕ) (hm : 1 ≤ m) (hn : n ≤ k)
    (tier : P → ℕ) (outside : List ℕ) (cb cd : ℝ)
    (μ : ℕ → P → ℝ) (hμ : ∀ j a, μ j a ≠ 0 → tier a = j)
    (ν : MovingRegularSlot n r m → P → ℝ) (hν : ∀ j a, 0 ≤ ν j a)
    (hidentical : ∀ j l, ν (movingTemplateBulk n r m j) = ν (movingTemplateBulk n r m l))
    (hsmall : ∀ y : MovingRegularSlot n r m → P, (∏ j, ν j (y j)) ≠ 0 →
      ∀ j : TreeLeafIndex n × Fin r, tier (y (j.1, .inl j.2)) ≠ k)
    (hbulk : ∀ y : MovingRegularSlot n r m → P, (∏ j, ν j (y j)) ≠ 0 →
      ∀ j : TreeLeafIndex n × Fin m, tier (y (j.1, .inr j.2)) = k)
    (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (G : ℕ → ℝ)
    (active : MovingRegularSlot n r m → Bool)
    (hactive : ∀ j, active (movingTemplateBulk n r m j) = true)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (Jleft Jright : ℝ) (diagonal : Bool)
    (u v a b center D E : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hdiag : ‖mixedExternalAverage ν (V n) u v a b center (fun s y x z =>
      (‖movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p (fun _ => f) g Dq Finset.univ ψ X lo hi)
        φ G n r m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊‖ ^ 2 : ℂ) *
      movingTemplateExternalMultiplier P hP n r m active outside greg s φ Jleft Jright diagonal y x z)‖ ≤ D)
    (hgood : ∀ perm : Equiv.Perm (TreeLeafIndex n × Fin m),
      4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤ 3 * Fintype.card (TreeLeafIndex n) →
      let bulk := movingPatternBulkLeaves n m (movingTemplateBulk n r m) perm
      let wgt := fun y => ((∏ j, bulkLogCutoffWeight (fun i => ((y i : ℕ) : ℝ)) cb
        (movingBulkPairedCutoffSlots n bulk j) : ℝ) : ℂ)
      ‖movingWeightedMatchedCorrelation p Subtype.val outside μ ν childBound pivotBound V f g Dq Finset.univ
        ψ X lo hi φ G n (movingTemplateSmall n r m) bulk
        (fun s y x z => wgt y * movingTemplateExternalMultiplier P hP n r m active outside greg s φ
          Jleft Jright diagonal y x z) u v a b center‖ ≤ E) :
    ‖movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V
      (movingOriginalLeaf Subtype.val p
        (fun T s => (movingBulkLeafLogWeight Subtype.val tier k outside cb cd T : ℂ) * f s)
        g Dq Finset.univ ψ X lo hi) φ G n r m ν active greg Jleft Jright diagonal u v a b center‖ ≤
      (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
        Real.exp ((2 ^ n : ℝ) * m * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4)) * D + E := by
  let F : MovingSlotState P → ℤ → ℂ := movingOriginalLeaf Subtype.val p (fun _ => f) g Dq Finset.univ ψ X lo hi
  let Fw : MovingSlotState P → ℤ → ℂ := movingOriginalLeaf Subtype.val p
    (fun T s => (movingBulkLeafLogWeight Subtype.val tier k outside cb cd T : ℂ) * f s)
    g Dq Finset.univ ψ X lo hi
  have hleaf : Fw = fun x s =>
      (movingBulkLeafLogWeight Subtype.val tier k outside cb cd x.data : ℂ) * F x s := by
    funext x s
    exact movingOriginalLeaf_bulk_log Subtype.val tier k outside cb cd p (fun _ => f)
      g Dq Finset.univ ψ X lo hi x s
  rw [movingTemplateMaskedSymmetrizedEnergy_norm_eq_re P hP outside μ childBound pivotBound V
    Fw φ hφ G n r m ν hν active greg Jleft Jright diagonal u v a b center]
  apply movingTemplateMaskedSymmetrizedEnergy_bound P hP outside μ childBound pivotBound V Fw
    φ hφ G n r m hm ν hν hidentical active hactive greg Jleft Jright diagonal u v a b center D E hD hE
  · rw [hleaf]
    exact (movingTemplate_log_diagonal_le P hP n r m k hn tier outside cb cd μ hμ ν hν hsmall hbulk
      childBound pivotBound V F φ hφ G active greg Jleft Jright diagonal u v a b center).trans
        ((Complex.re_le_norm _).trans hdiag)
  · intro perm hperm
    have he := movingTemplate_log_correlation_eq P hP n r m k hn tier outside cb cd μ hμ ν hsmall hbulk
      p g Dq childBound pivotBound V f ψ X lo hi φ G active greg Jleft Jright diagonal u v a b center perm
    rw [he, norm_mul]
    have hfac : ‖((logCellProfile ((outside.map (fun p => Real.log (p : ℝ))).sum - cd) ^
        (2 ^ n + 2 ^ n) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (logCellProfile_nonneg _) _)]
      exact pow_le_one₀ (logCellProfile_nonneg _) (logCellProfile_le_one _)
    exact (mul_le_of_le_one_left (norm_nonneg _) hfac).trans (hgood perm hperm)

end Ostmann

end OAI
