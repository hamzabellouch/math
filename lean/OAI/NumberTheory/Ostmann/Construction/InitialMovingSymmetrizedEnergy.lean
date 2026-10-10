import OAI.NumberTheory.Ostmann.Construction.InitialMovingLogCorrelation
import OAI.NumberTheory.Ostmann.Construction.InitialMovingNorm
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateSymmetrizedNorm

namespace OAI

/-! # Symmetrized energy with both original half-cutoffs retained -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingTemplate_initial_symmetrized_energy_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n a b d r : ℕ)
    (hm : 1 ≤ b + b) (hlen : a + 4 * n = r + r)
    (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P) (outside : List ℕ)
    (μ : ℕ → P → ℝ) (ν : MovingRegularSlot n a (b + b) → P → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p)
    (hidentical : ∀ j l, ν (movingTemplateBulk n a (b + b) j) =
      ν (movingTemplateBulk n a (b + b) l))
    (q : Fin (b + b) → ℕ) [∀ i, Fact (q i).Prime]
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ)
    (childBound pivotBound V : ℕ → ℕ) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (G : ℕ → ℝ)
    (active : MovingRegularSlot n a (b + b) → Bool)
    (hactive : ∀ j, active (movingTemplateBulk n a (b + b) j) = true)
    (greg : ∀ p : ℕ, ZMod p → ℂ) (Jleft Jright : ℝ) (diagonal : Bool)
    (u v w z center D E : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hdiag : ‖mixedExternalAverage ν (V n) u v w z center (fun s y x z =>
      (‖movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val q (fun _ s => if s = 0 then 0 else 1)
          g Dq Finset.univ ψ X lo hi) φ G n a (b + b) s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊‖ ^ 2 : ℂ) *
      movingTemplateExternalMultiplier P hP n a (b + b) active outside greg s φ
        Jleft Jright diagonal y x z)‖ ≤ D)
    (hgood : ∀ perm : Equiv.Perm (TreeLeafIndex n × Fin (b + b)),
      4 * Fintype.card (arrangementGraph (b + b) perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex n) →
      let slot := movingTemplateBulk n a (b + b)
      let bulk := movingPatternBulkLeaves n (b + b) slot perm
      let slots := fun side => if side then slot ∘ perm.symm else (slot : _ → _)
      let logSlots := initialPairedHalfLogSlots n b slots
      let wgt := fun (y : MovingRegularSlot n a (b + b) → P) =>
        ((∏ j, bulkLogCutoffWeight (fun i => ((y i : ℕ) : ℝ)) cb (logSlots j) : ℝ) : ℂ)
      ‖movingWeightedMatchedCorrelation q Subtype.val outside μ ν childBound pivotBound V
        (fun s => if s = 0 then 0 else 1) g Dq Finset.univ ψ X lo hi φ G n
        (movingTemplateSmall n a (b + b)) bulk (fun s y x z => wgt y *
          movingTemplateExternalMultiplier P hP n a (b + b) active outside greg s φ
            Jleft Jright diagonal y x z) u v w z center‖ ≤ E) :
    ‖movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V
      (movingOriginalLeaf Subtype.val q
        (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback)
        g Dq Finset.univ ψ X lo hi) φ G n a (b + b) ν active greg
      Jleft Jright diagonal u v w z center‖ ≤
    (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
      Real.exp ((2 ^ n : ℝ) * ((b + b : ℕ) : ℝ) * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4)) * D + E := by
  let F : MovingSlotState P → ℤ → ℂ := movingOriginalLeaf Subtype.val q (fun _ s => if s = 0 then 0 else 1)
    g Dq Finset.univ ψ X lo hi
  let Fw : MovingSlotState P → ℤ → ℂ := movingOriginalLeaf Subtype.val q
    (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback) g Dq Finset.univ ψ X lo hi
  rw [movingTemplateMaskedSymmetrizedEnergy_norm_eq_re P hP outside μ childBound pivotBound V
    Fw φ hφ G n a (b + b) ν hν active greg Jleft Jright diagonal u v w z center]
  apply movingTemplateMaskedSymmetrizedEnergy_bound P hP outside μ childBound pivotBound V Fw
    φ hφ G n a (b + b) hm ν hν hidentical active hactive greg
    Jleft Jright diagonal u v w z center D E hD hE
  · have hw (s : ℤ) (y : MovingRegularSlot n a (b + b) → P) (x z : ℝ) :
        ((movingTemplateExternalMultiplier P hP n a (b + b) active outside greg s φ
          Jleft Jright diagonal y x z).re : ℂ) =
        movingTemplateExternalMultiplier P hP n a (b + b) active outside greg s φ
          Jleft Jright diagonal y x z :=
      (movingTemplateExternalMultiplier_nonneg P hP n a (b + b) active outside greg s φ hφ
        Jleft Jright diagonal y x z).2
    have h := mixedExternalAverage_square_mono_support ν hν (V n) u v w z center
      (fun s y x z => movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V Fw
        φ G n a (b + b) s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)
      (fun s y x z => movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F
        φ G n a (b + b) s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)
      (fun s y x z => (movingTemplateExternalMultiplier P hP n a (b + b) active outside greg s φ
        Jleft Jright diagonal y x z).re)
      (fun s y x z => (movingTemplateExternalMultiplier_nonneg P hP n a (b + b) active outside greg s φ hφ
        Jleft Jright diagonal y x z).1)
      (fun y _ s x z => movingTemplateCoefficient_original_initial_norm_le Subtype.val b d r cb cd
        sl sr fallback q g Dq Finset.univ ψ X lo hi outside μ childBound pivotBound V φ G n a s y
        hlen ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)
    simp only [hw] at h
    exact h.trans ((Complex.re_le_norm _).trans hdiag)
  · intro perm hperm
    have he := movingTemplate_initial_log_correlation_eq P hP n a b d r hlen cb cd sl sr fallback
      outside μ ν q g Dq childBound pivotBound V ψ X lo hi φ G active greg Jleft Jright diagonal
      u v w z center perm
    rw [he, norm_mul]
    have h0 := mul_nonneg (initialLogSumWeight_nonneg Subtype.val cd sl)
      (initialLogSumWeight_nonneg Subtype.val cd sr)
    have h1 : initialLogSumWeight Subtype.val cd sl * initialLogSumWeight Subtype.val cd sr ≤ 1 :=
      (mul_le_mul (initialLogSumWeight_le_one Subtype.val cd sl)
        (initialLogSumWeight_le_one Subtype.val cd sr)
        (initialLogSumWeight_nonneg Subtype.val cd sr) zero_le_one).trans_eq (one_mul 1)
    have hfac : ‖((initialLogSumWeight Subtype.val cd sl * initialLogSumWeight Subtype.val cd sr) ^
        (2 ^ n + 2 ^ n) : ℝ)‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (pow_nonneg h0 _)]
      exact pow_le_one₀ h0 h1
    rw [Complex.norm_real]
    exact (mul_le_of_le_one_left (norm_nonneg _) hfac).trans (hgood perm hperm)

end Ostmann

end OAI
