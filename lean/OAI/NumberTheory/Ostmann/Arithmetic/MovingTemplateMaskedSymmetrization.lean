import OAI.NumberTheory.Ostmann.Arithmetic.MovingNormalizedSymmetrizedEnergy
import OAI.NumberTheory.Ostmann.Arithmetic.MovingMaskedBulkAction
import OAI.NumberTheory.Ostmann.Characters.MixedBulkSymmetrization

namespace OAI

/-! # Symmetrization with the actual compensation mask and original leaf coefficient -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplateExternalMultiplier_nonneg
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n r m : ℕ)
    (active : MovingRegularSlot n r m → Bool) (outside : List ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (s : ℤ) (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (Jleft Jright : ℝ) (diagonal : Bool) (y : MovingRegularSlot n r m → P) (x z : ℝ) :
    0 ≤ (movingTemplateExternalMultiplier P hP n r m active outside greg s φ
      Jleft Jright diagonal y x z).re ∧
    ((movingTemplateExternalMultiplier P hP n r m active outside greg s φ
      Jleft Jright diagonal y x z).re : ℂ) =
      movingTemplateExternalMultiplier P hP n r m active outside greg s φ
        Jleft Jright diagonal y x z := by
  have hc (J t : ℝ) : 0 ≤ positiveLogCutoff φ J t := by
    unfold positiveLogCutoff
    split_ifs
    · exact hφ _
    · exact le_rfl
  let q := fun i => (y i : ℕ)
  let _ : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (y i).property⟩
  let M := naturalRegularMultiplier q active s
    (fun i => ((outside.prod * tupleCofactor q i : ℕ) : ZMod (q i)))
    (fun i => greg (q i)) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  have hM : 0 ≤ M := by
    dsimp only [M, naturalRegularMultiplier]
    apply Finset.prod_nonneg
    intro i _
    split_ifs <;> positivity
  let a := positiveLogCutoff φ Jleft (⌊Real.exp x⌋₊ : ℝ)
  let b := positiveLogCutoff φ Jright (⌊Real.exp z⌋₊ : ℝ)
  let d : ℝ := if diagonal then Real.exp Jright / (⌊Real.exp z⌋₊ : ℝ) else 1
  have hd : 0 ≤ d := by dsimp [d]; split_ifs <;> positivity
  have heq : movingTemplateExternalMultiplier P hP n r m active outside greg s φ
      Jleft Jright diagonal y x z = ((a * b * d * M : ℝ) : ℂ) := by
    unfold movingTemplateExternalMultiplier giantOuterWeight
    dsimp only [a, b, d, M, q]
    cases diagonal <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> push_cast <;> rfl
  rw [heq]
  simpa only [Complex.ofReal_re] using
    And.intro (mul_nonneg (mul_nonneg (mul_nonneg (hc _ _) (hc _ _)) hd) hM)
      (Eq.refl ((a * b * d * M : ℝ) : ℂ))

theorem movingTemplateMaskedSymmetrizedEnergy_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (G : ℕ → ℝ) (n r m : ℕ) (hm : 1 ≤ m)
    (ν : MovingRegularSlot n r m → P → ℝ) (hν : ∀ j a, 0 ≤ ν j a)
    (hidentical : ∀ j k, ν (movingTemplateBulk n r m j) = ν (movingTemplateBulk n r m k))
    (active : MovingRegularSlot n r m → Bool)
    (hactive : ∀ j, active (movingTemplateBulk n r m j) = true)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (Jleft Jright : ℝ) (diagonal : Bool)
    (u v a b center D E : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hdiag : (mixedExternalAverage ν (V n) u v a b center (fun s y x z =>
      (‖movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G n r m s y
        ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊‖ ^ 2 : ℂ) *
      movingTemplateExternalMultiplier P hP n r m active outside greg s φ Jleft Jright diagonal y x z)).re ≤ D)
    (hgood : ∀ e : Equiv.Perm (TreeLeafIndex n × Fin m),
      4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤ 3 * Fintype.card (TreeLeafIndex n) →
      ‖mixedExternalAverage ν (V n) u v a b center (fun s y x z =>
        (movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G n r m s y
          ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ *
        star (movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G n r m s
          (selectedBulkSample (movingTemplateBulk n r m) e y) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)) *
        movingTemplateExternalMultiplier P hP n r m active outside greg s φ Jleft Jright diagonal y x z)‖ ≤ E) :
    (movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G n r m
      ν active greg Jleft Jright diagonal u v a b center).re ≤
      (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
        Real.exp ((2 ^ n : ℝ) * m * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4)) * D + E := by
  let C := fun s y x z => movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
    n r m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  let W := fun s y x z => movingTemplateExternalMultiplier P hP n r m active outside greg s φ
    Jleft Jright diagonal y x z
  have hwcast (s : ℤ) (y : MovingRegularSlot n r m → P) (x z : ℝ) :
      ((W s y x z).re : ℂ) = W s y x z :=
    (movingTemplateExternalMultiplier_nonneg P hP n r m active outside greg s φ
      hφ Jleft Jright diagonal y x z).2
  have hd : (mixedExternalAverage ν (V n) u v a b center
      (fun s y x z => (‖C s y x z‖ ^ 2 : ℂ) * (W s y x z).re)).re ≤ D := by
    simp_rw [hwcast]
    exact hdiag
  have hg (e : Equiv.Perm (TreeLeafIndex n × Fin m))
      (he : 4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤ 3 * Fintype.card (TreeLeafIndex n)) :
      ‖mixedExternalAverage ν (V n) u v a b center (fun s y x z =>
        (C s y x z * star (C s (selectedBulkSample (movingTemplateBulk n r m) e y) x z)) *
          (W s y x z).re)‖ ≤ E := by
    simp_rw [hwcast]
    exact hgood e he
  have h := mixedBulkSymmetrize_energy_bound n m hm (movingTemplateBulk n r m) ν hν hidentical
    (V n) u v a b center C (fun s y x z => (W s y x z).re)
    (fun s y x z => (movingTemplateExternalMultiplier_nonneg P hP n r m active outside greg s φ
      hφ Jleft Jright diagonal y x z).1)
    (fun e s y x z => congrArg Complex.re (movingTemplateExternalMultiplier_bulk_action P hP
      n r m active hactive outside greg s φ Jleft Jright diagonal e y x z)) D E hD hE hd hg
  change (mixedExternalAverage ν (V n) u v a b center (fun s y x z =>
    (‖mixedBulkSymmetrize n m (movingTemplateBulk n r m) C s y x z‖ ^ 2 : ℂ) * W s y x z)).re ≤ _
  simpa only [hwcast] using h

end Ostmann

end OAI
