import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateDiagonal
import OAI.NumberTheory.Ostmann.Arithmetic.MovingGroupedBulkAverage
import OAI.NumberTheory.Ostmann.Arithmetic.MovingHarmonicGroupedEnergy
import OAI.NumberTheory.Ostmann.Construction.SelectedBulkSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingHarmonicDiagonal
import OAI.NumberTheory.Ostmann.Construction.SmoothGiantPrior

namespace OAI

/-! # The restored diagonal under the original giant and regular priors -/

namespace Ostmann
open scoped Classical BigOperators

/-- The original harmonic product law pays the giant atom and a single
factorial product-fibre cost. The frequency range contributes no cardinality
factor, because the diagonal key includes the frequency itself. -/
theorem movingTemplate_symmetrized_harmonic_diagonal_le
    (P Pg : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPg : ∀ p ∈ Pg, p.Prime)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) (G : ℕ → ℝ)
    (cg : ℝ)
    (n r m : ℕ) (Q : MovingRegularSlot n r m → Finset ℕ)
    (hν : ∀ j k : TreeLeafIndex n × Fin m,
      primeSubsetPrior P (Q (movingTemplateBulk n r m j)) =
        primeSubsetPrior P (Q (movingTemplateBulk n r m k)))
    (u : TreeLeafIndex n × Fin 4 → P) (p : ℕ)
    (hvg : ∀ q : Pg, V n < (q : ℕ)) (hvr : ∀ q : P, V n < (q : ℕ))
    (hsep : ∀ q : Pg, ∀ a : P, (q : ℕ) ≠ (a : ℕ))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    let A := Pg × ((MovingRegularSlot n r m → P) × transferFrequencyRange (V n))
    let X := fun a : A => (a.1 : ℕ)
    let y := fun a : A => a.2.1
    let v := fun a : A => (a.2.2 : ℤ)
    let _ : ∀ a, Fact (X a).Prime := fun a => ⟨hPg _ a.1.property⟩
    let _ : ∀ a i, Fact (y a i : ℕ).Prime := fun a i => ⟨hP _ (y a i).property⟩
    let α := fun a : A => smoothGiantPrior Pg φ cg a.1 *
      ∏ i, primeSubsetPrior P (Q i) (y a i)
    let C := fun a : A => movingTemplateCoefficient (fun q : P => (q : ℕ)) outside μ
      childBound pivotBound V F φ G n (4 + r) m (v a)
        (movingRestoreSample n r m u (y a)) p (X a)
    let Csym := fun a : A => mixedBulkSymmetrize n m (movingTemplateBulk n r m)
      (fun _ z _ _ => C (a.1, z, a.2.2)) 0 (y a) 0 0
    let θ := fun a : A => (Real.exp (smoothGiantLogNormalizer Pg φ cg) / X a) *
      ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹) * ((∏ i, (y a i : ℕ)) : ℝ)⁻¹
    let D := p * (∏ i, (u i : ℕ)) * outside.prod
    (pivotDiagonal (fun a => X a * ∏ i, (y a i : ℕ)) v
      (fun a => (α a : ℂ) * C a *
        movingRegularTransform (movingOneGiantModuli (X a) (fun i => (y a i : ℕ)))
          (movingOneGiantFactors (X a) (fun i => (y a i : ℕ)) greg ggiant favorable) D (v a))).re ≤
      ∑ a, α a * θ a *
        ‖Csym a * primeProductTransform greg (D * X a) (∏ i, (y a i : ℕ)) (v a)‖ ^ 2 := by
  intro A X y v instX instY α C Csym θ D
  let g := fun q : ℕ => Real.exp (smoothGiantLogNormalizer Pg φ cg) / q
  have hg q : 0 ≤ g q := div_nonneg (Real.exp_nonneg _) (Nat.cast_nonneg _)
  have hα a : 0 ≤ α a :=
    mul_nonneg (smoothGiantPrior_nonneg Pg φ cg hφ0 a.1)
      (Finset.prod_nonneg (fun i _ => primeSubsetPrior_nonneg P (Q i) (y a i)))
  have hpoint a : α a ≤ g (X a) * ∏ i, primeSubsetPrior P (Q i) (y a i) := by
    apply mul_le_mul_of_nonneg_right _
      (Finset.prod_nonneg (fun i _ => primeSubsetPrior_nonneg P (Q i) (y a i)))
    change Real.exp (smoothGiantLogNormalizer Pg φ cg) * φ (Real.log (a.1 : ℕ) - cg) /
      (a.1 : ℕ) ≤ Real.exp (smoothGiantLogNormalizer Pg φ cg) / (a.1 : ℕ)
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (Real.exp_nonneg _) (hφ1 _)) (Nat.cast_nonneg _)
  have hrow (a b : A) (hx : X a = X b) (hy : y a = y b) (hv : v a = v b) : a = b :=
    Prod.ext (Subtype.ext hx) (Prod.ext hy (Subtype.ext hv))
  have hc a (ha : (α a : ℂ) * C a ≠ 0) : C a ≠ 0 := right_ne_zero_of_mul ha
  have hinjC a (ha : C a ≠ 0) : Function.Injective (y a) := by
    have hs := movingTemplateCoefficient_restored_support (fun q : P => (q : ℕ)) outside μ
      childBound pivotBound V F φ G n r m (v a) u (y a) p (X a) ha
    intro i j hij
    by_contra hne
    have hh := hs.2.2.1 (show (Sum.inr i : Unit ⊕ MovingRegularSlot n r m) ≠ .inr j from
      fun he => hne (Sum.inr.inj he))
    change (y a i : ℕ).Coprime (y a j : ℕ) at hh
    rw [hij] at hh
    exact (hP _ (y a j).property).ne_one (by simpa only [Nat.coprime_self] using hh)
  have hinj a (ha : (α a : ℂ) * C a ≠ 0) := hinjC a (hc a ha)
  have hnewinj a (ha : (α a : ℂ) * Csym a ≠ 0) : Function.Injective (y a) := by
    obtain ⟨e, he⟩ := mixedBulkSymmetrize_ne_zero n m (movingTemplateBulk n r m)
      (fun _ z _ _ => C (a.1, z, a.2.2)) 0 (y a) 0 0 (right_ne_zero_of_mul ha)
    have hi := hinjC (a.1, selectedBulkSample (movingTemplateBulk n r m) e (y a), a.2.2) he
    exact (selectedBulkSample_injective_iff (movingTemplateBulk n r m) e id (y a)).mp hi
  have hgroup (k : ℕ × ℕ × ℤ) :
      groupedCoefficient (fun a => (X a, (∏ i, (y a i : ℕ)), v a))
        (fun a => (α a : ℂ) * C a) k =
      groupedCoefficient (fun a => (X a, (∏ i, (y a i : ℕ)), v a))
        (fun a => (α a : ℂ) * Csym a) k := by
    exact (movingAmplitude_grouped_bulk_average P Pg n r m V
      (smoothGiantPrior Pg φ cg) (fun i => primeSubsetPrior P (Q i)) hν C k).symm
  have hz a (ha : (α a : ℂ) * C a ≠ 0) : v a ≠ 0 := by
    intro he
    apply hc a ha
    simpa only [C, movingTemplateCoefficient, he] using
      movingFrequencyCoefficient_zero (fun q : P => (q : ℕ)) outside μ
        childBound pivotBound V F hF φ G n
        (treeLeafMap (List.map (movingRestoreSample n r m u (y a))) n
          (movingTemplateSmall n (4 + r) m))
        (treeLeafMap (List.map (movingRestoreSample n r m u (y a))) n
          (bulkSlotLeaves n m (movingTemplateBulk n (4 + r) m))) p (X a)
  have h := movingOneGiant_harmonic_grouped_diagonal_le P hP Q X
    (fun a => hPg _ a.1.property) y v α C Csym hα g hg hrow hpoint hinj hz
    (fun a _ => ((mem_transferFrequencyRange _ _).mp a.2.2.property).trans_lt (hvg a.1))
    (fun a _ i => ((mem_transferFrequencyRange _ _).mp a.2.2.property).trans_lt (hvr (y a i)))
    (fun a b _ _ i => hsep a.1 (y b i)) hgroup hnewinj greg ggiant favorable D
  simpa only [g, θ, Nat.cast_prod] using h

end Ostmann

end OAI
