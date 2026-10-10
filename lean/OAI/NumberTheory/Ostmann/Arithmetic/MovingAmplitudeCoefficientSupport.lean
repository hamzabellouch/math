import OAI.NumberTheory.Ostmann.Arithmetic.MovingNodeCoefficientSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingConstructedLiveProductStep

namespace OAI

/-! # The full moving transfer with separation on its actual coefficient support -/
namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

private theorem coefficient_amplitude_pair_sum {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (ρ : A → ℝ) (ν : B → ℝ) (F : A → A → B → B → C → C → ℂ) :
    (∑ a : A × (B × C), ∑ b : A × (B × C),
      ((ρ a.1 * ν a.2.1 : ℝ) : ℂ) * ((ρ b.1 * ν b.2.1 : ℝ) : ℂ) *
        F a.1 b.1 a.2.1 b.2.1 a.2.2 b.2.2) =
      ∑ x, (ρ x : ℂ) * ∑ z, (ρ z : ℂ) *
        ∑ y, (ν y : ℂ) * ∑ t, (ν t : ℂ) * ∑ v, ∑ w, F x z y t v w := by
  simp only [Fintype.sum_prod_type, Finset.mul_sum, Complex.ofReal_mul]
  conv_lhs =>
    arg 2
    ext x
    arg 2
    ext y
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext x
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext x
    arg 2
    ext z
    arg 2
    ext y
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  ring

private theorem coefficient_amplitude_full_sum {U S A B C : Type}
    [Fintype U] [Fintype S] [Fintype A] [Fintype B] [Fintype C]
    (M : U → ℂ) (ρ : A → ℝ) (ν : B → ℝ)
    (F : U → S → A → A → B → B → C → C → ℂ) :
    (∑ u, M u * ∑ s, ∑ a : A × (B × C), ∑ b : A × (B × C),
      ((ρ a.1 * ν a.2.1 : ℝ) : ℂ) * ((ρ b.1 * ν b.2.1 : ℝ) : ℂ) *
        F u s a.1 b.1 a.2.1 b.2.1 a.2.2 b.2.2) =
    ∑ XL, (ρ XL : ℂ) * ∑ XR, (ρ XR : ℂ) * ∑ s, ∑ u, M u *
      ∑ left, (ν left : ℂ) * ∑ right, (ν right : ℂ) * ∑ v, ∑ w,
        F u s XL XR left right v w := by
  simp_rw [coefficient_amplitude_pair_sum]
  simp only [Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro XL _
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro XR _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem movingAmplitudeOffDiagonal_eq_next_on_coefficients {σ : Type} [Fintype σ]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Pg : Finset ℕ) (hPg : ∀ q ∈ Pg, q.Prime) (ρ : Pg → ℝ)
    (ν : MovingRegularSlot n r m → σ → ℝ)
    (hlarge : ∀ q : Pg, V (n + 1) < (q : ℕ))
    (I : Finset ℕ) (hI : ∀ p ∈ I, 0 < p)
    (hφ : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : ∀ XR : Pg, ∀ right : MovingRegularSlot n r m → σ, (∏ i, ν i (right i)) ≠ 0 →
      ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ) (w : ℤ),
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m w
        (movingRestoreSample n r m u right) p XR ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < (XR : ℕ) * ∏ i, value (right i))
    (hRH : ∀ XR : Pg, ∀ right : MovingRegularSlot n r m → σ, (∏ i, ν i (right i)) ≠ 0 →
      ∀ q, q.Prime → q ∣ (XR : ℕ) * (∏ i, value (right i)) → V (n + 1) < q)
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    movingAmplitudeOffDiagonal value outside μ childBound pivotBound V F φ G n r m Pg I
      ρ ν greg ggiant favorable =
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G (n + 1) r m
      Pg ρ (movingTemplateDoubledPrior n r m ν) greg ggiant favorable := by
  rw [movingTemplatePrimeAmplitude_next_on_coefficients value hvalue outside μ childBound pivotBound V hV
    F hF φ G n r m Pg hPg ρ (movingTemplateDoubledPrior n r m ν) hlarge I hI hφ hchild
    (by simpa only [movingTemplateDoubledPrior_side] using hgap)
    (by simpa only [movingTemplateDoubledPrior_side] using hRH) hcomp]
  simp only [movingTemplateDoubledPrior_side]
  unfold movingAmplitudeOffDiagonal
  dsimp only [movingAmplitudePrior]
  have hr := coefficient_amplitude_full_sum
    (U := TreeLeafIndex n × Fin 4 → σ) (S := transferFrequencyRange (V (n + 1)))
    (A := Pg) (B := MovingRegularSlot n r m → σ) (C := transferFrequencyRange (V n))
    (fun u => (((∏ i, μ n (u i)) * (∏ i, value (u i) : ℕ) : ℝ) : ℂ))
    ρ (fun y => ∏ i, ν i (y i))
    (fun u s XL XR left right v w => movingTemplateIntegerFourierTerm value outside μ
      childBound pivotBound V F φ G n r m I XL XR s.val left right greg ggiant favorable
        u v.val w.val)
  convert hr using 1
  simp only [Nat.cast_prod]

theorem movingTemplatePrimeAmplitude_step_on_coefficients {σ : Type} [Fintype σ]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime)
    (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Pg I : Finset ℕ) (hPg : ∀ p ∈ Pg, p.Prime) (hPI : Pg ⊆ I)
    (hI : ∀ p ∈ I, 0 < p) (hφ : ∀ x, 0 ≤ φ x)
    (hpos : 0 < smoothGiantMass Pg φ (G (n + 1)))
    (hμ : ∀ a, 0 ≤ μ n a) (hμmass : ∑ a, μ n a = 1)
    (ν : MovingRegularSlot n r m → σ → ℝ)
    (sets : ∀ q : ℕ, Finset (ZMod q))
    (hsets : ∀ a, (sets (value a)).Nonempty)
    (hcard : ∀ a, (sets (value a)).card < value a)
    (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (hgiant : ∀ q : Pg, ∀ x, ggiant q (-x) = conj (ggiant q x))
    (H : ℕ)
    (hH : ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ), p ∈ I →
      ∀ (q : Pg) (y : MovingRegularSlot n r m → σ) (s : transferFrequencyRange (V n)),
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
        n (4 + r) m s.val (movingRestoreSample n r m u y) p q ≠ 0 →
        (q : ℕ) * (∏ i, value (y i)) ≤ H)
    (hscale : ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 → ∀ p ∈ I,
      2 * V n * H ≤ V (n + 1) * (p * ∏ i, value (u i)))
    (hlarge : ∀ (q : Pg) (y : MovingRegularSlot n r m → σ),
      (∏ i, ν i (y i)) ≠ 0 → ∀ ℓ, ℓ.Prime → ℓ ∣ (q : ℕ) * (∏ i, value (y i)) → V (n + 1) < ℓ)
    (hvg : ∀ q : Pg, V (n + 1) < (q : ℕ))
    (hφsupport : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : ∀ XR : Pg, ∀ right : MovingRegularSlot n r m → σ, (∏ i, ν i (right i)) ≠ 0 →
      ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ) (w : ℤ),
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m w
        (movingRestoreSample n r m u right) p XR ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < (XR : ℕ) * ∏ i, value (right i))
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q)) :
    let ρ := smoothGiantPrior Pg φ (G (n + 1))
    let greg := normalizedResidueFamily sets
    Real.exp (-smoothGiantLogNormalizer Pg φ (G (n + 1))) *
      ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n (4 + r) m
        Pg ρ (movingTemplateRestoredPrior n r m (μ n) ν) greg ggiant favorable‖ ^ 2 ≤
      movingAmplitudeDiagonal value outside μ childBound pivotBound V F φ G n r m Pg I
        ρ ν greg ggiant favorable +
      ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G (n + 1) r m
        Pg ρ (movingTemplateDoubledPrior n r m ν) greg ggiant favorable‖ := by
  intro ρ greg
  have he := movingAmplitudeOffDiagonal_eq_next_on_coefficients value hvalue outside μ childBound pivotBound V
    hV F hF φ G n r m Pg hPg ρ ν hvg I hI hφsupport hchild hgap
    (fun XR right hr => hlarge XR right hr) hcomp greg ggiant favorable
  rw [← he]
  exact movingTemplatePrimeAmplitude_transfer_on_live value hvalue outside μ childBound pivotBound V F
    φ G n r m Pg I hPg hPI hI hφ hpos hμ hμmass ν sets hsets hcard ggiant favorable
    hgiant H hH hscale hlarge

theorem movingTemplatePrimeAmplitude_step_of_live_coefficients {σ J : Type} [Fintype σ]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime)
    (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (q : J → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (hF : ∀ {n} (T : MovingSlotData σ n), F T 0 = 0)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J)
    (ψ : SchwartzMap ℝ ℂ) (X lo hi W : ℝ) (hX : 0 < X)
    (hwindow : X * hi ≤ Real.exp W)
    (φ : ℝ → ℝ) (G c : ℕ → ℝ) (hout : ∀ t, 1 ≤ |t| → φ t = 0)
    (hμlower : ∀ j x, μ j x ≠ 0 → Real.exp (c j - 1) ≤ (value x : ℝ))
    (n r m : ℕ)
    (Pg I : Finset ℕ) (hPg : ∀ p ∈ Pg, p.Prime) (hPI : Pg ⊆ I)
    (hI : ∀ p ∈ I, 0 < p) (hφ : ∀ x, 0 ≤ φ x)
    (hpos : 0 < smoothGiantMass Pg φ (G (n + 1)))
    (hμ : ∀ a, 0 ≤ μ n a) (hμmass : ∑ a, μ n a = 1)
    (ν : MovingRegularSlot n r m → σ → ℝ)
    (sets : ∀ q : ℕ, Finset (ZMod q))
    (hsets : ∀ a, (sets (value a)).Nonempty)
    (hcard : ∀ a, (sets (value a)).card < value a)
    (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (hgiant : ∀ q : Pg, ∀ x, ggiant q (-x) = conj (ggiant q x))
    (H : ℕ)
    (hcap : ⌈Real.exp (movingProductExponent (movingCellPivotExponent G c) W n -
      movingCellPivotExponent G c n)⌉₊ ≤ H)
    (hIlower : ∀ p ∈ I, Real.exp (G (n + 1) - 1) ≤ (p : ℝ))
    (hscale : ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 → ∀ p ∈ I,
      2 * V n * H ≤ V (n + 1) * (p * ∏ i, value (u i)))
    (hlarge : ∀ (q : Pg) (y : MovingRegularSlot n r m → σ),
      (∏ i, ν i (y i)) ≠ 0 → ∀ ℓ, ℓ.Prime → ℓ ∣ (q : ℕ) * (∏ i, value (y i)) → V (n + 1) < ℓ)
    (hvg : ∀ q : Pg, V (n + 1) < (q : ℕ))
    (hφsupport : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : ∀ XR : Pg, ∀ right : MovingRegularSlot n r m → σ, (∏ i, ν i (right i)) ≠ 0 →
      ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ) (w : ℤ),
      movingTemplateCoefficient value outside μ childBound pivotBound V (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n (4 + r) m w
        (movingRestoreSample n r m u right) p XR ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < (XR : ℕ) * ∏ i, value (right i))
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q)) :
    let ρ := smoothGiantPrior Pg φ (G (n + 1))
    let greg := normalizedResidueFamily sets
    Real.exp (-smoothGiantLogNormalizer Pg φ (G (n + 1))) *
      ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n (4 + r) m
        Pg ρ (movingTemplateRestoredPrior n r m (μ n) ν) greg ggiant favorable‖ ^ 2 ≤
      movingAmplitudeDiagonal value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n r m Pg I
        ρ ν greg ggiant favorable +
      ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G (n + 1) r m
        Pg ρ (movingTemplateDoubledPrior n r m ν) greg ggiant favorable‖ := by
  let F₀ := movingOriginalLeaf value q F g Dq S ψ X lo hi
  have hzero : ∀ x, F₀ x 0 = 0 :=
    movingOriginalLeaf_zero value q F hF g Dq S ψ X lo hi
  have hH (u : TreeLeafIndex n × Fin 4 → σ) (hu : (∏ i, μ n (u i)) ≠ 0)
      (p : ℕ) (hp : p ∈ I) (q' : Pg) (y : MovingRegularSlot n r m → σ)
      (s : transferFrequencyRange (V n))
      (hc : movingTemplateCoefficient value outside μ childBound pivotBound V F₀ φ G
        n (4 + r) m s.val (movingRestoreSample n r m u y) p q' ≠ 0) :
      (q' : ℕ) * (∏ i, value (y i)) ≤ H :=
    (movingTemplateCoefficient_recursive_cell_cap value outside μ childBound pivotBound V
      q F g Dq S ψ X lo hi W hX hwindow φ G c hout hμlower n r m u hu
      s.val y p q' (hIlower p hp) hc).trans hcap
  exact movingTemplatePrimeAmplitude_step_on_coefficients value hvalue outside μ childBound pivotBound V
    hV F₀ hzero φ G n r m Pg I hPg hPI hI hφ hpos hμ hμmass ν sets hsets hcard
    ggiant favorable hgiant H hH hscale hlarge hvg hφsupport hchild hgap hcomp

theorem movingTemplatePrimeAmplitude_step_constructed_coefficients {σ J : Type} [Fintype σ]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime)
    (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (q : J → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (hF : ∀ {n} (T : MovingSlotData σ n), F T 0 = 0)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J)
    (ψ : SchwartzMap ℝ ℂ) (X lo hi W : ℝ) (hX : 0 < X)
    (hwindow : X * hi ≤ Real.exp W)
    (φ : ℝ → ℝ) (G c : ℕ → ℝ) (hout : ∀ t, 1 ≤ |t| → φ t = 0)
    (hμlower : ∀ j x, μ j x ≠ 0 → Real.exp (c j - 1) ≤ (value x : ℝ))
    (n r m : ℕ) (Y reserveMass : ℝ) (hm : 64 ≤ reserveMass) (hY : Y ≤ W)
    (hVeq : V = movingProductNaturalCutoff (movingCellPivotExponent G c) W Y reserveMass)
    (hbudget : ∀ j, 2 * movingCellPivotExponent G c j ≤
      movingProductExponent (movingCellPivotExponent G c) W j)
    (hpositive : 0 ≤ movingProductExponent (movingCellPivotExponent G c) W n -
      movingCellPivotExponent G c n)
    (Pg I : Finset ℕ) (hPg : ∀ p ∈ Pg, p.Prime) (hPI : Pg ⊆ I)
    (hI : ∀ p ∈ I, 0 < p) (hφ : ∀ x, 0 ≤ φ x)
    (hpos : 0 < smoothGiantMass Pg φ (G (n + 1)))
    (hμ : ∀ a, 0 ≤ μ n a) (hμmass : ∑ a, μ n a = 1)
    (ν : MovingRegularSlot n r m → σ → ℝ)
    (sets : ∀ q : ℕ, Finset (ZMod q))
    (hsets : ∀ a, (sets (value a)).Nonempty)
    (hcard : ∀ a, (sets (value a)).card < value a)
    (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (hgiant : ∀ q : Pg, ∀ x, ggiant q (-x) = conj (ggiant q x))
    (H : ℕ)
    (hHeq : H = ⌈Real.exp (movingProductExponent (movingCellPivotExponent G c) W n -
      movingCellPivotExponent G c n)⌉₊)
    (hIlower : ∀ p ∈ I, Real.exp (G (n + 1) - 1) ≤ (p : ℝ))
    (hlarge : ∀ (q : Pg) (y : MovingRegularSlot n r m → σ),
      (∏ i, ν i (y i)) ≠ 0 → ∀ ℓ, ℓ.Prime → ℓ ∣ (q : ℕ) * (∏ i, value (y i)) → V (n + 1) < ℓ)
    (hvg : ∀ q : Pg, V (n + 1) < (q : ℕ))
    (hφsupport : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : ∀ XR : Pg, ∀ right : MovingRegularSlot n r m → σ, (∏ i, ν i (right i)) ≠ 0 →
      ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ) (w : ℤ),
      movingTemplateCoefficient value outside μ childBound pivotBound V (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n (4 + r) m w
        (movingRestoreSample n r m u right) p XR ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < (XR : ℕ) * ∏ i, value (right i))
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q)) :
    let ρ := smoothGiantPrior Pg φ (G (n + 1))
    let greg := normalizedResidueFamily sets
    Real.exp (-smoothGiantLogNormalizer Pg φ (G (n + 1))) *
      ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n (4 + r) m
        Pg ρ (movingTemplateRestoredPrior n r m (μ n) ν) greg ggiant favorable‖ ^ 2 ≤
      movingAmplitudeDiagonal value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n r m Pg I
        ρ ν greg ggiant favorable +
      ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G (n + 1) r m
        Pg ρ (movingTemplateDoubledPrior n r m ν) greg ggiant favorable‖ := by
  have hV : Monotone V := by
    rw [hVeq]
    exact movingProductNaturalCutoff_monotone (movingCellPivotExponent G c) W Y reserveMass hbudget
  have hcap : ⌈Real.exp (movingProductExponent (movingCellPivotExponent G c) W n -
      movingCellPivotExponent G c n)⌉₊ ≤ H := by rw [hHeq]
  have hscale (u : TreeLeafIndex n × Fin 4 → σ) (hu : (∏ i, μ n (u i)) ≠ 0)
      (p : ℕ) (hp : p ∈ I) : 2 * V n * H ≤ V (n + 1) * (p * ∏ i, value (u i)) := by
    rw [hVeq, hHeq]
    exact movingProductNaturalCutoff_compensation_scale value μ G c hμlower W Y reserveMass
      hm hY hbudget n hpositive u hu p (hIlower p hp)
  exact movingTemplatePrimeAmplitude_step_of_live_coefficients value hvalue outside μ childBound pivotBound V hV
    q F hF g Dq S ψ X lo hi W hX hwindow φ G c hout hμlower n r m Pg I hPg hPI hI hφ
    hpos hμ hμmass ν sets hsets hcard ggiant favorable hgiant H hcap hIlower hscale
    hlarge hvg hφsupport hchild hgap hcomp

end Ostmann

end OAI
