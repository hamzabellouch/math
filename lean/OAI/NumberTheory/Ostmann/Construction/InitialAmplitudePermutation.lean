import OAI.NumberTheory.Ostmann.Construction.InitialMovingSmallPermutation
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateAmplitude
import OAI.NumberTheory.Ostmann.Construction.FiniteFormulaRenaming

namespace OAI

/-! # Reordering actual small-cell laws preserves the initial amplitude -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem finite_prior_reindex_invariant {V A : Type*} [Fintype V] [Fintype A]
    (e : Equiv.Perm V) (ν : V → A → ℝ) (F : (V → A) → ℂ)
    (hF : ∀ x, F (x ∘ e.symm) = F x) :
    (∑ x : V → A, ((∏ i, ν (e i) (x i) : ℝ) : ℂ) * F x) =
      ∑ x : V → A, ((∏ i, ν i (x i) : ℝ) : ℂ) * F x := by
  have he := finite_prior_reindex e ν F
  simpa only [hF] using he

theorem movingTaggedTransform_small_perm {A : Type} (value : A → ℕ)
    (hvalue : ∀ a, value a ≠ 0) (r m : ℕ) (e : Equiv.Perm (Fin r))
    (y : MovingRegularSlot 0 r m → A) (XL XR : ℕ) (hXL : XL ≠ 0) (hXR : XR ≠ 0)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) :
    movingTaggedTransform
      (Sum.elim (fun a : Bool => if a then XL else XR)
        (value ∘ (y ∘ movingSmallSlotEquiv 0 m e)))
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable D s =
    movingTaggedTransform
      (Sum.elim (fun a : Bool => if a then XL else XR) (value ∘ y))
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable D s := by
  let E := Equiv.sumCongr (Equiv.refl Bool) (movingSmallSlotEquiv 0 m e)
  let p : Bool ⊕ MovingRegularSlot 0 r m → ℕ :=
    Sum.elim (fun a : Bool => if a then XL else XR) (value ∘ y)
  have hp : ∀ i, p i ≠ 0 := by
    intro i
    rcases i with a | i
    · cases a <;> assumption
    · exact hvalue _
  have hpull : p ∘ E = Sum.elim (fun a : Bool => if a then XL else XR)
      (value ∘ (y ∘ movingSmallSlotEquiv 0 m e)) := by
    funext i
    cases i <;> rfl
  have hflag : (Sum.elim (fun _ : Bool => true)
      (fun _ : MovingRegularSlot 0 r m => false)) ∘ E =
      Sum.elim (fun _ => true) (fun _ => false) := by
    funext i
    cases i <;> rfl
  have he := movingTaggedTransform_equiv E p hp
    (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable D s
  rw [hpull, hflag] at he
  exact he

theorem movingTemplatePrimeAmplitude_small_perm {A : Type} [Fintype A]
    (value : A → ℕ) (hvalue : ∀ a, value a ≠ 0)
    (outside : List ℕ) (μ : ℕ → A → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState A → ℤ → ℂ) (φ : ℝ → ℝ) (G : ℕ → ℝ) (r m : ℕ)
    (Pg : Finset ℕ) (hPg : ∀ p ∈ Pg, p ≠ 0) (ρ : Pg → ℝ)
    (ν : MovingRegularSlot 0 r m → A → ℝ) (e : Equiv.Perm (Fin r))
    (hC : ∀ s y XL XR,
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G 0 r m s
        (y ∘ movingSmallSlotEquiv 0 m e.symm) XL XR =
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G 0 r m s
        y XL XR)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G 0 r m Pg ρ
      (fun i => ν (movingSmallSlotEquiv 0 m e i)) greg ggiant favorable =
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G 0 r m Pg ρ
      ν greg ggiant favorable := by
  unfold movingTemplatePrimeAmplitude
  apply Finset.sum_congr rfl
  intro XL _
  apply congrArg (fun z : ℂ => (ρ XL : ℂ) * z)
  apply Finset.sum_congr rfl
  intro XR _
  apply congrArg (fun z : ℂ => (ρ XR : ℂ) * z)
  apply Finset.sum_congr rfl
  intro s _
  let term := fun y : MovingRegularSlot 0 r m → A =>
    movingTemplateCoefficient value outside μ childBound pivotBound V F φ G 0 r m s.val
      y XL XR * movingTaggedTransform
      (Sum.elim (fun a : Bool => if a then (XL : ℕ) else (XR : ℕ)) (value ∘ y))
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s.val
  have hterm : ∀ y, term (y ∘ (movingSmallSlotEquiv 0 m e).symm) = term y := by
    intro y
    change term (y ∘ movingSmallSlotEquiv 0 m e.symm) = term y
    dsimp only [term]
    rw [hC]
    rw [movingTaggedTransform_small_perm value hvalue r m e.symm y XL XR
      (hPg _ XL.property) (hPg _ XR.property)]
  have he := finite_prior_reindex_invariant (movingSmallSlotEquiv 0 m e) ν term hterm
  simpa only [term, finite_univ_canonical] using he

theorem movingTemplatePrimeAmplitude_initial_small_permutation {A J : Type} [Fintype A]
    (value : A → ℕ) (hvalue : ∀ a, value a ≠ 0)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → A) (fallback : A)
    (q : J → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → A → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Pg : Finset ℕ) (hPg : ∀ p ∈ Pg, p ≠ 0) (ρ : Pg → ℝ)
    (ν : MovingRegularSlot 0 (r + r) (b + b) → A → ℝ)
    (e : Equiv.Perm (Fin (r + r)))
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G 0 (r + r) (b + b) Pg ρ
      (fun i => ν (movingSmallSlotEquiv 0 (b + b) e i)) greg ggiant favorable =
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G 0 (r + r) (b + b) Pg ρ ν greg ggiant favorable := by
  exact movingTemplatePrimeAmplitude_small_perm value hvalue outside μ childBound pivotBound V
    _ φ G (r + r) (b + b) Pg hPg ρ ν e
    (fun s y XL XR => movingTemplateCoefficient_initial_zero_small_perm value b d r cb cd
      sl sr fallback q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G s
      e.symm y XL XR) greg ggiant favorable

theorem movingTemplatePrimeAmplitude_initial_small_equiv {A J : Type} [Fintype A]
    (value : A → ℕ) (hvalue : ∀ a, value a ≠ 0)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → A) (fallback : A)
    (q : J → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → A → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Pg : Finset ℕ) (hPg : ∀ p ∈ Pg, p ≠ 0) (ρ : Pg → ℝ)
    (rnew : ℕ) (ν : MovingRegularSlot 0 rnew (b + b) → A → ℝ)
    (e : Fin (r + r) ≃ Fin rnew)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G 0 (r + r) (b + b) Pg ρ
      (fun i => ν (movingSmallSlotEquiv 0 (b + b) e i)) greg ggiant favorable =
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G 0 rnew (b + b) Pg ρ ν greg ggiant favorable := by
  have hr : r + r = rnew := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst rnew
  exact movingTemplatePrimeAmplitude_initial_small_permutation value hvalue b d r cb cd
    sl sr fallback q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G Pg hPg ρ ν e
    greg ggiant favorable

end Ostmann

end OAI
