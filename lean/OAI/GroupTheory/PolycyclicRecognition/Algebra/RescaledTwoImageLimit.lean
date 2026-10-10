import OAI.GroupTheory.PolycyclicRecognition.Analysis.BoxCoordinateChanges
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TwoImageLimits

namespace OAI

/-! # The alternating submersion for actual pairs of rescaled boxes -/

noncomputable section
namespace PolycyclicRecognition

open Module Filter
open scoped Topology

variable {I L : Type*} [Fintype I] [DecidableEq I]
  [LieRing L] [LieAlgebra ℝ L]

def rescaledTwoImageData (X : I → L) (S : Finset (FreeMagma I))
    (β β₁ β₂ : WordBasisSelections X S) (s₁ s₂ : I → ℝ) (r : ℝ) :
    TwoImageData I (finrank ℝ L) :=
  let s := fun i => max (s₁ i) (s₂ i)
  let b := exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun j => bracketWordExponent s (β.val j)) r
  let b₁ := exponentialRescaleBasis (WordBasisSelections.basis X S β₁)
    (fun j => bracketWordExponent s₁ (β₁.val j)) r
  let b₂ := exponentialRescaleBasis (WordBasisSelections.basis X S β₂)
    (fun j => bracketWordExponent s₂ (β₂.val j)) r
  ((rescaledLieData X S β s r, (boxCoordinateChange b b₁, boxCoordinateChange b b₂)),
    ((rescaledLieData X S β₁ s₁ r).2, (rescaledLieData X S β₂ s₂ r).2))

theorem rescaledTwoImageData_generatorsCovered
    (X : I → L) (S : Finset (FreeMagma I))
    (β β₁ β₂ : WordBasisSelections X S) (s₁ s₂ : I → ℝ) (r : ℝ) :
    (rescaledTwoImageData X S β β₁ β₂ s₁ s₂ r).generatorsCovered := by
  intro i
  rcases le_total (s₁ i) (s₂ i) with hi | hi
  · exact Or.inr (rescaled_generator_in_coordinate_image X S β β₂
      (fun i => max (s₁ i) (s₂ i)) s₂ r i (max_eq_right hi))
  · exact Or.inl (rescaled_generator_in_coordinate_image X S β β₁
      (fun i => max (s₁ i) (s₂ i)) s₁ r i (max_eq_left hi))

theorem exists_rescaledTwoImageData_map_bound
    (X : I → L) (S : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (s₁ s₂ : I → ℝ) (β β₁ β₂ : WordBasisSelections X S)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X S b₀)
      (fun w => bracketWordExponent (fun i => max (s₁ i) (s₂ i)) w) β.val) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ r : ℝ, 0 ≤ r →
      ‖(rescaledTwoImageData X S β β₁ β₂ s₁ s₂ r).1.2.1‖ ≤ D ∧
      ‖(rescaledTwoImageData X S β β₁ β₂ s₁ s₂ r).1.2.2‖ ≤ D := by
  obtain ⟨D, hD, hmaps⟩ := exists_uniform_boxCoordinateChange_bound X S b₀
  have hleft (w : S) : bracketWordExponent s₁ w ≤
      bracketWordExponent (fun i => max (s₁ i) (s₂ i)) w :=
    bracketWordExponent_mono (s := s₁) (t := fun i => max (s₁ i) (s₂ i))
      (fun i => le_max_left (s₁ i) (s₂ i)) (w : FreeMagma I)
  have hright (w : S) : bracketWordExponent s₂ w ≤
      bracketWordExponent (fun i => max (s₁ i) (s₂ i)) w :=
    bracketWordExponent_mono (s := s₂) (t := fun i => max (s₁ i) (s₂ i))
      (fun i => le_max_right (s₁ i) (s₂ i)) (w : FreeMagma I)
  refine ⟨D, hD, ?_⟩
  intro r hr
  constructor
  · exact hmaps (fun w => bracketWordExponent (fun i => max (s₁ i) (s₂ i)) w)
      (fun w => bracketWordExponent s₁ w) β β₁ hβ hr
      hleft
  · exact hmaps (fun w => bracketWordExponent (fun i => max (s₁ i) (s₂ i)) w)
      (fun w => bracketWordExponent s₂ w) β β₂ hβ hr
      hright

theorem rescaled_twoImage_submersion_of_bounds
    (X : I → L) (S : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    {c : ℕ} (a : DynkinCoefficients c 2) (C : ℝ)
    (hdata : ∀ (s : I → ℝ) (γ : WordBasisSelections X S),
      IsMaximizingColumnBasis (wordListCoordinates X S b₀)
        (fun w => bracketWordExponent s w) γ.val → ∀ r : ℝ, 0 ≤ r →
      rescaledLieData X S γ s r ∈ normalizedExponentialParameters a
        (fun i => (γ.val i : FreeMagma I)) (fun i => Pi.single i 1) C)
    (s₁ s₂ : I → ℝ) (β β₁ β₂ : WordBasisSelections X S)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X S b₀)
      (fun w => bracketWordExponent (fun i => max (s₁ i) (s₂ i)) w) β.val)
    (hβ₁ : IsMaximizingColumnBasis (wordListCoordinates X S b₀)
      (fun w => bracketWordExponent s₁ w) β₁.val)
    (hβ₂ : IsMaximizingColumnBasis (wordListCoordinates X S b₀)
      (fun w => bracketWordExponent s₂ w) β₂.val)
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 ≤ scale n) :
    HasSubmersiveTwoImageSubsequence a (fun i => (β.val i : FreeMagma I)) C
      (fun n => rescaledTwoImageData X S β β₁ β₂ s₁ s₂ (scale n)) := by
  obtain ⟨D, hD, hmaps⟩ := exists_rescaledTwoImageData_map_bound X S b₀ s₁ s₂ β β₁ β₂ hβ
  let q := fun n => rescaledTwoImageData X S β β₁ β₂ s₁ s₂ (scale n)
  have hp (n : ℕ) : (q n).1.1 ∈ normalizedExponentialParameters a
      (fun i => (β.val i : FreeMagma I)) (fun i => Pi.single i 1) C :=
    hdata (fun i => max (s₁ i) (s₂ i)) β hβ (scale n) (hscale n)
  have hv₁ (n : ℕ) : ‖(q n).2.1‖ ≤ max D C :=
    (hdata s₁ β₁ hβ₁ (scale n) (hscale n)).1.1.2.1.trans (le_max_right D C)
  have hv₂ (n : ℕ) : ‖(q n).2.2‖ ≤ max D C :=
    (hdata s₂ β₂ hβ₂ (scale n) (hscale n)).1.1.2.1.trans (le_max_right D C)
  exact exists_submersive_twoImage_limit a (fun i => (β.val i : FreeMagma I)) C (max D C) q hp
    (fun n => (hmaps (scale n) (hscale n)).1.trans (le_max_left D C))
    (fun n => (hmaps (scale n) (hscale n)).2.trans (le_max_left D C)) hv₁ hv₂
    (fun n => rescaledTwoImageData_generatorsCovered X S β β₁ β₂ s₁ s₂ (scale n))

variable [FiniteDimensional ℝ L] {G A : Type*} [Group G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

theorem exists_rescaled_twoImage_submersion
    (X : I → L) {k : ℕ} (hk : LieModule.lowerCentralSeries ℝ L L k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hzero : Exp 0 = 1) (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    (s₁ s₂ : I → ℝ) (β β₁ β₂ : WordBasisSelections X (boundedBracketWords k))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
      (fun w => bracketWordExponent (fun i => max (s₁ i) (s₂ i)) w) β.val)
    (hβ₁ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
      (fun w => bracketWordExponent s₁ w) β₁.val)
    (hβ₂ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
      (fun w => bracketWordExponent s₂ w) β₂.val)
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 ≤ scale n) :
    ∃ C : ℝ, 0 ≤ C ∧ HasSubmersiveTwoImageSubsequence a
      (fun i => (β.val i : FreeMagma I)) C
      (fun n => rescaledTwoImageData X (boundedBracketWords k) β β₁ β₂ s₁ s₂ (scale n)) := by
  obtain ⟨C, hC, hdata⟩ := exists_rescaledExponentialData_bound X hk hletters b₀
    Exp hinj hzero hneg hadd a hm j ρ hρ hmatch
  exact ⟨C, hC, rescaled_twoImage_submersion_of_bounds X (boundedBracketWords k) b₀
    a C hdata s₁ s₂ β β₁ β₂ hβ hβ₁ hβ₂ scale hscale⟩

end PolycyclicRecognition

end

end OAI
