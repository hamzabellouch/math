import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxSchemes
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledTwoImageLimit
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ReflectedSegmentSupport
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlternatingPolynomialCoordinates

namespace OAI

/-! # Selecting the alternating scheme from the actual Cartan boxes

The full limiting multiplication map is selected before any restriction to
good profiles or any choice of separated target tuples.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Filter Set
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The actual two boxes have a common subsequence and a full alternating
submersion. Only their intrinsic exponential representation and Haar chart
are taken from published inputs. -/
theorem exists_alternating_box_scheme
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (b : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {c : ℕ} (aN : DynkinCoefficients c 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (E₁ E₂ : Set W) (hE₁ : IsCompact E₁) (hne₁ : E₁.Nonempty)
    (hE₂ : IsCompact E₂) (hne₂ : E₂.Nonempty)
    (β β₁ β₂ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b)
      (M.boxCost T hunimod eW (E₁ ∪ E₂)) β.val)
    (hβ₁ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b)
      (M.boxCost T hunimod eW E₁) β₁.val)
    (hβ₂ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b)
      (M.boxCost T hunimod eW E₂) β₂.val)
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 ≤ scale n) :
    ∃ C : ℝ, 0 ≤ C ∧ HasSubmersiveTwoImageSubsequence aN
      (fun i => (β.val i : FreeMagma (Fin M.letterCount))) C
      (fun n => rescaledTwoImageData M.letter M.wordList β β₁ β₂
        ((M.supportIn T hunimod eW).weightSupport E₁)
        ((M.supportIn T hunimod eW).weightSupport E₂) (scale n)) := by
  let s₁ := (M.supportIn T hunimod eW).weightSupport E₁
  let s₂ := (M.supportIn T hunimod eW).weightSupport E₂
  have hmax : (M.supportIn T hunimod eW).weightSupport (E₁ ∪ E₂) =
      fun i => max (s₁ i) (s₂ i) := by
    funext i
    exact (M.supportIn T hunimod eW).weightSupport_union hE₁ hne₁ hE₂ hne₂ i
  have hcost : M.boxCost T hunimod eW (E₁ ∪ E₂) =
      fun w : M.wordList => bracketWordExponent (fun i => max (s₁ i) (s₂ i)) w := by
    funext w
    exact congrArg (fun s => bracketWordExponent s (w : FreeMagma (Fin M.letterCount))) hmax
  have hβ' : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b)
      (fun w => bracketWordExponent (fun i => max (s₁ i) (s₂ i)) w) β.val := by
    exact hcost ▸ hβ
  obtain ⟨C, hC, hb⟩ := M.exists_box_normalized_bound T F hunimod eW hExp realize haarN
    b aN hm (E₁ ∪ E₂) β hβ
  obtain ⟨C₁, _, hb₁⟩ := M.exists_box_normalized_bound T F hunimod eW hExp realize haarN
    b aN hm E₁ β₁ hβ₁
  obtain ⟨C₂, _, hb₂⟩ := M.exists_box_normalized_bound T F hunimod eW hExp realize haarN
    b aN hm E₂ β₂ hβ₂
  obtain ⟨D, _, hmaps⟩ := exists_rescaledTwoImageData_map_bound M.letter M.wordList b
    s₁ s₂ β β₁ β₂ hβ'
  let q := fun n => rescaledTwoImageData M.letter M.wordList β β₁ β₂ s₁ s₂ (scale n)
  refine ⟨C, hC, exists_submersive_twoImage_limit aN
    (fun i => (β.val i : FreeMagma (Fin M.letterCount))) C (max D (max C₁ C₂)) q ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro n
    simpa only [q, rescaledTwoImageData, hmax] using hb (scale n) (hscale n)
  · intro n
    exact (hmaps (scale n) (hscale n)).1.trans (le_max_left _ _)
  · intro n
    exact (hmaps (scale n) (hscale n)).2.trans (le_max_left _ _)
  · intro n
    exact (hb₁ (scale n) (hscale n)).1.1.2.1.trans
      ((le_max_left C₁ C₂).trans (le_max_right D _))
  · intro n
    exact (hb₂ (scale n) (hscale n)).1.1.2.1.trans
      ((le_max_right C₁ C₂).trans (le_max_right D _))
  · intro n
    exact rescaledTwoImageData_generatorsCovered M.letter M.wordList β β₁ β₂ s₁ s₂ (scale n)

end PolycyclicRecognition.CartanWordModel

namespace PolycyclicRecognition

/-- A submersion to positive-dimensional coordinates has at least one block. -/
theorem alternating_submersion_length_pos {n h c : ℕ} (hn : 0 < n)
    (a : DynkinCoefficients c 2) (p : AlternatingLawData n)
    (z : Fin h → (Fin n → ℝ) × (Fin n → ℝ))
    (hs : Function.Surjective (fderiv ℝ (alternatingCoordinateProduct a p.1 p.2.1 p.2.2) z)) :
    0 < h := by
  by_contra hh
  have he : h = 0 := Nat.eq_zero_of_not_pos hh
  subst h
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨v, hv⟩ := hs 1
  have hv0 : v = 0 := Subsingleton.elim _ _
  rw [hv0, map_zero] at hv
  exact zero_ne_one hv

end PolycyclicRecognition

end

end OAI
