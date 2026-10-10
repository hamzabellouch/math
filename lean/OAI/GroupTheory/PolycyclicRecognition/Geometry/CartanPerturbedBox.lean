import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGroupBoxes
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledBasisChange
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MixedWordBoxModel
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # Subexponential corrections to endpoint-tuple increments

For a template containing zero, its scaled box contains the corresponding
unscaled box. Left and right corrections with subexponential logarithms
therefore preserve the template and change only its subexponential radius.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

theorem norm_boxBasis_le_unscaled_of_zero_mem {E : Set W}
    (hE : IsCompact E) (h0 : (0 : W) ∈ E) (β : M.Bases)
    {r : ℝ} (hr : 0 ≤ r) (v : cartanRootIdeal H) :
    ‖(M.boxBasis T hunimod eW E β r).equivFun v‖ ≤
      ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun v‖ := by
  let b := WordBasisSelections.basis M.letter M.wordList β
  have hs (i : Fin M.letterCount) :
      0 ≤ (M.supportIn T hunimod eW).weightSupport E i := by
    simpa only [map_zero] using (M.supportIn T hunimod eW).weight_le_weightSupport hE h0 i
  have hc (j : Fin (finrank ℝ (cartanRootIdeal H))) :
      0 ≤ M.boxCost T hunimod eW E (β.val j) :=
    bracketWordExponent_nonneg _ hs _
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (b.equivFun v))).mpr
  intro j
  change |(M.boxBasis T hunimod eW E β r).repr v j| ≤ _
  have he := repr_exponentialRescaleBasis_smul b
    (fun j => M.boxCost T hunimod eW E (β.val j)) r 0 v j
  simp only [mul_zero, Real.exp_zero, one_smul, zero_sub] at he
  rw [show (M.boxBasis T hunimod eW E β r).repr v j =
    b.repr v j * Real.exp (r * -M.boxCost T hunimod eW E (β.val j)) from he]
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ ‖b.equivFun v‖ * 1 := mul_le_mul (norm_le_pi_norm (b.equivFun v) j)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hr (neg_nonpos.mpr (hc j))))
      (Real.exp_pos _).le (norm_nonneg _)
    _ = _ := mul_one _

variable {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]

theorem exists_subexponential_perturbed_groupBox
    (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
    (dynkin : NilpotentDynkinExpansionInput EN N)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (h0 : (0 : W) ∈ E) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (scale R S : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 0 ≤ scale n) (hR0 : ∀ n, 0 ≤ R n) (hS0 : ∀ n, 0 ≤ S n)
    (hR : HasSubexponentialUpperBoundSeq scale R)
    (hS : HasSubexponentialUpperBoundSeq scale S) :
    ∃ Q : ℕ → ℝ, (∀ n, 0 ≤ Q n) ∧ HasSubexponentialUpperBoundSeq scale Q ∧
      ∀ n (x u y : N),
        x ∈ exponentialCoordinateBox (Exp ∘ eN)
          (WordBasisSelections.basis M.letter M.wordList β) (S n) →
        u ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (R n) →
        y ∈ exponentialCoordinateBox (Exp ∘ eN)
          (WordBasisSelections.basis M.letter M.wordList β) (S n) →
        x⁻¹ * u * y ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (Q n) := by
  obtain ⟨C, hC, hprod⟩ := M.exists_groupBox_product_bound T hunimod eW eN Exp hExp dynkin b₀
  let Q := fun n => (C * 4 ^ M.bound) * (1 + (R n + S n)) ^ M.bound
  have hsum0 (n : ℕ) : 0 ≤ 1 + (R n + S n) := by linarith [hR0 n, hS0 n]
  have hsum := (sequence_subexponential_upper_const hs 1).add (hR.add hS hs) hs
  refine ⟨Q, fun n => mul_nonneg (mul_nonneg hC (by positivity))
    (pow_nonneg (hsum0 n) _), ?_, ?_⟩
  · exact (sequence_subexponential_upper_const hs (C * 4 ^ M.bound)).mul
      (hsum.pow hs (Eventually.of_forall hsum0) M.bound)
      (Eventually.of_forall (fun _ => mul_nonneg hC (by positivity)))
  intro n x u y hx hu hy
  have hsmall {g : N} (hg : g ∈ exponentialCoordinateBox (Exp ∘ eN)
      (WordBasisSelections.basis M.letter M.wordList β) (S n)) :
      g ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (R n + S n) := by
    obtain ⟨v, hv, hb⟩ := hg
    exact ⟨v, hv, (M.norm_boxBasis_le_unscaled_of_zero_mem T hunimod eW hE h0 β
      (hscale n) v).trans (hb.trans (le_add_of_nonneg_left (hR0 n)))⟩
  have hu' : u ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (R n + S n) := by
    obtain ⟨v, hv, hb⟩ := hu
    exact ⟨v, hv, hb.trans (le_add_of_nonneg_right (hS0 n))⟩
  have hp := hprod E β hβ (scale n) (hscale n) 3 (R n + S n)
    (add_nonneg (hR0 n) (hS0 n)) ![x⁻¹, u, y] (by
      intro i
      fin_cases i
      · exact M.groupBox_inv_mem T hunimod eW eN Exp hExp E β _ _ (hsmall hx)
      · exact hu'
      · exact hsmall hy)
  simpa [Q, mul_assoc, show (1 : ℝ) + 3 = 4 by norm_num] using hp

end PolycyclicRecognition.CartanWordModel

end

end OAI
