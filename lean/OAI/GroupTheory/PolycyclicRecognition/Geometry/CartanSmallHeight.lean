import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanControlledAction
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TemplateBoxEnvelopes
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # Conjugating a small error by a Cartan factor of small height

The full logarithm of the Cartan factor may be polynomially large. Only its
height contributes to the exponential factor; the residual action contributes
a fixed polynomial. This distinction is needed for thickened probe endpoints.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric Filter
open scoped Topology
open scoped Pointwise

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The estimate is uniform over all input word bases. The output uses
one fixed zero-template basis. -/
theorem exists_small_height_adjoint_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW {0}) β.val) :
    ∃ (A K : ℝ) (p : ℕ), 0 ≤ A ∧ 0 ≤ K ∧
      ∀ (γ : M.Bases) (h : H) (v : cartanRootIdeal H),
        ‖(M.boxBasis T hunimod eW {0} β 1).equivFun
          (cartanIdealAdjointAutomorphism T H h v)‖ ≤
        A * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p *
          Real.exp (K * ‖eW (heightProjection T.character (h : L))‖) *
            ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ := by
  obtain ⟨A, p, hA, haction⟩ := M.exists_controlled_adjoint_bound T hunimod eW b₀
  obtain ⟨D, hD, hcompare⟩ := exists_word_box_comparison_constant M.letter M.wordList b₀
  obtain ⟨K, hK, hcost⟩ := M.exists_boxCost_thickening_constant T hunimod eW
  refine ⟨D * A, K, p, mul_nonneg hD hA, hK, ?_⟩
  intro γ h v
  let w := eW (heightProjection T.character (h : L))
  let E : Set W := ({0} : Set W) + closedBall 0 ‖w‖
  have hE : IsCompact E := isCompact_singleton.add (isCompact_closedBall 0 ‖w‖)
  have hw : w ∈ E := by
    have hh : w ∈ closedBall (0 : W) ‖w‖ := by simp
    simpa only [zero_add] using add_mem_add (mem_singleton (0 : W)) hh
  have hne : E.Nonempty := ⟨w, hw⟩
  obtain ⟨βh, hβh, _⟩ := M.exists_maximizing_box_basis T hunimod eW b₀ E
  have ha := haction hE hne βh hβh γ 1 (by norm_num) h w hw (by simp [w]) v
  have hc := hcompare (M.boxCost T hunimod eW {0}) (M.boxCost T hunimod eW E)
    β βh hβ (r := 1) (ε := K * ‖w‖) (by norm_num)
    (hcost isCompact_singleton (singleton_nonempty (0 : W)) (norm_nonneg w))
    (cartanIdealAdjointAutomorphism T H h v)
  change ‖(M.boxBasis T hunimod eW {0} β 1).equivFun
      (cartanIdealAdjointAutomorphism T H h v)‖ ≤ _ at hc
  rw [mul_one] at hc
  calc
    _ ≤ D * Real.exp (K * ‖w‖) *
        ‖(M.boxBasis T hunimod eW E βh 1).equivFun
          (cartanIdealAdjointAutomorphism T H h v)‖ := hc
    _ ≤ D * Real.exp (K * ‖w‖) *
        (A * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p *
          ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖) :=
      mul_le_mul_of_nonneg_left ha (mul_nonneg hD (Real.exp_pos _).le)
    _ = _ := by dsimp [w]; ring

include hunimod in
/-- The output can use the fixed adapted ideal-section basis. Its
coordinate change only changes the constant, not the height exponent. -/
theorem exists_small_height_adjoint_bound_in_basis
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {J : Type*} [Fintype J] (b : Basis J ℝ (cartanRootIdeal H)) :
    ∃ (A K : ℝ) (p : ℕ), 0 ≤ A ∧ 0 ≤ K ∧
      ∀ (γ : M.Bases) (h : H) (v : cartanRootIdeal H),
        ‖b.equivFun (cartanIdealAdjointAutomorphism T H h v)‖ ≤
        A * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p *
          Real.exp (K * ‖eW (heightProjection T.character (h : L))‖) *
            ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ := by
  obtain ⟨β, hβ, _⟩ := M.exists_maximizing_box_basis T hunimod eW b₀ {0}
  obtain ⟨A, K, p, hA, hK, hbound⟩ :=
    M.exists_small_height_adjoint_bound T hunimod eW b₀ β hβ
  let bZ := M.boxBasis T hunimod eW {0} β 1
  let f := (b.equivFun.toLinearMap.comp bZ.equivFun.symm.toLinearMap).toContinuousLinearMap
  have hf (v : cartanRootIdeal H) : ‖b.equivFun v‖ ≤ ‖f‖ * ‖bZ.equivFun v‖ := by
    simpa only [f, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
      f.le_opNorm (bZ.equivFun v)
  refine ⟨‖f‖ * A, K, p, mul_nonneg (norm_nonneg _) hA, hK, ?_⟩
  intro γ h v
  calc
    _ ≤ ‖f‖ * ‖bZ.equivFun (cartanIdealAdjointAutomorphism T H h v)‖ := hf _
    _ ≤ ‖f‖ * (A * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p *
        Real.exp (K * ‖eW (heightProjection T.character (h : L))‖) *
          ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖) :=
      mul_le_mul_of_nonneg_left (hbound γ h v) (norm_nonneg _)
    _ = _ := by ring

include hunimod in
/-- Polynomial Cartan-log growth and small height preserve a small
exponential error. The constant is independent of the chosen small δ and
of every point in the family. -/
theorem exists_small_height_adjoint_sequence_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {J : Type*} [Fintype J] (b : Basis J ℝ (cartanRootIdeal H))
    (scale RH RE : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hRH0 : ∀ n, 0 ≤ RH n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH)
    (hRE : HasSubexponentialUpperBoundSeq scale RE) :
    ∃ B : ℝ, 0 < B ∧ ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ∀ (γ : M.Bases) (h : H) (v : cartanRootIdeal H),
        ‖(finBasis ℝ H).equivFun h‖ ≤ RH n →
        ‖eW (heightProjection T.character (h : L))‖ ≤ δ * scale n →
        ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ ≤
          RE n * Real.exp (δ * scale n) →
        ‖b.equivFun (cartanIdealAdjointAutomorphism T H h v)‖ ≤
          Real.exp (B * δ * scale n) := by
  obtain ⟨A, K, p, hA, hK, hbound⟩ :=
    M.exists_small_height_adjoint_bound_in_basis T hunimod eW b₀ b
  let R := fun n => A * (1 + RH n) ^ p * RE n
  have hR : HasSubexponentialUpperBoundSeq scale R :=
    ((sequence_subexponential_upper_const hs A).mul
      (((sequence_subexponential_upper_const hs 1).add hRH hs).pow hs
        (Eventually.of_forall (fun n => by linarith [hRH0 n])) p)
      (Eventually.of_forall (fun _ => hA))).mul hRE
      (Eventually.of_forall (fun n => mul_nonneg hA (pow_nonneg (by linarith [hRH0 n]) _)))
  refine ⟨K + 2, by linarith, ?_⟩
  intro δ hδ
  filter_upwards [hR δ hδ] with n hn γ h v hh hw hv
  have hpow : (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p ≤ (1 + RH n) ^ p :=
    pow_le_pow_left₀ (by positivity) (by linarith) p
  have he : Real.exp (K * ‖eW (heightProjection T.character (h : L))‖) ≤
      Real.exp (K * (δ * scale n)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw hK)
  have hr0 : 0 ≤ A * (1 + RH n) ^ p * Real.exp (K * (δ * scale n)) := by
    exact mul_nonneg (mul_nonneg hA (pow_nonneg (by linarith [hRH0 n]) _))
      (Real.exp_nonneg _)
  calc
    _ ≤ A * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p *
        Real.exp (K * ‖eW (heightProjection T.character (h : L))‖) *
          ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ := hbound γ h v
    _ ≤ A * (1 + RH n) ^ p * Real.exp (K * (δ * scale n)) *
        (RE n * Real.exp (δ * scale n)) := by
      apply mul_le_mul _ hv (norm_nonneg _) hr0
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hA) he
        (Real.exp_nonneg _) (mul_nonneg hA (pow_nonneg (by linarith [hRH0 n]) _))
    _ = R n * Real.exp ((K + 1) * δ * scale n) := by
      dsimp [R]
      rw [show (K + 1) * δ * scale n = K * (δ * scale n) + δ * scale n by ring,
        Real.exp_add]
      ring
    _ ≤ Real.exp (δ * scale n) * Real.exp ((K + 1) * δ * scale n) :=
      mul_le_mul_of_nonneg_right hn (Real.exp_nonneg _)
    _ = Real.exp ((K + 2) * δ * scale n) := by
      rw [← Real.exp_add]
      congr 1
      ring

end PolycyclicRecognition.CartanWordModel

end

end OAI
