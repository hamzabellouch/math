import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGroupBoxes
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RescaledLieFamily

namespace OAI

/-! # Source generator intervals fit in the containing template box -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] (eW : HeightSpace T.character ≃ₗ[ℝ] W)

theorem exists_source_interval_box_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Set W) (β : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ (s : Fin M.letterCount → ℝ),
        (∀ i, s i ≤ (M.supportIn T hunimod eW).weightSupport E i) →
      ∀ {N : Type*} (Exp : cartanRootIdeal H → N) (r R : ℝ), 0 ≤ r → 0 ≤ R →
      ∀ (i : Fin M.letterCount) (t : ℝ), |t| ≤ R →
        Exp (t • (Real.exp (r * s i) • M.letter i)) ∈
          M.groupBox T hunimod eW Exp E β r (C * R) := by
  obtain ⟨C, hC, hgen⟩ := exists_uniform_rescaled_generator_bound M.letter M.wordList
    M.letter_mem_wordList b₀
  refine ⟨C, hC, ?_⟩
  intro E β hβ s hs N Exp r R hr hR i t ht
  let w := (M.supportIn T hunimod eW).weightSupport E
  let q := Real.exp (r * (s i - w i))
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonneg_of_nonpos hr (sub_nonpos.mpr (hs i))
  have hvec : ‖(M.boxBasis T hunimod eW E β r).equivFun
      (Real.exp (r * w i) • M.letter i)‖ ≤ C :=
    hgen w β hβ r hr i
  have he : t • (Real.exp (r * s i) • M.letter i) =
      (t * q) • (Real.exp (r * w i) • M.letter i) := by
    have hscalar : Real.exp (r * s i) = q * Real.exp (r * w i) := by
      dsimp only [q]
      rw [← Real.exp_add]
      congr 1
      ring
    simpa only [smul_smul, mul_assoc] using
      congrArg (fun a : ℝ => (t * a) • M.letter i) hscalar
  refine ⟨t • (Real.exp (r * s i) • M.letter i), rfl, ?_⟩
  rw [he, map_smul, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hq0, mul_assoc]
  have hb : q * ‖(M.boxBasis T hunimod eW E β r).equivFun
      (Real.exp (r * w i) • M.letter i)‖ ≤ C := by
    exact (mul_le_mul hq1 hvec (norm_nonneg _) zero_le_one).trans_eq (one_mul C)
  calc
    _ ≤ R * C := mul_le_mul ht hb (mul_nonneg hq0.le (norm_nonneg _)) hR
    _ = C * R := mul_comm _ _

end PolycyclicRecognition.CartanWordModel

end

end OAI
