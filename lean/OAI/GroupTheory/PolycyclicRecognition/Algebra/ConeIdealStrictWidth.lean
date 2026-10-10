import OAI.GroupTheory.PolycyclicRecognition.Geometry.ConeIdealInsideAdjoint
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentCoordinateFlow

namespace OAI

/-! # Strict width absorbs the inside-letter conjugation flow

The flow here is the finite exponential of the actual restricted adjoint.
No box inclusion is an input. A positive width gap absorbs its polynomial
growth uniformly over every point of the smaller box.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module Filter
open scoped Topology

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

def coneIdealLetterFlow (i : Fin M.letterCount) (t : ℝ) (v : M.coneWordIdeal C) :
    M.coneWordIdeal C := finiteEndFlow (M.coneIdealLetterAdjoint C i) M.bound t v

theorem exists_positive_coneIdeal_width (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, 0 ≤ s i)
    (hpos : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → 0 < s i) :
    ∃ lo : ℝ, 0 < lo ∧ ∀ w : M.coneIdealWordList C, lo ≤ M.coneIdealWordCost C s w := by
  classical
  cases isEmpty_or_nonempty (M.coneIdealWordList C) with
  | inl he => exact ⟨1, zero_lt_one, fun w => isEmptyElim w⟩
  | inr he =>
    obtain ⟨w, _, hw⟩ := Finset.exists_min_image Finset.univ
      (fun w : M.coneIdealWordList C => M.coneIdealWordCost C s w) Finset.univ_nonempty
    exact ⟨_, M.coneIdealWordCost_pos C s hs hpos w, fun v => hw v (Finset.mem_univ v)⟩

theorem norm_coneIdealBoxBasis_strict_width
    (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C)
    {a b lo r : ℝ} (hab : a ≤ b) (hr : 0 ≤ r)
    (hlo : ∀ w : M.coneIdealWordList C, lo ≤ M.coneIdealWordCost C s w)
    (v : M.coneWordIdeal C) :
    ‖(M.coneIdealBoxBasis C (fun i => b * s i) β r).equivFun v‖ ≤
      Real.exp (-((b - a) * lo) * r) *
        ‖(M.coneIdealBoxBasis C (fun i => a * s i) β r).equivFun v‖ := by
  unfold coneIdealBoxBasis
  rw [mul_comm (-((b - a) * lo)) r]
  apply norm_change_exponentialRescaleBasis_le _ _ _ hr _ v
  intro j
  rw [M.coneIdealWordCost_smul, M.coneIdealWordCost_smul]
  have hh := mul_le_mul_of_nonpos_left (hlo (β.val j)) (sub_nonpos.mpr hab)
  nlinarith

/-- For a fixed strict width gap, all logarithmic conjugating times below
the corresponding exponential threshold send the whole unit box into the
larger unit box. Negative times are included. -/
theorem coneIdealLetterFlow_absorbed
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C b₀ s β)
    (i : Fin M.letterCount) (hi : s i = 0)
    {a b lo α : ℝ} (ha : 0 ≤ a) (hab : a < b) (hα : 0 ≤ α)
    (hlo : ∀ w : M.coneIdealWordList C, lo ≤ M.coneIdealWordCost C s w)
    (hgap : (M.bound : ℝ) * α < (b - a) * lo)
    (t ε : ℝ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (ht : ∀ᶠ r in atTop, |t r| ≤ Real.exp ((α + ε r) * r)) :
    ∀ᶠ r in atTop, ∀ v : M.coneWordIdeal C,
      ‖(M.coneIdealBoxBasis C (fun j => a * s j) β r).equivFun v‖ ≤ 1 →
      ‖(M.coneIdealBoxBasis C (fun j => b * s j) β r).equivFun
        (M.coneIdealLetterFlow C i (t r) v)‖ ≤ 1 := by
  cases isEmpty_or_nonempty (Fin (finrank ℝ (M.coneWordIdeal C))) with
  | inl he =>
    exact Filter.Eventually.of_forall fun r v _ => by
      have hz := Subsingleton.elim
        ((M.coneIdealBoxBasis C (fun j => b * s j) β r).equivFun
          (M.coneIdealLetterFlow C i (t r) v))
        (0 : Fin (finrank ℝ (M.coneWordIdeal C)) → ℝ)
      rw [hz, norm_zero]
      exact zero_le_one
  | inr he =>
    obtain ⟨A, hA, hbound⟩ := M.exists_uniform_coneIdealLetterAdjoint_bound C b₀
    let br := fun r => M.coneIdealBoxBasis C (fun j => b * s j) β r
    let D := M.coneIdealLetterAdjoint C i
    have hpow : D ^ (M.bound + 1) = 0 := by
      rw [pow_succ, M.coneIdealLetterAdjoint_nilpotent, zero_mul]
    have hDr (r : ℝ) : coordinateEnd (br r) D ^ (M.bound + 1) = 0 :=
      coordinateEnd_pow_zero (br r) D hpow
    have hbd : ∀ᶠ r in atTop, ‖coordinateEnd (br r) D‖ ≤ A := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
      apply ContinuousLinearMap.opNorm_le_bound _ hA
      intro x
      have hh := hbound (fun j => b * s j) β
        (M.maximizing_coneIdealBasis_smul C b₀ s β hβ (ha.trans hab.le))
        i (by rw [hi, mul_zero]) r hr ((br r).equivFun.symm x)
      change ‖(br r).equivFun (D ((br r).equivFun.symm x))‖ ≤
        A * ‖(br r).equivFun ((br r).equivFun.symm x)‖ at hh
      simpa only [coordinateEnd_apply, LinearEquiv.apply_symm_apply] using hh
    have hsmall := eventually_uniform_nilpotent_exp_ball
      (fun r => coordinateEnd (br r) D) t hDr hA hα hgap ε hε hbd ht
    filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with r hsmall hr v hv
    have hvr : ‖(br r).equivFun v‖ ≤ Real.exp (-((b - a) * lo) * r) := by
      exact (M.norm_coneIdealBoxBasis_strict_width C s β hab.le hr hlo v).trans
        (by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hv (Real.exp_pos (-((b - a) * lo) * r)).le)
    have hh := hsmall ((br r).equivFun v) hvr
    rw [← coordinate_finiteEndFlow (br r) D (M.coneIdealLetterAdjoint_nilpotent C i)] at hh
    exact hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
