import OAI.Analysis.KadisonSimilarity.Representation.SpectralSteps
import OAI.Analysis.FactorGeneration.Bicommutant
import Mathlib.Analysis.CStarAlgebra.Commutative.PosPart
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.InnerProductSpace.StarOrder

namespace OAI

/-! # Concrete spectral cut projections

We construct the spectral cuts from the closed range of the positive part.
The construction takes place in the represented Hilbert space; bicommutant
closure proves membership in the given von Neumann algebra.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Closed range used to construct the support projection of an operator. -/
def operatorRangeClosure (B : H →L[ℂ] H) : Submodule ℂ H :=
  B.range.topologicalClosure

instance operatorRangeClosure_complete (B : H →L[ℂ] H) :
    CompleteSpace (operatorRangeClosure B) :=
  inferInstanceAs (CompleteSpace B.range.topologicalClosure)

/-- The orthogonal projection onto the closed operator range. -/
def rangeSupport (B : H →L[ℂ] H) : H →L[ℂ] H :=
  (operatorRangeClosure B).starProjection

theorem rangeSupport_isStarProjection (B : H →L[ℂ] H) :
    IsStarProjection (rangeSupport B) :=
  ⟨Submodule.isIdempotentElem_starProjection _, isSelfAdjoint_starProjection _⟩

theorem rangeSupport_mul (B : H →L[ℂ] H) : rangeSupport B * B = B := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr
    (Submodule.le_topologicalClosure _ ⟨x, rfl⟩)

theorem mul_rangeSupport (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) :
    B * rangeSupport B = B := by
  have h := congrArg star (rangeSupport_mul B)
  simpa only [star_mul, hB.star_eq, (rangeSupport_isStarProjection B).isSelfAdjoint.star_eq]
    using h

omit [CompleteSpace H] in
theorem operatorRangeClosure_invariant (B T : H →L[ℂ] H) (h : Commute B T)
    {x : H} (hx : x ∈ operatorRangeClosure B) : T x ∈ operatorRangeClosure B := by
  have hh : B.range.topologicalClosure ≤
      (operatorRangeClosure B).comap T.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨y, rfl⟩
      apply Submodule.le_topologicalClosure
      refine ⟨T y, ?_⟩
      exact congrArg (fun S : H →L[ℂ] H => S y) h.eq
    · exact (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  exact hh hx

theorem rangeSupport_commutes (B T : H →L[ℂ] H)
    (h : Commute B T) (hs : Commute B (star T)) : Commute (rangeSupport B) T := by
  exact Generator.starProjection_commutes_of_invariant _ T
    (fun _ hx => operatorRangeClosure_invariant B T h hx)
    (fun _ hx => operatorRangeClosure_invariant B (star T) hs hx)

theorem rangeSupport_mem (P : VonNeumannAlgebra H) (B : H →L[ℂ] H) (hB : B ∈ P) :
    rangeSupport B ∈ P := by
  suffices rangeSupport B ∈ P.commutant.commutant by simpa using this
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  have h : Commute B T := VonNeumannAlgebra.mem_commutant_iff.mp hT B hB
  have hs : Commute B (star T) := VonNeumannAlgebra.mem_commutant_iff.mp
    (star_mem hT) B hB
  exact (rangeSupport_commutes B T h hs).eq.symm

/-- Annihilating the range also annihilates its orthogonal support. -/
theorem mul_rangeSupport_eq_zero (B C : H →L[ℂ] H) (h : C * B = 0) :
    C * rangeSupport B = 0 := by
  have hh : operatorRangeClosure B ≤ C.ker := by
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨x, rfl⟩
      exact congrArg (fun S : H →L[ℂ] H => S x) h
    · exact C.isClosed_ker
  ext x
  exact hh ((operatorRangeClosure B).starProjection_apply_mem x)

/-- The open upper spectral cut `(t,∞)` of a selfadjoint operator. -/
def upperSpectralCut (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  rangeSupport ((A - t • 1)⁺)

theorem upperSpectralCut_isStarProjection (A : H →L[ℂ] H) (t : ℝ) :
    IsStarProjection (upperSpectralCut A t) := rangeSupport_isStarProjection _

theorem upperSpectralCut_mem (P : VonNeumannAlgebra H) (A : H →L[ℂ] H)
    (hA : A ∈ P) (t : ℝ) : upperSpectralCut A t ∈ P := by
  apply rangeSupport_mem P
  let : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
    change IsClosed P.carrier
    rw [← P.centralizer_centralizer']
    exact Set.isClosed_centralizer _
  apply cfcₙ_mem (𝕜' := ℂ) (s := P.toStarSubalgebra) (fun x : ℝ => x⁺)
  apply P.toStarSubalgebra.sub_mem hA
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact P.toStarSubalgebra.smul_mem P.one_mem (t : ℂ)

/-- Multiplication by a cut removes the negative part of the shifted operator. -/
theorem shifted_mul_upperSpectralCut (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    (A - t • 1) * upperSpectralCut A t = (A - t • 1)⁺ := by
  let B := A - t • (1 : H →L[ℂ] H)
  have hB : IsSelfAdjoint B := by
    dsimp [B]
    exact hA.sub ((IsSelfAdjoint.all t).smul (IsSelfAdjoint.one (H →L[ℂ] H)))
  change B * rangeSupport B⁺ = B⁺
  nth_rw 1 [← CFC.posPart_sub_negPart B hB]
  rw [sub_mul]
  rw [mul_rangeSupport B⁺ (CFC.posPart_nonneg B).isSelfAdjoint,
    mul_rangeSupport_eq_zero B⁺ B⁻ (CFC.negPart_mul_posPart B), sub_zero]

theorem shifted_mul_complement_upperSpectralCut (A : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (t : ℝ) :
    (A - t • 1) * (1 - upperSpectralCut A t) = -(A - t • 1)⁻ := by
  rw [mul_sub, mul_one, shifted_mul_upperSpectralCut A hA t]
  have hB : IsSelfAdjoint (A - t • (1 : H →L[ℂ] H)) :=
    hA.sub ((IsSelfAdjoint.all t).smul (IsSelfAdjoint.one (H →L[ℂ] H)))
  nth_rw 1 [← CFC.posPart_sub_negPart _ hB]
  abel


/-- A positive operator supported by a projection is bounded by its norm
 times that projection. -/
theorem nonneg_le_norm_smul_support (B p : H →L[ℂ] H)
    (hB : 0 ≤ B) (hp : IsStarProjection p) (hpB : p * B = B) (hBp : B * p = B) :
    B ≤ ‖B‖ • p := by
  simpa only [hp.isSelfAdjoint.star_eq, hpB, hBp, hp.isIdempotentElem.eq] using
    CStarAlgebra.star_left_conjugate_le_norm_smul p B hB.isSelfAdjoint

/-- One binary spectral correction. -/
def binarySpectralCorrection (B : H →L[ℂ] H) (r : ℝ) : H →L[ℂ] H :=
  r • rangeSupport B⁺ - (r / 2) • 1

/-- Binary rounding halves the norm bound without changing the algebra. -/
theorem norm_sub_binarySpectralCorrection_le (B : H →L[ℂ] H)
    (hB : IsSelfAdjoint B) {r : ℝ} (hr : 0 ≤ r) (hBr : ‖B‖ ≤ r) :
    ‖B - binarySpectralCorrection B r‖ ≤ r / 2 := by
  let p := rangeSupport B⁺
  have hp : IsStarProjection p := rangeSupport_isStarProjection _
  have hq : IsStarProjection (1 - p) := hp.one_sub
  have hpos : 0 ≤ B⁺ := CFC.posPart_nonneg B
  have hneg : 0 ≤ B⁻ := CFC.negPart_nonneg B
  have hpn : B⁻ * p = 0 := mul_rangeSupport_eq_zero B⁺ B⁻ (CFC.negPart_mul_posPart B)
  have hnp : p * B⁻ = 0 := by
    have h := congrArg star hpn
    simpa only [star_mul, hp.isSelfAdjoint.star_eq, hneg.isSelfAdjoint.star_eq,
      star_zero] using h
  have hposBound : B⁺ ≤ r • p :=
    (nonneg_le_norm_smul_support B⁺ p hpos hp
      (rangeSupport_mul _) (mul_rangeSupport _ hpos.isSelfAdjoint)).trans
      (smul_le_smul_of_nonneg_right
        ((CStarAlgebra.norm_posPart_le B).trans hBr) hp.nonneg)
  have hnegBound : B⁻ ≤ r • (1 - p) := by
    apply (nonneg_le_norm_smul_support B⁻ (1 - p) hneg hq
      (by simp only [sub_mul, one_mul, hnp, sub_zero])
      (by simp only [mul_sub, mul_one, hpn, sub_zero])).trans
    exact smul_le_smul_of_nonneg_right
      ((CStarAlgebra.norm_negPart_le B).trans hBr) hq.nonneg
  have hupper : B ≤ r • p := by
    calc
      B = B⁺ - B⁻ := (CFC.posPart_sub_negPart B hB).symm
      _ ≤ B⁺ := sub_le_self _ hneg
      _ ≤ r • p := hposBound
  have hlower : r • p - r • 1 ≤ B := by
    calc
      r • p - r • 1 = -(r • (1 - p)) := by module
      _ ≤ -B⁻ := neg_le_neg hnegBound
      _ ≤ B⁺ - B⁻ := by simpa only [zero_sub] using sub_le_sub_right hpos B⁻
      _ = B := CFC.posPart_sub_negPart B hB
  have hlo : -((r / 2) • (1 : H →L[ℂ] H)) ≤ B - binarySpectralCorrection B r := by
    have h := add_le_add_right (sub_le_sub_right hlower (r • p)) ((r / 2) • 1)
    convert h using 1 <;> dsimp [binarySpectralCorrection, p] <;> module
  have hhi : B - binarySpectralCorrection B r ≤ (r / 2) • (1 : H →L[ℂ] H) := by
    have h := add_le_add_right (sub_le_sub_right hupper (r • p)) ((r / 2) • 1)
    convert h using 1 <;> dsimp [binarySpectralCorrection, p] <;> module
  have hself : IsSelfAdjoint (B - binarySpectralCorrection B r) :=
    hB.sub (((IsSelfAdjoint.all r).smul hp.isSelfAdjoint).sub
      ((IsSelfAdjoint.all (r / 2)).smul (IsSelfAdjoint.one (H →L[ℂ] H))))
  have hnormOne : ‖(r / 2) • (1 : H →L[ℂ] H)‖ ≤ r / 2 := by
    calc
      _ = |r / 2| * ‖(1 : H →L[ℂ] H)‖ := norm_smul _ _
      _ ≤ (r / 2) * 1 := by rw [abs_of_nonneg (by positivity)]; gcongr; exact ContinuousLinearMap.norm_id_le
      _ = r / 2 := mul_one _
  exact (IsSelfAdjoint.norm_le_max_of_le_of_le hlo hhi hself).trans
    (by simpa only [norm_neg, max_self] using hnormOne)

/-- The prescribed geometric error radius. -/
def binarySpectralRadius (A : H →L[ℂ] H) (k : ℕ) : ℝ := ‖A‖ * (1 / 2 : ℝ) ^ k

omit [CompleteSpace H] in
theorem binarySpectralRadius_nonneg (A : H →L[ℂ] H) (k : ℕ) :
    0 ≤ binarySpectralRadius A k := by unfold binarySpectralRadius; positivity

omit [CompleteSpace H] in
theorem binarySpectralRadius_succ (A : H →L[ℂ] H) (k : ℕ) :
    binarySpectralRadius A (k + 1) = binarySpectralRadius A k / 2 := by
  simp only [binarySpectralRadius, pow_succ]
  ring

/-- Repeated binary rounding, performed inside the given operator algebra. -/
def binarySpectralResidual (A : H →L[ℂ] H) : ℕ → H →L[ℂ] H
  | 0 => A
  | k + 1 => binarySpectralResidual A k -
      binarySpectralCorrection (binarySpectralResidual A k) (binarySpectralRadius A k)

theorem binarySpectralResidual_selfAdjoint (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (k : ℕ) : IsSelfAdjoint (binarySpectralResidual A k) := by
  induction k with
  | zero => exact hA
  | succ k ih =>
    exact ih.sub (((IsSelfAdjoint.all _).smul
      (rangeSupport_isStarProjection _).isSelfAdjoint).sub
      ((IsSelfAdjoint.all _).smul (IsSelfAdjoint.one (H →L[ℂ] H))))

theorem binarySpectralResidual_norm_le (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (k : ℕ) : ‖binarySpectralResidual A k‖ ≤ binarySpectralRadius A k := by
  induction k with
  | zero => simp [binarySpectralResidual, binarySpectralRadius]
  | succ k ih =>
    rw [binarySpectralRadius_succ]
    exact norm_sub_binarySpectralCorrection_le _
      (binarySpectralResidual_selfAdjoint A hA k) (binarySpectralRadius_nonneg A k) ih

theorem real_smul_mem_vonNeumann (P : VonNeumannAlgebra H) (r : ℝ)
    (T : H →L[ℂ] H) (hT : T ∈ P) : r • T ∈ P := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact P.toStarSubalgebra.smul_mem hT (r : ℂ)

theorem positive_rangeSupport_mem (P : VonNeumannAlgebra H)
    (A : H →L[ℂ] H) (hA : A ∈ P) : rangeSupport A⁺ ∈ P := by
  simpa only [upperSpectralCut, zero_smul, sub_zero] using upperSpectralCut_mem P A hA 0

theorem binarySpectralResidual_mem (P : VonNeumannAlgebra H)
    (A : H →L[ℂ] H) (hA : A ∈ P) (k : ℕ) : binarySpectralResidual A k ∈ P := by
  induction k with
  | zero => exact hA
  | succ k ih =>
    exact P.toStarSubalgebra.sub_mem ih (P.toStarSubalgebra.sub_mem
      (real_smul_mem_vonNeumann P _ _ (positive_rangeSupport_mem P _ ih))
      (real_smul_mem_vonNeumann P _ _ P.one_mem))

theorem binarySpectralResidual_eq_sub_sum (A : H →L[ℂ] H) (n : ℕ) :
    binarySpectralResidual A n = A - ∑ k ∈ Finset.range n,
      binarySpectralCorrection (binarySpectralResidual A k) (binarySpectralRadius A k) := by
  induction n with
  | zero => simp [binarySpectralResidual]
  | succ n ih =>
    change binarySpectralResidual A n -
      binarySpectralCorrection (binarySpectralResidual A n) (binarySpectralRadius A n) = _
    rw [Finset.sum_range_succ]
    exact (congrArg (fun T => T -
      binarySpectralCorrection (binarySpectralResidual A n) (binarySpectralRadius A n)) ih).trans
      (by abel)

omit [CompleteSpace H] in
theorem sum_binarySpectralRadius_le (A : H →L[ℂ] H) (n : ℕ) :
    ∑ i : Fin n, |binarySpectralRadius A i| ≤ 2 * ‖A‖ := by
  simp_rw [abs_of_nonneg (binarySpectralRadius_nonneg A _)]
  unfold binarySpectralRadius
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ‖A‖ * (1 / 2 : ℝ) ^ i) n, ← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (sum_geometric_two_le n) (norm_nonneg A)
  simpa only [mul_comm] using h

omit [CompleteSpace H] in
theorem binarySpectralRadius_tendsto_zero (A : H →L[ℂ] H) :
    Filter.Tendsto (binarySpectralRadius A) Filter.atTop (nhds 0) := by
  change Filter.Tendsto (fun k : ℕ => ‖A‖ * (1 / 2 : ℝ) ^ k) _ _
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) < 1 by norm_num)).const_mul ‖A‖

/-- The accumulated binary corrections have exactly the required scalar
 offset and projection coefficients. -/
theorem spectralStep_binary_eq_sum (A : H →L[ℂ] H) (n : ℕ) :
    spectralStep (-(∑ i : Fin n, binarySpectralRadius A i / 2))
      (fun i : Fin n => binarySpectralRadius A i)
      (fun i : Fin n => rangeSupport (binarySpectralResidual A i)⁺) =
      ∑ k ∈ Finset.range n,
        binarySpectralCorrection (binarySpectralResidual A k) (binarySpectralRadius A k) := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [spectralStep, binarySpectralCorrection, Finset.sum_sub_distrib,
    RCLike.real_smul_eq_coe_smul (K := ℂ), Complex.ofReal_neg, Complex.ofReal_sum,
    neg_smul, ← Finset.sum_smul]
  module

/-- The required published spectral approximation is constructed directly:
 each binary correction halves the residual norm, while all coefficients
 together cost at most twice the original norm. -/
theorem spectralStepApproximation (P : VonNeumannAlgebra H) : SpectralStepApproximation P := by
  intro A hAP hA δ hδ
  have hself : IsSelfAdjoint A := hA
  obtain ⟨n, hn⟩ := ((binarySpectralRadius_tendsto_zero A).eventually
    (gt_mem_nhds hδ)).exists
  refine ⟨n, -(∑ i : Fin n, binarySpectralRadius A i / 2),
    (fun i : Fin n => binarySpectralRadius A i),
    (fun i : Fin n => rangeSupport (binarySpectralResidual A i)⁺), ?_,
    sum_binarySpectralRadius_le A n, ?_⟩
  · intro i
    exact ⟨positive_rangeSupport_mem P _ (binarySpectralResidual_mem P A hAP i),
      (rangeSupport_isStarProjection _).isSelfAdjoint.star_eq,
      (rangeSupport_isStarProjection _).isIdempotentElem.eq⟩
  · rw [spectralStep_binary_eq_sum, ← binarySpectralResidual_eq_sub_sum]
    exact (binarySpectralResidual_norm_le A hself n).trans hn.le

end KadisonSimilarity

end

end OAI
