import OAI.Analysis.KadisonSimilarity.Representation.SpectralStepDischarge
import OAI.Analysis.KadisonSimilarity.Tracial.GNSTracialGeometry

namespace OAI

/-! Quantitative high spectral cuts. The discarded part has small operator
norm, and positivity bounds the trace of the retained projection. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem upperSpectralCut_commutes_self (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    Commute (upperSpectralCut A t) A := by
  have h : Commute (A - t • 1) A := by
    change (A - t • 1) * A = A * (A - t • 1)
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hp : Commute (A - t • 1)⁺ A := by
    rw [CFC.posPart_def]
    exact h.cfcₙ_real _
  exact rangeSupport_commutes _ A hp (by simpa only [hA.star_eq] using hp)

/-- The high cut of a positive operator is bounded in order by that operator. -/
theorem smul_upperSpectralCut_le (A : H →L[ℂ] H) (hA : 0 ≤ A) (t : ℝ) :
    t • upperSpectralCut A t ≤ A := by
  let p := upperSpectralCut A t
  have hp : IsStarProjection p := upperSpectralCut_isStarProjection A t
  have hpa : Commute p A := upperSpectralCut_commutes_self A hA.isSelfAdjoint t
  have hc : Commute A (1 - p) := by
    change A * (1 - p) = (1 - p) * A
    rw [mul_sub, sub_mul, mul_one, one_mul, hpa.eq]
  have hfirst : 0 ≤ A * (1 - p) := Commute.mul_nonneg hA hp.one_sub.nonneg hc
  have hsecond : 0 ≤ (A - t • 1) * p := by
    rw [shifted_mul_upperSpectralCut A hA.isSelfAdjoint t]
    exact CFC.posPart_nonneg _
  apply sub_nonneg.mp
  have heq : A - t • p = A * (1 - p) + (A - t • 1) * p := by
    simp only [mul_sub, sub_mul, mul_one, smul_mul_assoc, one_mul]
    abel
  rw [heq]
  exact add_nonneg hfirst hsecond

/-- Removing the high cut of `x x*` leaves operator norm at most `ε`. -/
theorem norm_complement_upperSpectralCut_mul_le (x : H →L[ℂ] H)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ‖(1 - upperSpectralCut (x * star x) (ε ^ 2)) * x‖ ≤ ε := by
  let A := x * star x
  let p := upperSpectralCut A (ε ^ 2)
  let q := 1 - p
  let B := q * x
  have hA : 0 ≤ A := mul_star_self_nonneg x
  have hp : IsStarProjection p := upperSpectralCut_isStarProjection A _
  have hq : IsStarProjection q := hp.one_sub
  have hpa : Commute p A := upperSpectralCut_commutes_self A hA.isSelfAdjoint _
  have hqa : q * A = A * q := by
    dsimp [q]
    rw [sub_mul, mul_sub, one_mul, mul_one, hpa.eq]
  have hu : A * q ≤ ε ^ 2 • q := by
    apply sub_nonpos.mp
    have heq : A * q - ε ^ 2 • q = (A - ε ^ 2 • 1) * q := by
      simp only [sub_mul, smul_mul_assoc, one_mul]
    rw [heq, shifted_mul_complement_upperSpectralCut A hA.isSelfAdjoint _]
    exact neg_nonpos.mpr (CFC.negPart_nonneg _)
  have hBB : B * star B = A * q := by
    change (q * x) * star (q * x) = A * q
    rw [star_mul, hq.isSelfAdjoint.star_eq]
    calc
      (q * x) * (star x * q) = (q * A) * q := by dsimp [A]; noncomm_ring
      _ = A * q := by rw [hqa, mul_assoc, hq.isIdempotentElem.eq]
  have hle : B * star B ≤ ε ^ 2 • (1 : H →L[ℂ] H) := by
    rw [hBB]
    exact hu.trans (smul_le_smul_of_nonneg_left
      (show q ≤ 1 from sub_le_self _ hp.nonneg) (sq_nonneg ε))
  have hn : ‖B‖ * ‖B‖ ≤ ε ^ 2 := by
    rw [← CStarRing.norm_self_mul_star]
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg ε)
      (mul_star_self_nonneg B)).mpr
    simpa only [Algebra.algebraMap_eq_smul_one] using hle
  change ‖B‖ ≤ ε
  nlinarith [norm_nonneg B]

section Trace
open Filter
open scoped Topology

local instance spectralCut_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed M.carrier
  rw [← M.centralizer_centralizer']
  exact Set.isClosed_centralizer _

/-- The high left spectral cut of an element of the normal algebra. -/
def leftSpectralCut (M : VonNeumannAlgebra H) (x : M.toStarSubalgebra) (ε : ℝ) :
    M.toStarSubalgebra :=
  ⟨upperSpectralCut ((x : H →L[ℂ] H) * star (x : H →L[ℂ] H)) (ε ^ 2),
    upperSpectralCut_mem M _
      (M.toStarSubalgebra.mul_mem x.property (M.toStarSubalgebra.star_mem' x.property)) _⟩

theorem leftSpectralCut_isStarProjection (M : VonNeumannAlgebra H)
    (x : M.toStarSubalgebra) (ε : ℝ) : IsStarProjection (leftSpectralCut M x ε) := by
  constructor
  · apply Subtype.ext
    exact (upperSpectralCut_isStarProjection _ _).isIdempotentElem.eq
  · apply Subtype.ext
    exact (upperSpectralCut_isStarProjection _ _).isSelfAdjoint.star_eq

theorem norm_complement_leftSpectralCut_mul_le (M : VonNeumannAlgebra H)
    (x : M.toStarSubalgebra) (ε : ℝ) (hε : 0 ≤ ε) :
    ‖(1 - leftSpectralCut M x ε) * x‖ ≤ ε :=
  norm_complement_upperSpectralCut_mul_le (x : H →L[ℂ] H) ε hε

/-- Chebyshev's trace bound for the left spectral cut. -/
theorem leftSpectralCut_trace_bound (M : VonNeumannAlgebra H)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (htr : ∀ a b, τ (a * b) = τ (b * a))
    (x : M.toStarSubalgebra) (ε : ℝ) :
    ε ^ 2 * (τ (leftSpectralCut M x ε)).re ≤ ‖gnsTracialVector τ x‖ ^ 2 := by
  have horder : (ε ^ 2 : ℝ) • leftSpectralCut M x ε ≤ x * star x := by
    change (ε ^ 2 : ℝ) • upperSpectralCut
      ((x : H →L[ℂ] H) * star (x : H →L[ℂ] H)) (ε ^ 2) ≤
      (x : H →L[ℂ] H) * star (x : H →L[ℂ] H)
    exact smul_upperSpectralCut_le ((x : H →L[ℂ] H) * star (x : H →L[ℂ] H))
      (mul_star_self_nonneg _) (ε ^ 2)
  have ht := (τ.monotone horder).1
  change (τ ((ε ^ 2 : ℝ) • leftSpectralCut M x ε)).re ≤
    (τ (x * star x)).re at ht
  have hmap : τ ((ε ^ 2 : ℝ) • leftSpectralCut M x ε) =
      (ε ^ 2 : ℝ) • τ (leftSpectralCut M x ε) :=
    τ.toLinearMap.map_smul_of_tower _ _
  rw [hmap] at ht
  have hreal : ε ^ 2 * (τ (leftSpectralCut M x ε)).re ≤ (τ (x * star x)).re := by
    simpa only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using ht
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), gnsTracialVector_inner, ← htr x (star x)]
  exact hreal

/-- Algebra vectors tending to zero have high spectral cuts of vanishing
trace at every fixed positive threshold. -/
theorem leftSpectralCut_trace_tendsto_zero (M : VonNeumannAlgebra H)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (htr : ∀ a b, τ (a * b) = τ (b * a))
    (x : ℕ → M.toStarSubalgebra)
    (hx : Tendsto (fun n => gnsTracialVector τ (x n)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (τ (leftSpectralCut M (x n) ε)).re) atTop (𝓝 0) := by
  have hsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  apply squeeze_zero (g := fun n => ‖gnsTracialVector τ (x n)‖ ^ 2 / ε ^ 2)
    (fun n => (τ.map_nonneg (leftSpectralCut_isStarProjection M (x n) ε).nonneg).1)
    (fun n => (le_div_iff₀ hsq).mpr (by
      nlinarith [leftSpectralCut_trace_bound M τ htr (x n) ε]))
  simpa only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div]
    using (hx.norm.pow 2).div_const (ε ^ 2)

end Trace
end KadisonSimilarity

end

end OAI
