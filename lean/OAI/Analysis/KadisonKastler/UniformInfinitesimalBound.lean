import OAI.Analysis.KadisonKastler.UniformInfinitesimalCutoff
import OAI.Analysis.KadisonKastler.SelfAdjointApproximation

namespace OAI

/-! # The uniform linear infinitesimal estimate with matrix-corner data

Subtract a self-adjoint approximating sum and normalize by its distance.
The bounded cutoff then contradicts any failure of the linear estimate.
No closedness of the algebra-plus-commutant sum is used.
-/

namespace KadisonKastler

noncomputable section

universe u

local instance uniformInfinitesimalBoundSourceOrder (P : MatrixTypeIIIFactorModel.{u}) :
    PartialOrder (Algebra P.M) := CStarAlgebra.spectralOrder _
local instance uniformInfinitesimalBoundSourceStarOrder (P : MatrixTypeIIIFactorModel.{u}) :
    StarOrderedRing (Algebra P.M) := CStarAlgebra.spectralOrderedRing _

private theorem infinitesimal_bound_of_cutoff (P : MatrixTypeIIIFactorModel.{u})
    {ε : ℝ} (hε : 0 < ε)
    (hcut : ∀ D : P.H →L[ℂ] P.H, IsSelfAdjoint D → ‖D‖ ≤ 2 →
      (∀ x : Algebra P.M, ∃ y : Algebra P.M,
        ‖D * (x : P.H →L[ℂ] P.H) - (x : P.H →L[ℂ] P.H) * D -
          (y : P.H →L[ℂ] P.H)‖ ≤ ε * ‖x‖) →
      ∃ a b : P.H →L[ℂ] P.H, a ∈ P.M ∧ b ∈ P.M.commutant ∧
        ‖D - (a + b)‖ < 1)
    (T : P.H →L[ℂ] P.H) (hT : IsSelfAdjoint T) {δ : ℝ} (hδ : 0 ≤ δ)
    (happrox : ∀ x : Algebra P.M, ∃ y : Algebra P.M,
      ‖T * (x : P.H →L[ℂ] P.H) - (x : P.H →L[ℂ] P.H) * T -
        (y : P.H →L[ℂ] P.H)‖ ≤ δ * ‖x‖) :
    Metric.infDist T (selfAdjointAlgebraCommutantSum P.M) ≤ δ / ε := by
  let S := selfAdjointAlgebraCommutantSum P.M
  let d := Metric.infDist T S
  by_contra hle
  have hd : δ / ε < d := lt_of_not_ge hle
  have hdpos : 0 < d := (div_nonneg hδ hε.le).trans_lt hd
  have hS : S.Nonempty := ⟨0, selfAdjointAlgebraCommutantSum_zero P.M⟩
  obtain ⟨s, hs, hnear⟩ := (Metric.infDist_lt_iff hS).mp
    (show Metric.infDist T S < 2 * d by change d < 2 * d; linarith)
  have hnear' : ‖T - s‖ < 2 * d := by simpa only [dist_eq_norm] using hnear
  let D : P.H →L[ℂ] P.H := d⁻¹ • (T - s)
  have hD : IsSelfAdjoint D := (show IsSelfAdjoint (d⁻¹) from rfl).smul
    (hT.sub (selfAdjoint_of_mem_algebraCommutantSum P.M hs))
  have hDn : ‖D‖ ≤ 2 := by
    dsimp [D]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdpos)]
    have h := mul_le_mul_of_nonneg_left hnear'.le (inv_nonneg.mpr hdpos.le)
    have he : d⁻¹ * (2 * d) = 2 := by field_simp
    exact h.trans_eq he
  have hδd : d⁻¹ * δ ≤ ε := by
    have hlt : δ < d * ε := (div_lt_iff₀ hε).mp hd
    have hdiv : δ / d ≤ ε := (div_le_iff₀ hdpos).mpr (by nlinarith)
    simpa only [div_eq_mul_inv, mul_comm] using hdiv
  have hDapprox (x : Algebra P.M) : ∃ y : Algebra P.M,
      ‖D * (x : P.H →L[ℂ] P.H) - (x : P.H →L[ℂ] P.H) * D -
        (y : P.H →L[ℂ] P.H)‖ ≤ ε * ‖x‖ := by
    obtain ⟨y, hy⟩ := happrox x
    let c : Algebra P.M := ⟨s * x.val - x.val * s,
      commutator_mem_of_mem_algebraCommutantSum P.M hs x.property⟩
    refine ⟨(d⁻¹ : ℝ) • (y - c), ?_⟩
    have he : D * x.val - x.val * D - ((d⁻¹ : ℝ) • (y - c) : Algebra P.M) =
        (d⁻¹ : ℝ) • (T * x.val - x.val * T - y.val) := by
      change D * x.val - x.val * D - (d⁻¹ : ℝ) • (y.val - (s * x.val - x.val * s)) = _
      dsimp [D]
      rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, ← smul_sub]
      congr 1
      noncomm_ring
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdpos)]
    calc
      _ ≤ d⁻¹ * (δ * ‖x‖) := mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hdpos.le)
      _ ≤ ε * ‖x‖ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hδd (norm_nonneg x)
  obtain ⟨a, b, ha, hb, hab⟩ := hcut D hD hDn hDapprox
  obtain ⟨s0, hs0, hDs0⟩ := exists_selfAdjoint_sum_approximation P.M D hD a b ha hb
  have hsmall : ‖D - s0‖ < 1 := hDs0.trans_lt hab
  have hresult : s + d • s0 ∈ S := selfAdjointAlgebraCommutantSum_add P.M hs
    (selfAdjointAlgebraCommutantSum_smul P.M d hs0)
  have hnorm : ‖T - (s + d • s0)‖ < d := by
    have hscale : d • D = T - s := by
      dsimp [D]
      rw [smul_smul, mul_inv_cancel₀ hdpos.ne', one_smul]
    have he : T - (s + d • s0) = d • (D - s0) := by
      rw [smul_sub, hscale]
      abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hdpos]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hsmall hdpos
  have hdist := Metric.infDist_le_dist_of_mem (x := T) hresult
  have hdist' : d ≤ ‖T - (s + d • s0)‖ := by
    simpa only [dist_eq_norm] using hdist
  exact (not_lt_of_ge hdist') hnorm

theorem uniform_typeIII_infinitesimal_bound
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (hDistance : ∀ P : MatrixTypeIIIFactorModel.{u},
      PublishedBlockCommutantApproximation (Algebra P.M) P.H) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : MatrixTypeIIIFactorModel.{u},
      ∀ T : P.H →L[ℂ] P.H, IsSelfAdjoint T → ∀ δ : ℝ, 0 ≤ δ →
        (∀ x : Algebra P.M, ∃ y : Algebra P.M,
          ‖T * (x : P.H →L[ℂ] P.H) - (x : P.H →L[ℂ] P.H) * T -
            (y : P.H →L[ℂ] P.H)‖ ≤ δ * ‖x‖) →
        Metric.infDist T (selfAdjointAlgebraCommutantSum P.M) ≤ C * δ := by
  obtain ⟨ε, hε, hcut⟩ := uniform_typeIII_infinitesimal_cutoff hSpectral hCompare hSakai hDistance
  refine ⟨ε⁻¹, inv_pos.mpr hε, fun P T hT δ hδ happrox => ?_⟩
  simpa only [div_eq_mul_inv, mul_comm] using
    infinitesimal_bound_of_cutoff P hε (hcut P) T hT hδ happrox

end

end KadisonKastler

end OAI
