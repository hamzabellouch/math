import OAI.Probability.ContinuumTransition.BoundarySum

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem physical_log_deletedCore_bound {t β : ℝ} (ht : 0 ≤ t) (hβ : 0 < β)
    {σ τ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hτ : ∀ n, 0 ≤ τ n) (hR : ∀ n, 1 ≤ R n)
    (hs : Summable σ) (hτs : Summable τ)
    (hsmall : 2197*t*kernelHeight*(∑' n, (σ n+τ n)) ≤ (t^2/8)/8) (q : ℕ) (h L : ℝ) :
    Real.log (grandPartition (physicalProfile t (fun n => σ n+τ n) R) t β h L) ≤
      Real.log (grandIntegral (gibbsFamily (deletedCore t σ τ R q) β (t*h)) (cube L)) := by
  have hστ (n : ℕ) : 0 ≤ σ n+τ n := add_nonneg (hσ n) (hτ n)
  have hfin : volume (cube L) ≠ ⊤ := by rw [volume_cube]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hUF := cellLowerBound_gibbs_finite ht hβ.le hστ hR (hs.add hτs) hsmall
    (deletedCore_lower ht hσ hτ hR hs hτs q)
    (measurable_deletedCore t hσ hτ hR hs hτs q) hfin (t*h)
  have hPF := cellLowerBound_gibbs_finite ht hβ.le hστ hR (hs.add hτs) hsmall
    (physical_cellLowerBound ht hστ hR (hs.add hτs))
    (measurable_physical_interaction t hστ hR (hs.add hτs)) hfin (t*h)
  have hm := grandIntegral_gibbs_antitone hβ.le
    (deletedCore_le_physical t hσ hτ hR hs hτs q) (t*h) (measurableSet_cube L) hUF hPF
  have hZ := grandIntegral_gibbs_pos (fun x y => physicalProfile t (fun n => σ n+τ n) R ‖x-y‖)
    β (t*h) (cube L) hPF.summable
  rw [grandIntegral_radial] at hZ hm
  exact Real.log_le_log hZ hm

theorem deletedCore_log_cut_bound {t β : ℝ} (ht : 0 < t) (hβ : 0 < β)
    {σ τ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hτ : ∀ n, 0 ≤ τ n) (hR : ∀ n, 1 ≤ R n)
    (hs : Summable σ) (hτs : Summable τ)
    (hsmall : 2197*t*kernelHeight*(∑' n, (σ n+τ n)) ≤ (t^2/8)/8)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (hbound : ∀ n, σ n ≠ 0 → R n ≤ R₀)
    (m q : ℕ) (hq : 0 < q) (h : ℝ) :
    Real.log (grandIntegral (gibbsFamily (deletedCore t σ τ R q) β (t*h))
      (cube ((m : ℝ)*(q : ℝ)/2)))-
    Real.log (grandIntegral (gibbsFamily (cutReference t σ τ R q) β (t*h))
      (cube ((m : ℝ)*(q : ℝ)/2))) ≤
      β*(momentConstant t β (t*h)/2)*(boundaryIndices m q (cellRadius R₀).toNat).card*
        (2197*t*kernelHeight*(∑' n, σ n)) := by
  let L := (m : ℝ)*(q : ℝ)/2
  let T := boundaryIndices m q (cellRadius R₀).toNat
  let J (k l : cubeCells L) : ℝ := if (k : Lattice) ∈ T then physicalCoupling t σ R k l else 0
  have hστ (n : ℕ) : 0 ≤ σ n+τ n := add_nonneg (hσ n) (hτ n)
  have hU := deletedCore_lower ht.le hσ hτ hR hs hτs q
  have hUV := deletedCore_le_cutReference (τ := τ) ht.le hσ hR q
  have hJ (k l : cubeCells L) : 0 ≤ J k l := by
    dsimp only [J]
    split_ifs
    · exact physicalCoupling_nonneg ht.le hσ hR k l
    · rfl
  have hboundJ : ∀ (k l : cubeCells L) (x y : Space), x ∈ cube L → y ∈ cube L →
      cellIndex x = k → cellIndex y = l →
      cutReference t σ τ R q x y-deletedCore t σ τ R q x y ≤ J k l := by
    intro k l x y hx _ hk hl
    have hh := cutReference_boundary_bound (τ := τ) (y := y) ht.le hσ hR hs hR₀ hbound hq hx
    simpa only [hk, hl, J, T] using hh
  have hb := modified_log_grand_comparison ht hβ hστ hR (hs.add hτs) hsmall (hU.mono hUV) hU
    (measurable_cutReference t hσ hτ hR hs hτs q) (measurable_deletedCore t hσ hτ hR hs hτs q)
    (cutReference_symm t σ τ R q) (deletedCore_symm t σ τ R q) hUV (t*h) L J hJ hboundJ
  have hnon : 0 ≤ 2197*t*kernelHeight*(∑' n, σ n) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ht.le) kernelHeight_pos.le) (tsum_nonneg hσ)
  have hrow := sum_supported_rows_le (cubeCells L) T
    (2197*t*kernelHeight*(∑' n, σ n)) hnon (physicalCoupling t σ R)
    (fun k => physicalCoupling_row ht.le hσ hR hs (fun l : cubeCells L => (l : Lattice)) Subtype.val_injective k)
  have hc : 0 ≤ β*(momentConstant t β (t*h)/2) :=
    mul_nonneg hβ.le (div_nonneg (momentConstant_pos ht hβ (t*h)).le (by norm_num))
  have hh := hb.trans (mul_le_mul_of_nonneg_left hrow hc)
  change _ ≤ β*(momentConstant t β (t*h)/2)*((T.card : ℝ)*(2197*t*kernelHeight*(∑' n, σ n))) at hh
  simpa only [mul_assoc] using hh

theorem physical_log_cut_bound {t β : ℝ} (ht : 0 < t) (hβ : 0 < β)
    {σ τ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hτ : ∀ n, 0 ≤ τ n) (hR : ∀ n, 1 ≤ R n)
    (hs : Summable σ) (hτs : Summable τ)
    (hsmall : 2197*t*kernelHeight*(∑' n, (σ n+τ n)) ≤ (t^2/8)/8)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (hbound : ∀ n, σ n ≠ 0 → R n ≤ R₀)
    (m q : ℕ) (hq : 0 < q) (h : ℝ) :
    Real.log (grandPartition (physicalProfile t (fun n => σ n+τ n) R) t β h ((m : ℝ)*(q : ℝ)/2)) ≤
      Real.log (grandIntegral (gibbsFamily (cutReference t σ τ R q) β (t*h)) (cube ((m : ℝ)*(q : ℝ)/2)))+
      β*(momentConstant t β (t*h)/2)*(boundaryIndices m q (cellRadius R₀).toNat).card*
        (2197*t*kernelHeight*(∑' n, σ n)) := by
  exact (physical_log_deletedCore_bound ht.le hβ hσ hτ hR hs hτs hsmall q h _).trans
    (sub_le_iff_le_add'.mp (deletedCore_log_cut_bound ht hβ hσ hτ hR hs hτs hsmall hR₀ hbound m q hq h))

end ContinuumTemperature
end

end OAI
