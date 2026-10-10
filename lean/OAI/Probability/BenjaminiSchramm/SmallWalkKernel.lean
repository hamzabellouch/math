import OAI.Probability.BenjaminiSchramm.KernelExteriorBound

namespace OAI

open Filter
open scoped ENNReal Topology

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_small_walk_kernel (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G) (ε : ℝ) (hε : 0 < ε) :
    ∃ (d M : ℕ) (K : Hilbert V →L[ℂ] Hilbert V),
      (∀ a, degree G a ≤ d) ∧ PositiveRealMatrix K ∧ ‖K‖ < ε ∧
      (∀ a, ∑' b, ennMatrixCoeff K a b = 1) ∧
      (∀ a b, b ∉ reachBall G a M → ennMatrixCoeff K a b = 0) := by
  obtain ⟨d,P,hd,hdeg,hPn,_,hP⟩ := exists_strict_walk_operator G hloc hqt hh
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : 0 ≤ (1 : ℝ)/(2*d) := by positivity
  have had : (1 : ℝ)/(2*d)*d ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 2*(d : ℝ))).mpr
    nlinarith
  have hpos : PositiveRealMatrix P := by
    intro a b
    change (P (lp.single 2 b (1 : ℂ)) a).im = 0 ∧
      0 ≤ (P (lp.single 2 b (1 : ℂ)) a).re
    rw [hP]
    exact ⟨Complex.ofReal_im _,walkKernel_nonneg G hloc d hdeg _ ha had a b⟩
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg P) hPn
  obtain ⟨M,hM,hMp⟩ := Filter.Eventually.exists
    ((ht.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop 1))
  refine ⟨d,M,P^M,hdeg,hpos.pow M,
    (norm_pow_le' P (Nat.zero_lt_of_lt hMp)).trans_lt hM,?_,?_⟩
  · intro a
    change (∑' b, ENNReal.ofReal (matrixCoeff (P^M) a b).re) = 1
    rw [←ENNReal.ofReal_tsum_of_nonneg (fun b => ((hpos.pow M) a b).2)
      (walkPower_hasSum G hloc _ P hpos hP M a).summable,
      (walkPower_hasSum G hloc _ P hpos hP M a).tsum_eq,ENNReal.ofReal_one]
  · intro a b hb
    change ENNReal.ofReal (matrixCoeff (P^M) a b).re = 0
    rw [walkPower_support G hloc _ P hpos hP M a b hb,ENNReal.ofReal_zero]

end Percolation.BenjaminiSchramm

end OAI
