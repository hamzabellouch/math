import Mathlib
import OAI.Analysis.LaughlinGap.FourBound
import OAI.Analysis.LaughlinGap.GlobalBoundCore
import OAI.Analysis.LaughlinGap.ThreeComparison

namespace OAI

/-! Global Bound. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators InnerProduct MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology
variable {ι : Type*} [Fintype ι]

theorem physical_square_eventually_of_certificates
    (rows : ι → RowData) (ε γ : ℝ) (hε : 0 ≤ ε)
    (hmargin : γ < 1-rowEta rows-(61/4096:ℝ)-1222*ε)
    (hthree : ∀ z : Fin 16, z.val ≠ 0 → z.val ≠ 1 → z.val ≠ 3 →
      (∑ r, rowTrace threeWeightCoefficientStar z.val (rows r)) <
        (3/2:ℝ) * ((3*(z.val:ℝ)-1)*(-1/2:ℝ)^z.val))
    (hfour : ∀ d : Fin 23, FourCertificate rows ε (d.val+1) (by omega)) :
    ∀ᶠ Q in atTop, γ • physicalHamiltonian Q ≤ physicalHamiltonian Q * physicalHamiltonian Q := by
  obtain ⟨R,hpos,hlimR,hR⟩ := four_comparison_of_certificates rows ε hε hfour
  have hlim : Tendsto (fun Q => 1-rowEta rows-threeBodyTail Q-(1222*ε+R Q)) atTop
      (𝓝 (1-rowEta rows-(61/4096:ℝ)-1222*ε)) := by
    simpa only [add_zero] using (threeBodyTail_tendsto.const_sub (1-rowEta rows)).sub
      (hlimR.const_add (1222*ε))
  filter_upwards [eventually_ge_atTop 24,three_comparison_of_strict_traces rows hthree,hR,
    hlim.eventually (Ioi_mem_nhds hmargin)] with Q hQ h₃ h₄ hγ
  apply le_trans _ (physical_square_of_comparisons hQ rows (1222*ε+R Q) (h₃ (by omega)) (h₄ hQ))
  exact smul_le_smul_of_nonneg_right (le_of_lt hγ) (physicalHamiltonian_positive Q).nonneg

lemma occupation_square_of_real_square {Q : ℕ} (γ : ℝ)
    (h : γ • physicalHamiltonian Q ≤ physicalHamiltonian Q * physicalHamiltonian Q) :
    ∀ x : Occupation.Hilbert (Q+1), γ * Occupation.localPairEnergy (Q+1) (2*Q-1) Q x ≤
      ‖Occupation.physicalOccupationHamiltonian Q x‖^2 := by
  have hp := complexify_positive (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h))
  intro x
  have hx := hp.re_inner_nonneg_right x
  simp only [map_sub,map_mul,map_smul,complexify_physicalHamiltonian,
    LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,inner_sub_right,
    inner_smul_right_eq_smul] at hx
  rw [← (Occupation.physicalOccupationHamiltonian_positive Q).isSymmetric x
    (Occupation.physicalOccupationHamiltonian Q x),inner_self_eq_norm_sq_to_K] at hx
  change 0 ≤ ((‖Occupation.physicalOccupationHamiltonian Q x‖:ℂ)^2).re -
    (γ • inner ℂ x (Occupation.physicalOccupationHamiltonian Q x)).re at hx
  rw [← Complex.ofReal_pow,Complex.ofReal_re,Complex.real_smul,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Occupation.physicalOccupationHamiltonian_inner] at hx
  exact sub_nonneg.mp hx

theorem mainTarget_of_finite_certificates
    (rows : ι → RowData) (ε : ℝ) (hε : 0 ≤ ε)
    (hmargin : (1/25:ℝ) < 1-rowEta rows-(61/4096:ℝ)-1222*ε)
    (hthree : ∀ z : Fin 16, z.val ≠ 0 → z.val ≠ 1 → z.val ≠ 3 →
      (∑ r, rowTrace threeWeightCoefficientStar z.val (rows r)) <
        (3/2:ℝ) * ((3*(z.val:ℝ)-1)*(-1/2:ℝ)^z.val))
    (hfour : ∀ d : Fin 23, FourCertificate rows ε (d.val+1) (by omega)) : MainTarget := by
  apply Occupation.mainTarget_of_uniform_occupation_square_estimate
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.mp
    (physical_square_eventually_of_certificates rows ε (1/25) hε hmargin hthree hfour)
  exact ⟨Q₀,fun Q hQ => occupation_square_of_real_square _ (hQ₀ Q hQ)⟩

end LaughlinGap.RealOccupation

end

end OAI
